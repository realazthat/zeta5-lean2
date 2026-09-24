#!/usr/bin/env python3
"""Replay every local module's stored declarations through Lean's kernel.

Run after a build. The default uses ordinary Lake artifacts. Development
artifact directories can be supplied explicitly; their order is recorded.
This does not build missing modules or manufacture Lake build traces.
"""
from __future__ import annotations
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

from project_audit import ROOT, sources, graph, closure


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("targets", nargs="*", default=["Main", "AxiomAudit"])
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--lake-project", type=Path, default=ROOT)
    ap.add_argument("--artifact-dir", action="append", type=Path, default=[])
    ap.add_argument("--refresh-stale", action="store_true",
                    help="re-elaborate sources newer than their selected artifacts before replay")
    ap.add_argument("--output", type=Path, default=ROOT / "KernelReplay-audit.json")
    args = ap.parse_args()
    if args.jobs < 1: ap.error("--jobs must be positive")
    src = sources(); deps = graph(src); selected = set(); missing = set()
    for target in args.targets:
        c, m = closure(target, deps); selected |= c; missing |= m
    if missing: raise RuntimeError("Missing modules: " + ", ".join(sorted(missing)))
    env = os.environ.copy(); env.pop("LEAN_PATH", None); env.pop("LEAN_SRC_PATH", None)
    if args.artifact_dir:
        env["LEAN_PATH"] = os.pathsep.join(str(p.resolve()) for p in args.artifact_dir)
    env["LEAN_NUM_THREADS"] = "1"
    env["LEAN_PATH"] = subprocess.check_output(
        ["lake", "env", "printenv", "LEAN_PATH"], cwd=args.lake_project,
        env=env, text=True).strip()
    path = [Path(p).resolve() for p in env["LEAN_PATH"].split(os.pathsep)]
    lean = subprocess.check_output(["lake", "env", "which", "lean"],
        cwd=args.lake_project, env=env, text=True).strip()
    checker = str(Path(lean).with_name("leanchecker"))
    version = subprocess.check_output([lean, "--version"], env=env, text=True).strip()
    logs = ROOT / ".lake" / "build" / "kernel-replay-logs"
    logs.mkdir(parents=True, exist_ok=True)
    artifacts = {}
    for m in selected:
        rel = Path(*m.split(".")).with_suffix(".olean")
        found = next((p / rel for p in path if (p / rel).is_file()), None)
        if found is None: raise RuntimeError("No compiled artifact for " + m)
        artifacts[m] = found
    order = []; seen = set()
    def visit(m):
        if m in seen: return
        for d in deps[m]:
            if d in selected: visit(d)
        seen.add(m); order.append(m)
    for m in sorted(selected): visit(m)
    refreshed = []
    for m in order:
        if src[m].stat().st_mtime_ns <= artifacts[m].stat().st_mtime_ns: continue
        if not args.refresh_stale: raise RuntimeError("Source newer than chosen artifact: " + m)
        print("Refreshing " + m, flush=True)
        start = time.monotonic()
        with (logs / (m + ".refresh.log")).open("w") as stream:
            proc = subprocess.run([lean, "-o", str(artifacts[m]), str(src[m])],
                cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT)
        refreshed.append({"module": m, "returncode": proc.returncode,
                          "seconds": round(time.monotonic() - start, 2)})
        if proc.returncode:
            print((logs / (m + ".refresh.log")).read_text()[-12000:], flush=True)
            return proc.returncode
    report = {"toolchain": version, "targets": args.targets, "module_count": len(selected),
              "search_path": list(map(str, path)), "jobs": args.jobs,
              "checker": checker, "refreshes": refreshed, "modules": {}, "complete": False}
    snapshots = {}
    for m in sorted(selected):
        snapshots[m] = {"source": str(src[m].relative_to(ROOT)),
            "source_sha256": digest(src[m]), "artifact": str(artifacts[m]),
            "artifact_sha256": digest(artifacts[m]), "parts": {}}
        for suffix in (".private", ".server"):
            p = Path(str(artifacts[m]) + suffix)
            if p.exists(): snapshots[m]["parts"][suffix] = digest(p)
    def replay(m):
        start = time.monotonic(); log = logs / (m + ".log")
        with log.open("w") as stream:
            proc = subprocess.run([checker, m], cwd=ROOT, env=env,
                stdout=stream, stderr=subprocess.STDOUT)
        return {**snapshots[m], "returncode": proc.returncode,
                "seconds": round(time.monotonic() - start, 2),
                "log": str(log.relative_to(ROOT))}
    print(f"Kernel replay: {len(selected)} modules, {args.jobs} workers", flush=True)
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        future_modules = {pool.submit(replay, m): m for m in sorted(selected)}
        for future in as_completed(future_modules):
            m = future_modules[future]; result = future.result(); report["modules"][m] = result
            print(f"[{len(report['modules'])}/{len(selected)}] {m}: " +
                  ("OK" if result["returncode"] == 0 else "FAILED") +
                  f" ({result['seconds']} s)", flush=True)
            args.output.write_text(json.dumps(report, indent=2) + "\n")
    report["changed_during_replay"] = [m for m in sorted(selected)
        if digest(src[m]) != snapshots[m]["source_sha256"] or
        digest(artifacts[m]) != snapshots[m]["artifact_sha256"] or any(
            digest(Path(str(artifacts[m]) + suffix)) != h
            for suffix, h in snapshots[m]["parts"].items())]
    report["complete"] = not report["changed_during_replay"] and all(
        r["returncode"] == 0 for r in report["modules"].values())
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print("Kernel replay " + ("PASSED" if report["complete"] else "FAILED"), flush=True)
    return 0 if report["complete"] else 1


if __name__ == "__main__": raise SystemExit(main())
