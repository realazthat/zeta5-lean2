#!/usr/bin/env python3
"""Inspect local Lean imports, dependency pins, and compiled-artifact locations."""
from __future__ import annotations
import argparse
import collections
import json
from pathlib import Path
import re
import sys
import tomllib

ROOT = Path(__file__).resolve().parents[1]
LEAN_VERSION = "4.32.2"
TOOLCHAIN = "leanprover/lean4:v4.32.2"
PINNED = {
    "PrimeNumberTheoremAnd": "a5154676af9aa3095150ee410cdda80555aa0642",
    "mathlib": "905b95818eb32af7874a58b427f50c1711a5e96c",
    "leancert": "6b11513512c9d27183fb4725bfc291ab38b4a6d7",
}
EXTERNAL_ROOTS = {"Init", "Lean", "Lake", "Std", "Mathlib", "Batteries", "Aesop",
                  "Qq", "LeanCert", "PrimeNumberTheoremAnd", "PrimeCert",
                  "LeanArchitect", "Checkdecls", "ProofWidgets", "Plausible"}
SKIP_DIRS = {".lake", "build432", ".git", "__pycache__"}
DIAGNOSTICS = {"CheckOuter", "CheckSmall", "ProbeRoot"}


def uncomment(s: str) -> str:
    """Remove nested Lean comments, preserving line breaks and string contents."""
    out = []; i = 0; depth = 0; quoted = False
    while i < len(s):
        if depth:
            if s.startswith("/-", i): depth += 1; out.extend("  "); i += 2
            elif s.startswith("-/", i): depth -= 1; out.extend("  "); i += 2
            else: out.append("\n" if s[i] == "\n" else " "); i += 1
        elif quoted:
            out.append(s[i])
            if s[i] == "\\" and i + 1 < len(s): out.append(s[i+1]); i += 2
            else:
                if s[i] == '"': quoted = False
                i += 1
        elif s.startswith("/-", i): depth = 1; out.extend("  "); i += 2
        elif s.startswith("--", i):
            end = s.find("\n", i)
            if end < 0: end = len(s)
            out.extend(" " * (end-i)); i = end
        else:
            if s[i] == '"': quoted = True
            out.append(s[i]); i += 1
    return "".join(out)


def sources() -> dict[str, Path]:
    return {".".join(p.relative_to(ROOT).with_suffix("").parts): p
            for p in ROOT.rglob("*.lean") if not (set(p.relative_to(ROOT).parts) & SKIP_DIRS)
            and p.stem not in DIAGNOSTICS and not p.stem.startswith("Probe")}


def imports(path: Path) -> list[str]:
    # Lean imports precede declarations. Stop at the first declaration rather
    # than lexing megabytes of generated numerical proof terms.
    header = ""; result = []
    with path.open() as stream:
        for line in stream:
            header += line
            clean = uncomment(header).splitlines()
            current = clean[-1].strip() if clean else ""
            if not current or current in {"module", "prelude"}: continue
            match = re.fullmatch(r"(?:(?:public|meta)\s+)*import\s+(.+)", current)
            if match:
                result.extend(x for x in match.group(1).split() if x != "all")
            else: break
    return result


def graph(src: dict[str, Path]) -> dict[str, list[str]]:
    return {m: imports(p) for m,p in src.items()}


def closure(target: str, deps: dict[str, list[str]]) -> tuple[set[str], set[str]]:
    seen = set(); missing = set(); active = set()
    def visit(m):
        if m in active: raise ValueError(f"local import cycle at {m}")
        if m in seen: return
        if m not in deps:
            if m.split('.')[0] not in EXTERNAL_ROOTS: missing.add(m)
            return
        active.add(m)
        for d in deps[m]: visit(d)
        active.remove(m); seen.add(m)
    visit(target)
    return seen, missing


def artifact(path: Path, source: Path) -> dict | None:
    if not path.exists(): return None
    with path.open("rb") as f: header = f.read(40)
    version = header[7:].split(b"\0",1)[0].decode("ascii", errors="replace") if header.startswith(b"olean") else "unknown"
    return {"path":str(path.relative_to(ROOT)), "lean_version":version,
            "source_newer":source.stat().st_mtime_ns > path.stat().st_mtime_ns}


def desired_globs(src: dict[str, Path]) -> list[str]:
    # Explicit module names avoid claiming external namespaces such as Mathlib.
    return sorted(set(src) | {"Main"})


def sync_lake(src: dict[str, Path]) -> None:
    p = ROOT / "lakefile.toml"
    text = p.read_text()
    block = "# BEGIN GENERATED LOCAL MODULES\nglobs = [\n" + "".join(
        f'  "{m}",\n' for m in desired_globs(src)) + "]\n# END GENERATED LOCAL MODULES"
    pat = r"# BEGIN GENERATED LOCAL MODULES\n.*?# END GENERATED LOCAL MODULES"
    if re.search(pat, text, flags=re.S): text = re.sub(pat, lambda _: block, text, flags=re.S)
    else: text = text.rstrip() + "\n" + block + "\n"
    p.write_text(text)


def inspect() -> dict:
    src = sources(); deps = graph(src)
    config = tomllib.loads((ROOT/"lakefile.toml").read_text())
    manifest = json.loads((ROOT/"lake-manifest.json").read_text())
    pins = {p["name"]:p["rev"] for p in manifest["packages"]}
    problems = []
    for package in manifest["packages"]:
        if package.get("type") != "git" or not re.fullmatch(r"[0-9a-f]{40}", package.get("rev", "")):
            problems.append("dependency is not pinned to a Git commit: " + package["name"])
    if config.get("defaultTargets") != ["Main"]:
        problems.append("default target must be Main")
    if config["lean_lib"][0].get("roots") != ["Main"]:
        problems.append("library root must be Main")
    if (ROOT/"lean-toolchain").read_text().strip() != TOOLCHAIN: problems.append("incorrect lean-toolchain")
    for name, rev in PINNED.items():
        if pins.get(name) != rev: problems.append(f"incorrect dependency pin: {name}")
    registered = set(config["lean_lib"][0].get("globs",[]))
    missing_globs = sorted(set(src)-registered)
    if missing_globs: problems.append("unregistered local modules: " + ", ".join(missing_globs))
    modules = []
    for m,p in sorted(src.items()):
        rel = Path(*m.split('.')).with_suffix('.olean')
        outputs = [a for prefix in [".lake/build/lib/lean", "build432", ""]
                   if (a := artifact(ROOT/prefix/rel, p)) is not None]
        modules.append({"module":m, "source":str(p.relative_to(ROOT)), "imports":deps[m],
                        "diagnostic_only":m in DIAGNOSTICS, "artifacts":outputs})
    missing_imports = sorted({d for ds in deps.values() for d in ds
                             if d not in src and d.split('.')[0] not in EXTERNAL_ROOTS})
    main_closure, main_missing = closure("Main", deps)
    counts = collections.Counter(a["lean_version"] for m in modules for a in m["artifacts"])
    return {"toolchain":TOOLCHAIN, "dependency_pins":pins, "problems":problems,
            "summary":{"source_modules":len(src), "source_bytes":sum(p.stat().st_size for p in src.values()),
                       "main_closure_modules":len(main_closure), "main_missing_imports":sorted(main_missing),
                       "missing_imports":missing_imports, "artifact_versions":dict(counts),
                       "missing_current_olean":[m["module"] for m in modules if not any(
                           a["lean_version"]==LEAN_VERSION for a in m["artifacts"])],
                       "diagnostic_modules":sorted(DIAGNOSTICS & set(src))},
            "modules":modules}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--sync-lake", action="store_true", help="refresh the generated local-module registration")
    ap.add_argument("--output", type=Path, help="write a JSON inventory")
    ap.add_argument("--target", default="Main", help="check the import closure of this module")
    ap.add_argument("--check", action="store_true", help="fail on bad pins, unregistered modules, or missing target imports")
    args = ap.parse_args()
    if args.sync_lake: sync_lake(sources())
    report = inspect()
    if args.output: args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(report["summary"],indent=2))
    _, missing = closure(args.target, graph(sources()))
    failures = report["problems"] + (["missing target imports: "+", ".join(sorted(missing))] if missing else [])
    for failure in failures: print(failure,file=sys.stderr)
    return int(args.check and bool(failures))

if __name__ == "__main__": raise SystemExit(main())
