#!/usr/bin/env python3
"""Build a Lean module and its local imports with bounded parallel Lake jobs.

Uses only Lake's standard .lake/build artifacts. It does not use build432,
source-adjacent oleans, or a caller-supplied LEAN_PATH.
"""
from __future__ import annotations
import argparse
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

from project_audit import ROOT, sources, graph, closure, inspect, sync_lake


def execute(argv, env):
    print("+ " + " ".join(argv), flush=True)
    subprocess.run(argv,cwd=ROOT,env=env,check=True)


def main() -> int:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("targets",nargs="*",default=["Main"])
    ap.add_argument("--jobs",type=int,default=2,help="maximum simultaneous local-module builds (default: 2)")
    ap.add_argument("--no-cache",action="store_true",help="skip the optional mathlib cache download")
    ap.add_argument("--sync-lake",action="store_true",help="register newly added source modules before building")
    ap.add_argument("--dry-run",action="store_true",help="print the build plan without invoking Lake")
    args=ap.parse_args()
    if args.jobs<1: ap.error("--jobs must be positive")
    src=sources()
    if args.sync_lake: sync_lake(src)
    report=inspect(); deps=graph(src)
    if report["problems"]:
        for p in report["problems"]: print(p,file=sys.stderr)
        print("Run python3 scripts/project_audit.py --sync-lake after adding modules.",file=sys.stderr)
        return 1
    selected=set(); missing=set()
    for target in args.targets:
        c,m=closure(target,deps);selected|=c;missing|=m
    if missing:
        print("Missing source modules: "+", ".join(sorted(missing)),file=sys.stderr);return 1
    external=sorted({d for m in selected for d in deps[m] if d not in src})
    local_deps={m:set(deps[m])&selected for m in selected}
    print(f"Targets: {', '.join(args.targets)}; {len(selected)} local modules; {args.jobs} workers.",flush=True)
    if args.dry_run:
        print(json.dumps({"targets":args.targets,"local_modules":sorted(selected),"external_imports":external},indent=2))
        return 0
    if shutil.which("lake") is None:
        print("Install elan/Lean first: lake is not on PATH.",file=sys.stderr);return 1
    env=os.environ.copy();env.pop("LEAN_PATH",None);env.pop("LEAN_SRC_PATH",None)
    env.setdefault("MATHLIB_CACHE_GET_URL","https://lakecache.blob.core.windows.net/mathlib4")
    env["TAR_OPTIONS"]=(env.get("TAR_OPTIONS","")+" --no-same-owner").strip()
    # Bound the Lean/Lake runtime's worker pool as well as the module scheduler.
    env.setdefault("LEAN_NUM_THREADS",str(args.jobs))
    execute(["lake","env","lean","--version"],env)
    if not args.no_cache: execute(["lake","exe","cache","get"],env)
    # Complete shared external dependencies once, before parallel local jobs.
    if external: execute(["lake","build",*["+"+m+":olean" for m in external]],env)
    logs=ROOT/".lake"/"build"/"verification-logs";logs.mkdir(parents=True,exist_ok=True)
    results={};finished=set();pending=set(selected);running={};failed=False
    def build(m):
        log=logs/(m+".log");start=time.monotonic()
        with log.open("w") as stream:
            p=subprocess.run(["lake","build","+"+m+":olean"],cwd=ROOT,env=env,stdout=stream,stderr=subprocess.STDOUT)
        return {"module":m,"returncode":p.returncode,"seconds":round(time.monotonic()-start,2),
                "log":str(log.relative_to(ROOT))}
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while pending or running:
            if not failed:
                ready=sorted(m for m in pending if local_deps[m]<=finished)
                # Numerical batches are independent and dominate the build time.
                ready.sort(key=lambda m:(not m.startswith(("AppendixPotential.","AppendixField.")),m))
                for m in ready[:args.jobs-len(running)]:
                    pending.remove(m);running[pool.submit(build,m)]=m
            if not running:
                if pending and not failed: raise RuntimeError("No ready module: import graph has a cycle")
                break
            done,_=wait(running,return_when=FIRST_COMPLETED)
            for future in done:
                m=running.pop(future);r=future.result();results[m]=r
                print(f"[{len(results)}/{len(selected)}] {m}: {'OK' if r['returncode']==0 else 'FAILED'} ({r['seconds']} s)",flush=True)
                if r["returncode"]:
                    failed=True
                    print((ROOT/r["log"]).read_text()[-12000:],file=sys.stderr,flush=True)
                else: finished.add(m)
            (logs/"results.json").write_text(json.dumps({"targets":args.targets,"modules":results},indent=2)+"\n")
    if failed:return 1
    print("Build complete. Logs: .lake/build/verification-logs/",flush=True)
    return 0

if __name__=="__main__":
    try: raise SystemExit(main())
    except subprocess.CalledProcessError as e: raise SystemExit(e.returncode)
