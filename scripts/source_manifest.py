#!/usr/bin/env python3
"""Write SHA-256 fingerprints for the Lean sources and build configuration."""
from __future__ import annotations
import hashlib
import subprocess
from pathlib import Path
from project_audit import ROOT, SKIP_DIRS, DIAGNOSTICS


def main() -> None:
    # Only fingerprint files distributed by Git, not ignored upstream helpers
    # that happen to exist in the checkout. Stage new files before regenerating.
    tracked = {ROOT / name for name in subprocess.check_output(
        ["git", "ls-files", "-z"], cwd=ROOT).decode().split("\0") if name}
    configuration = {"lean-toolchain", "lakefile.toml", "lake-manifest.json",
                     "comparator.json", "formalization.yaml", "LICENSE"}
    files = set()
    for p in tracked:
        rel = p.relative_to(ROOT)
        first_party_lean = (p.suffix == ".lean" and not (set(rel.parts) & SKIP_DIRS)
                            and p.stem not in DIAGNOSTICS and not p.stem.startswith("Probe"))
        if (first_party_lean or rel.as_posix() in configuration
                or rel.parts[0] in {"vendor", "scripts"}
                or rel.as_posix().startswith(".github/workflows/")):
            files.add(p)
    rows = [hashlib.sha256(p.read_bytes()).hexdigest() + "  " + p.relative_to(ROOT).as_posix()
            for p in sorted(files)]
    destination = ROOT / "PalomarSourceManifest.sha256"
    destination.write_text("\n".join(rows) + "\n")
    print(f"Recorded {len(files)} source and build files in {destination.name}")


if __name__ == "__main__": main()
