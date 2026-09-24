#!/usr/bin/env python3
"""Write SHA-256 fingerprints for the Lean sources and build configuration."""
from __future__ import annotations
import hashlib
from pathlib import Path
from project_audit import ROOT, sources


def main() -> None:
    files = set(sources().values())
    files.update(ROOT / name for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"))
    files.update((ROOT / "scripts").glob("*.py"))
    rows = [hashlib.sha256(p.read_bytes()).hexdigest() + "  " + str(p.relative_to(ROOT))
            for p in sorted(files)]
    destination = ROOT / "SourceManifest.sha256"
    destination.write_text("\n".join(rows) + "\n")
    print(f"Recorded {len(files)} source and build files in {destination.name}")


if __name__ == "__main__": main()
