#!/usr/bin/env python3
"""Run the pinned toolchain Comparator with both independent kernel checkers."""
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    for command in ("lake", "lean", "bwrap"):
        if shutil.which(command) is None:
            raise SystemExit(f"Required executable missing: {command}")
    prefix = Path(subprocess.check_output(
        ["lean", "--print-prefix"], cwd=ROOT, text=True).strip())
    configuration = json.loads((ROOT / "comparator.json").read_text())
    if "external_kernels" in configuration:
        raise SystemExit("external_kernels must not appear in the submitted config")
    configuration.pop("enable_nanoda", None)
    kernels = {"nanoda": prefix / "bin/nanoda_bin", "con-ron": prefix / "bin/con-ron"}
    for executable in kernels.values():
        if not executable.is_file():
            raise SystemExit(f"Pinned toolchain is missing {executable}")
    configuration["external_kernels"] = {
        name: [str(executable)] for name, executable in kernels.items()
    }
    with tempfile.TemporaryDirectory(prefix="zeta5-comparator-") as temporary:
        config = Path(temporary) / "protected.json"
        config.write_text(json.dumps(configuration, indent=2) + "\n")
        subprocess.run(["lake", "comparator", "--config", str(config)],
                       cwd=ROOT, check=True)


if __name__ == "__main__":
    main()
