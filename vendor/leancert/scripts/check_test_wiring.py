#!/usr/bin/env python3
"""Fail when a LeanCert/Test module is not an explicit Lake library root."""

from pathlib import Path
import sys
import tomllib


ROOT = Path(__file__).resolve().parents[1]


def module_name(path: Path) -> str:
    return ".".join(path.relative_to(ROOT).with_suffix("").parts)


def main() -> int:
    with (ROOT / "lakefile.toml").open("rb") as lakefile:
        config = tomllib.load(lakefile)

    wired_roots = {
        root
        for library in config.get("lean_lib", [])
        for root in library.get("roots", [])
    }
    test_modules = {
        module_name(path)
        for path in (ROOT / "LeanCert" / "Test").rglob("*.lean")
    }
    unwired = sorted(test_modules - wired_roots)

    if unwired:
        print("The following test modules are not explicit roots of any Lake target:", file=sys.stderr)
        for module in unwired:
            print(f"  - {module}", file=sys.stderr)
        print("Add each module to FunctionalTests or another intentional test target.", file=sys.stderr)
        return 1

    print(f"All {len(test_modules)} LeanCert/Test modules are wired into Lake targets.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
