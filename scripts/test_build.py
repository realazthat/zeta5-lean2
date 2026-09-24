"""Regression checks for CI dependency planning."""
import unittest
from build import package_build_targets


class PackageTargetsTest(unittest.TestCase):
    def test_toolchain_imports_are_not_lake_package_targets(self):
        imports = ["Lean", "Lean.Elab.Tactic", "Init", "Std.Data.HashMap",
                   "Lake", "Mathlib.Data.Rat.Defs", "LeanCert.Tactic.IntervalAuto.PointIneq",
                   "PrimeNumberTheoremAnd.Consequences", "Mathlib.Data.Rat.Defs"]
        self.assertEqual(package_build_targets(imports), [
            "+LeanCert.Tactic.IntervalAuto.PointIneq:olean",
            "+Mathlib.Data.Rat.Defs:olean",
            "+PrimeNumberTheoremAnd.Consequences:olean",
        ])

    def test_only_toolchain_imports_need_no_package_build(self):
        self.assertEqual(package_build_targets(["Lean", "Std", "Init.Prelude"]), [])


if __name__ == "__main__":
    unittest.main()
