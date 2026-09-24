# Appendix A numerical certificate

The entry point is `AppendixNumericalCertificate.lean`. It proves every one of the paper's 684 cell bounds, verifies that the exact rational cells cover [0,2], and exposes `interval_cell_certificate`. The theorem `all_cell_bounds` proves the stronger bound −6645002/1000000 for each cell; the interval interface uses −1329/200.

`AppendixPartition.lean` contains the exact rational partition. The files under `AppendixPotential/`, `AppendixField/`, and `AppendixCells/` contain the 685 potential endpoint bounds, 684 field endpoint bounds, and 684 cell inequalities. `AppendixNumericSpecial.lean` proves both derivative signs bracketing the field minimum, the sign needed for the vstar estimate, and a certified lower bound for vstar.

The logarithm checker in `LogCertificates.lean` uses repeated rational upper square-root bounds and log(x) ≤ x−1. Lower logarithm bounds follow by reciprocation. The trigonometric checker in `TrigCertificates.lean` starts with proved Taylor inequalities at a small rational angle and propagates rational sine/cosine boxes through the exact double-angle identities. These boxes certify the required arctangent inequalities. All finite certificate predicates are evaluated by Lean's kernel using `decide +kernel`.

`AppendixNumerics.lean` verifies the paper's two tight energy constants with LeanCert in kernel mode, then proves `final_coefficient`. The actual measure, potential, field, and determinant bridges live in separate analytic modules; this certificate does not assume those bridges.

The master module compiled successfully on Lean 4.32.2 and mathlib commit 905b95818eb32af7874a58b427f50c1711a5e96c. All audited numerical endpoints use only `propext`, `Classical.choice`, and `Quot.sound`. The exact audit is in `AppendixNumericalCertificate-audit.txt`; all 215 batch build results are in `AppendixNumericalCertificate-build.json`. Python files and JSON bound data are generation/audit aids and are not trusted by these Lean theorems.

For a source distribution, include the `.lean` files and pinned Lake dependencies. Compiled `.olean` files are rebuildable and need not be packaged.
