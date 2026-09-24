# Numerical certificates

The appendix keeps every theorem statement and explicit rational bound visible.
Three proof macros replace repeated certificate tables and proof boilerplate.

## Files and inputs

- `CertificateData.lean` constructs exact rational data and Lean syntax.
- `CertificateTactics.lean` assembles proofs using the existing analytic lemmas.
- `AppendixPotential/` lists a point and sixteen component bounds in the order of
  `Zeta5RealEnergy.arcsineData`.
- `AppendixField/` lists a point followed by arctangent lower and upper bounds,
  then logarithm lower and upper bounds.
- `AppendixCells/` identifies the two endpoint potential theorems and the field
  lower-bound theorem used on each cell.

## Exact data generation

All generation uses integers and rational arithmetic; no floating-point
calculation participates. A logarithm chain repeatedly replaces a positive
rational q with `(floor(sqrt(q) * 2^80) + 1) / 2^80`. Integer square root computes
that numerator exactly. There are 34 steps in the appendix certificates.
The additional unit gives a strict upper approximation even for an exact square.

For a trigonometric certificate, the starting angle is divided by `2^28`.
Polynomial small-angle bounds produce an initial sine/cosine box, rounded
outward to a grid with 128 fractional binary digits. Twenty-eight double-angle
steps recover bounds at the original angle, again rounding outward each time.
The named fields of `RationalBox` record both endpoints for sine and cosine.

The potential macro uses the original sixteen source-table intervals and
weights. Inside an interval it invokes the corresponding support-log theorem.
Outside, it constructs an upper square-root witness on the `10^20` grid and
checks the logarithmic upper bound. It then combines the sixteen inequalities
with their nonnegative weights.

The field macro constructs lower and upper square-root witnesses on the same
`10^20` grid. It checks the two arctangent and two logarithm bounds, uses the
existing rational lower bound for pi, and chooses the appropriate square-root
endpoint according to the sign of its multiplier. The cell macro combines
endpoint potential bounds and the cell's field lower bound by linear arithmetic.

## What is trusted

The generators produce candidate data and ordinary proof syntax. They do not
introduce axioms. Each generated logarithmic or trigonometric certificate is
checked with `decide +kernel` against the existing verified Boolean checker.
The analytic assembly uses ordinary Lean lemmas and tactics. A wrong generated
witness must fail the checker or the subsequent proof, rather than becoming a
trusted numerical assertion. The code does not use `native_decide`.

Compilation still expands the certificates into proof terms. This change
reduces maintained source size; it does not claim a comparable reduction in
compiled proof size or verification time. The entire final theorem is also
checked through Palomar's sandboxed Comparator and independent kernels; consult
`PALOMAR.md` for the recorded status of the particular branch.
