# Compact proof sources

The verified baseline is commit
`5e55b5ff7a0d57a758e0bd7462753ea8e674c00e` on `palomar-preparation`.
This separate branch replaces repeated numerical certificates and proof assembly
with documented Lean macros while preserving all appendix theorem statements.

First-party Lean source: **42,615,395 → 2,251,837 bytes**, a **94.72% reduction**.
This counts the same first-party source inventory used by `project_audit.py`,
including the two new helper modules. It excludes vendored dependencies, build
artifacts, documentation, and Git history. It is not a claim of minimality or of
an equivalent reduction in compiled proof size.

The principal reductions are the 685 potential bounds, 684 field bounds, 684 cell
bounds, and sixteen support logarithm tables. Exact reconstruction was compared
with every replaced rational logarithm and trigonometric table before applying
the transformation. A source comparison also checked that the appendix theorem
names and statements were unchanged.

`CertificateData.lean` generates exact rational candidate data;
`CertificateTactics.lean` assembles ordinary checked proofs. Numerical acceptance
still uses `decide +kernel`. No mathematical assumptions or compiler-trust
fallback were added. Read [NUMERICAL_CERTIFICATES.md](NUMERICAL_CERTIFICATES.md)
for the formulas, argument order, and trust boundary.

The readability pass retains explicit theorem statements and rational bounds,
formats the sixteen component bounds in groups of four, names the reusable
assembly operations, and documents each helper module and its rounding rules.

PR #2 targets `palomar-preparation`. The Lean 4.35 port, dependency vendoring,
and Challenge/Solution interfaces are inherited from PR #1 at
`5e55b5ff7a0d57a758e0bd7462753ea8e674c00e`. PR #2 adds certificate
compaction, readability documentation, CI repairs, and evidence corrections.

## Verification

The saved local logs for compact source commit
`53f1134b621452a5b8339c3050367259d46b4de6` record a complete 4,590-job build
and acceptance by all three Comparator kernels. con-ron accepted 91,762 declarations;
NanoDa and the default Lean kernel also accepted the solution. Both final
statements use only `propext`, `Classical.choice`, and `Quot.sound`.
Full logs and fingerprints are in `verification/codegolf/`. These logs do not
independently attest process exit status, checker binary integrity, or sandbox
enforcement. They are historical local evidence, not a hosted CI result.
