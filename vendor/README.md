# Solution-only dependency ports

These source snapshots are included so that compatibility edits are part of the
immutable submission, rather than edits to an untracked dependency checkout.
They are imported only by the Solution development, never by Challenge.

| Directory | Upstream repository | Original commit |
| --- | --- | --- |
| `leancert` | https://github.com/alerad/leancert | `6b11513512c9d27183fb4725bfc291ab38b4a6d7` |
| `PrimeNumberTheoremAnd` | https://github.com/AlexKontorovich/PrimeNumberTheoremAnd | `a5154676af9aa3095150ee410cdda80555aa0642` |

The upstream license files and authorship notices are retained. The repository's
MIT license does not replace those licenses. Root Lake requirements select the
exact Mathlib 4.35.0-rc2 dependency closure for both ports.

Compatibility changes address conditional simplification, finite-list access,
removed Lean names in an axiom classifier, Lean's changed `Decidable` representation
in the kernel-only certificate verifier, equivalence coercions, almost-everywhere
interval membership, and explicit real type annotations. The verifier reduces
`decide` to a Boolean and still constructs a proof checked by Lean's kernel;
`Tests/KernelCertificates.lean` checks acceptance and rejection in kernel mode.
Proof statements are
not intentionally weakened. See the Git diff against the listed upstream commits
for the precise edits.

Upstream libraries contain additional unfinished or compiler-assisted results
outside the submitted theorem's proof dependencies. The final Solution axiom
audit and Comparator must establish that neither `sorryAx` nor compiler-trust
axioms occur in the submitted proofs; mere successful import is insufficient.
