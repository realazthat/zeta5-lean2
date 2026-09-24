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
Mathlib revision `065356127b1dc0016f66b7283ce0ce2c4055aa55` for both ports.
The root `lean-toolchain` selects Lean 4.35.0-rc2 for this workspace.
The nested toolchain files and manifests preserve upstream snapshot metadata,
including older Lean and Mathlib pins; they are not separate root lockfiles for
this build. Run Lake from the repository root, not inside a vendor directory.
Root path requirements select these source trees, while the root manifest
records the workspace dependency resolution. This does not claim that each
vendor snapshot builds independently with its retained historical configuration.

Compatibility changes address conditional simplification, finite-list access,
removed Lean names in an axiom classifier, Lean's changed `Decidable` representation
in the kernel-only certificate verifier, equivalence coercions, almost-everywhere
interval membership, and explicit real type annotations. The verifier reduces
`decide` to a Boolean and still constructs a proof checked by Lean's kernel;
`Tests/KernelCertificates.lean` checks acceptance and rejection in kernel mode.
The changed Lean files relative to the listed upstream commits are:

| File relative to `vendor/` | Compatibility change |
| --- | --- |
| `leancert/LeanCert/Core/Dyadic.lean` | Supply conditional branches to simplification. |
| `leancert/LeanCert/Engine/RootFinding/Krawczyk.lean` | Use the derivative proof directly. |
| `leancert/LeanCert/Engine/TaylorModel/Hyperbolic.lean` | Rewrite finite-list access. |
| `leancert/LeanCert/Tactic/Verification.lean` | Reduce the Boolean decision and quote removed names. |
| `PrimeNumberTheoremAnd/PrimeNumberTheoremAnd/Consequences.lean` | Supply the prime-factor multiplicity rewrite. |
| `PrimeNumberTheoremAnd/PrimeNumberTheoremAnd/Wiener.lean` | Update coercions, interval membership, and real annotations. |

This list was checked against the immutable upstream Git blobs, ignoring line
ending differences. Proof statements are not intentionally weakened; compare
those blobs with the vendored paths for the exact changes.

Upstream libraries contain additional unfinished or compiler-assisted results
outside the submitted theorem's proof dependencies. The final Solution axiom
audit and Comparator must establish that neither `sorryAx` nor compiler-trust
axioms occur in the submitted proofs; mere successful import is insufficient.
