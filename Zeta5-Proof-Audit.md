# Zeta(5) proof audit

Reviewed 24 September 2026.

**Verdict:** The saved project contains a complete, unconditional Lean proof of the irrationality of ζ(5), supported by its recorded successful kernel replay. This review found no missing mathematical hypothesis or proof placeholder. It verified the correspondence between the delivered sources, surviving compiled artifacts, and replay records. A new end-to-end compilation or kernel replay was **not completed** in this review, so this is not a claim of fresh independent reproduction.

The original paper is Aabir Fauzan’s [Zenodo record 22826419](https://zenodo.org/records/22826419). The shared [original proof conversation](https://chatgpt.com/share/6ab4a2e3-4ab4-83ea-9d10-9943687888e0) was read directly, together with the other two supplied shared conversations. Tool outputs are redacted in those public transcripts; the verdict therefore relies on examination of the actual saved project as well.

The endpoint in `Main.lean` is:

```lean
Zeta5.irrational_zeta_five : Irrational ((riemannZeta (5 : ℂ)).re)
```

It has no hypotheses. The second endpoint states irrationality of the sum of reciprocal fifth powers. The series includes the zero index, whose summand is zero under Lean’s division convention. The source uses mathlib’s ordinary irrationality and zeta definitions; this review found no replacement definitions shadowing those names.

| Check performed in this review | Result |
|---|---|
| Local source inventory | 411 Lean modules |
| Dependency closure of `Main` and `AxiomAudit` | 406 modules; no missing local imports |
| Closure versus recorded replay inventory | Exact match |
| Source hashes versus recorded replay | All 406 match |
| Surviving compiled artifact hashes, including recorded parts | All match |
| Delivered source/build manifest | All 418 entries match |
| Recorded replay exit codes | All 406 are zero; report marks replay complete |
| Source scan after removal of comments | No `sorry`, `admit`, added `axiom`, `native_decide`, `unsafe`, or scanned custom elaborator/foreign-code mechanisms |
| Pinned external dependency commits | All 14 recovered and matched |
| Exact final decay arithmetic | Approximately −11.4136744108, strictly below −10 |

The saved `AxiomAudit.txt` reports only `propext`, `Classical.choice`, and `Quot.sound` for both final endpoints and their main inputs. These are Lean’s standard foundations. This axiom output was inspected as an existing record, not regenerated in this review.

The proof’s final assembly supplies all three substantive inputs: integer coefficients of the actual polynomial family, positivity and decay of its determinant evaluation, and the prime-normalizer growth bound. The resulting positive values decay faster than a rational input could permit for integer polynomials of degree at most 37n. In particular, the early conditional theorem in `Zeta5Reduction.lean` does not leave an assumption in `Main.lean`; the subsequent modules supply the inputs used by the final theorem.

The package explicitly distinguishes the completed historical kernel replay from a partial clean Lake rebuild. Its report says that 42 local modules were rebuilt through ordinary Lake, while all 406 modules in the final closure passed replay of the stored proof terms. Thus, “the clean rebuild was not completed” does not by itself identify a mathematical gap.

For fresh reproduction, this review installed the pinned Lean 4.32.2 toolchain and recovered all dependency commits. The additional verification attempt was stopped during the mathlib artifact download; the final theorem was not freshly recompiled. No proof source was changed. Porting to the later toolchain requested for Palomar was outside this completeness audit.

Reviewed archive: `Zeta5Formalization.zip`, saved version 6.

SHA-256: `1986751614e319c9d6dfbc3e37c0c455959c6f7fe02ed46ef74854a0969aa43a`.
