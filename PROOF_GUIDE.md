# Guide to the ζ(5) formalization

This guide maps the proof's mathematical structure to its Lean files. The source is Aabir Fauzan, “ζ(5) is irrational,” [Zenodo 22826419](https://zenodo.org/records/22826419). The current port uses Lean 4.35.0-rc2, Mathlib, and the proved prime number theorem from `PrimeNumberTheoremAnd`.

**Verification scope.** The saved build and Comparator logs concern compact
source commit `53f1134b621452a5b8339c3050367259d46b4de6` under Lean
4.35.0-rc2. They report the complete build and acceptance by all three kernels.
Both final theorem axiom listings contain only `propext`, `Classical.choice`,
and `Quot.sound`. These historical logs do not establish current hosted CI
success or independent source-paper fidelity; see `PALOMAR.md` for provenance.
Earlier packaging reports that did not repeat a full clean build concern their
own historical checks, rather than the later recorded complete build.

Module introductions in `Zeta5Reduction.lean` and `PrimeSums.lean` retain
historical toolchain descriptions; the root `lean-toolchain` and manifest govern
the current port. The reduction module proves a conditional implication on
purpose; `Main.lean` supplies its construction and estimates unconditionally.
Its file-local disclaimer does not describe the assembled project's endpoint.

The proved target in `Main.lean` is:

```lean
Zeta5.irrational_zeta_five :
  Irrational ((riemannZeta (5 : ℂ)).re)
```

Here `Irrational x` is mathlib's usual assertion that `x` is not the image of a rational number. In `Zeta5Reduction.lean`, `zeta5` is defined as the displayed real part, and `zeta5_eq_series` proves

\[
\zeta(5)=\sum_{r=0}^{\infty}\frac1{r^5}.
\]

Lean defines the zero summand to be zero, so this is the ordinary sum over positive integers. `Main.lean` also states the equivalent irrationality theorem for this series.

**The constructed polynomial.** Fix

\[
K=40n,\qquad N=3n,\qquad h=37n,\qquad M=100000.
\]

`Construction.lean` defines \(D_A(t)=\prod_{j=1}^{A}(t+j^2)\), the rational functional \(\mu_X\), and the \(h\times h\) matrix whose \((i,j)\) entry applies that functional to

\[
\frac{D_N(t)^6t^{i+j}}{D_K(t)}
=\frac{D_N(t)^5t^{i+j}}{D_K(t)/D_N(t)}.
\]

Polynomial division and residues give each entry explicitly as an affine polynomial in \(X\). Its determinant is `determinant N h`. Multiplication by the explicit positive rational factorial factor `normalizingScalar N h` gives `normalizedDeterminant N h`, denoted \(F_K\).

`PaperParameters.lean` then defines

\[
P_{n,M}(X)=m_{K,M}F_K(X),\qquad
m_{K,M}=\prod_{p\le2h,\ p\text{ prime}}p^{-L_p(K,M)}.
\]

The exponents are signed: positive divisibility bounds permit division by prime powers. The implementation uses the sufficient `coarseOuterExponent` in its outer branch. `paperPolynomial_degree` proves the exact degree \(37n\), independently of the later estimates.

**Integer coefficients: the arithmetic gates.** The three ranges below partition the primes. The conditions in the table are literal integer inequalities used by the implementation.

| Range | What is proved | Main entry points |
|---|---|---|
| Small: \(pM\le K\) | A binomial basis makes the relevant numerators integer valued. Finite differences, a Lipschitz estimate, pole cancellation, and factorial estimates bound every matrix coefficient, including at \(p=2,3\). | `SmallPrimeFunctional.lean`, `SmallPrimeLipschitz.lean`, `SmallPrimeActual.lean`, `SmallPrimeEntry.lean`; `Zeta5SmallPrimeDeterminant.actual_small_localExponent_bound` in `SmallPrimeBound.lean`. |
| Inner: \(K<pM\) and \(3p\le K\) | The actual rational functional is distributed over residue disks. Near-pole interpolation and convergent far-pole expansions give entry bounds in the actual Chinese remainder basis; assigned row weights yield the determinant bound. | `ActualInnerDiskBound.lean`, theorem `Zeta5InnerDisk.actual_disk_bound`; `InnerSources.lean`, `InnerDeterminant.lean`; `Zeta5InnerNormalized.actual_inner_localExponent_bound`. |
| Outer: \(K<pM\) and \(K<3p\) | Explicit residue classes and a polynomial correction matrix give a weighted determinant estimate with the full correction rank allowed as a loss. | `OuterEntries.lean`, `OuterDeterminant.lean`, `OuterWeightAggregation.lean`; `Zeta5OuterNormalized.actual_outer_localExponent_bound`. |
| Outside the product: \(p>2h\) | Coefficients of \(F_K\) are already integral at these primes. | `Zeta5OuterNormalized.actual_outside_normalization_bound`. |

`IntegerPolynomial.lean` combines those bounds with `Normalization.lean`: a rational number whose valuation is nonnegative at every prime is an integer. Thus, for admissible parameters, `paperPolynomial n M` is the image of an actual polynomial over \(\mathbb Z\). Zero coefficients are handled separately and impose no valuation hypothesis.

Admissibility is \(40\le M\) and \(200M^2\le K\). It is not a vacuous restriction: `Zeta5Parameters.eventually_admissible` in `NormalizationLog.lean` proves it eventually for every fixed \(M\ge40\), using \(n\ge5M^2\).

The inner analytic argument can be inspected independently through `Zeta5Local.scaled_integer_presentation_bound` in `ScaledIntegerLocalBound.lean`. `InnerPullbackCertificate.lean` supplies the actual finite partial-fraction identity; `InnerDiskPadic.lean` and `InnerDiskRoots.lean` supply the factorizations and root conditions. `ActualInnerDiskBound.lean` discharges those hypotheses for every actual row pair and residue disk. Its conclusion concerns the literal local term of the actual \(\mu\) distribution, not an assumed replacement functional.

**Positive values and real decay.** `Moments.lean`, `PoleKernel.lean`, `PoleIntegral.lean`, and `MatrixIntegral.lean` identify evaluation at the actual zeta series with integrals against a positive weight. The matrix is positive definite, so

\[
F_K(\zeta(5))>0,\qquad P_{n,M}(\zeta(5))>0.
\]

The upper bound passes through a multiple-integral determinant formula and logarithmic energy. `RealEnergy.lean` proves the energy inequality; the arcsine-mixture modules supply the explicit comparison measure. `PotentialFieldCertificate.lean` joins the compact numerical certificate to a bound for the infinite tail. `AppendixNumerics.lean` and the rational logarithm/trigonometric certificate modules verify the numerical inequalities inside Lean.

The resulting endpoint, `Zeta5Construction.actual_eventually_normalizedDeterminant_log_upper` in `RealDeterminantBound.lean`, has no analytic or numerical assumptions beyond \(\varepsilon>0\):

\[
\log F_{40n}(\zeta(5))
\le\left(-\frac{2733991}{2000000}+\varepsilon\right)(40n)^2
\quad\text{eventually}.
\]

**The prime-normalizer asymptotic.** `NormalizationLog.lean` gives the exact identity

\[
\log m_{K,M}=-\sum_{p\le2h}L_p(K,M)\log p.
\]

`PrimeSums.lean` derives the weighted prime-sum limits from the proved Chebyshev form of PNT. `OuterPrimeUpperLimit.lean` handles the outer contribution. `InnerPrimeCells.lean`, `InnerPrimeLimit.lean`, and `InnerPrimeBound.lean` handle the finite inner interval through explicit affine cells. `NormalizationTail.lean` bounds the remaining integral; `TailPrimeBound.lean` transfers it to the actual tail prime sum. `SmallPrimeAsymptotics.lean` bounds the small-prime contribution, and `AllocationPrimeBound.lean` bounds the allocation loss.

`NormalizationRanges.lean` proves `Zeta5Parameters.log_normalizer_le_ranges`, and `NormalizerConstants.lean` identifies the sum of the certified constants. `NormalizerBound.lean` joins all five contributions with errors of size \(\varepsilon/5\). Its unconditional endpoint, `Zeta5Parameters.eventually_log_normalizer_upper`, proves for every \(\varepsilon>0\):

\[
\log m_{40n,100000}\le(A+\varepsilon)(40n)^2
\quad\text{eventually}.
\]

The exact coefficient is defined and evaluated in `NormalizationTail.lean`:

\[
A=\frac{2001164943296771438302478205521}
        {1471810649812878375000000000000}.
\]

The development uses several explicitly accounted-for weakenings of the paper's bounds:

| Choice | Consequence in the final coefficient |
|---|---|
| Charge the entire outer polynomial correction rank. | Add \(9/640\); the outer coefficient becomes \(129101/96000\). |
| Use the relaxed inner allocation estimate. | Add \(1/36\). |
| Prove \(\lvert C(x)\rvert\le17\) for the periodic cubic primitive. | The tail estimate uses \(34/M^3\), with the endpoint term \(-2677/48000\). |
| Fix \(M=100000\). | All cutoff and admissibility conditions are eventual conditions on \(n\). |
| Aim for decay \(10n^2\). | This leaves room for the conservative losses and positive asymptotic errors. |

These losses are included in \(A\); they are not omitted numerical tolerances.

**The last implication.** `FinalAssembly.lean` already proves the complete implication from eventual integrality and eventual logarithmic decay to irrationality. The exact checked inequality is

\[
1600\left(A+\frac1{10000}-\frac{2733991}{2000000}
                    +\frac1{10000}\right)<-10.
\]

Consequently the two eventual estimates give positive integer-polynomial values below \(e^{-10n^2}\), with degrees \(37n\). If \(\zeta(5)=a/b\) were rational, every nonzero such value would have magnitude at least \(b^{-37n}\). Quadratic exponential decay contradicts this linear-degree denominator bound. The proof of that implication is `Zeta5Reduction.irrational_of_small_polynomial_family`.

For an audit, start with `Main.lean` and its `#print axioms` output, then follow the named endpoints above. The observed axiom set for both final theorems is exactly the standard foundations `propext`, `Classical.choice`, and `Quot.sound`; it contains no `sorryAx`, additional arithmetic axiom, or assumed paper estimate. Build instructions and dependency pins belong to `README.md` and the project configuration. The documented build command reproduces the project; cached replay lines in historical logs do not establish a from-scratch rebuild. Current verification must be assessed at its actual commit.
