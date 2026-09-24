import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Irrationality of the Riemann zeta value at five

These statements use Mathlib's ordinary Riemann zeta function, real numbers,
irrationality predicate, and infinite sum. There are no mathematical hypotheses.
The sum includes n = 0; its summand is zero under Lean's division convention.
The deliberately missing proofs belong only to this independent statement file.
The source is Aabir Fauzan, “ζ(5) is irrational”, version 1 (17 September 2026),
https://doi.org/10.5281/zenodo.22826419. The claimed quantitative irrationality
measure in that paper is outside the scope of these two statements.
-/

namespace Zeta5Palomar

/-- The real value of the Riemann zeta function at five is irrational. -/
theorem irrational_zeta_five : Irrational ((riemannZeta (5 : ℂ)).re) := by
  sorry

/-- The sum of reciprocal fifth powers is irrational. -/
theorem irrational_reciprocal_fifth_power_sum :
    Irrational (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 5) := by
  sorry

end Zeta5Palomar
