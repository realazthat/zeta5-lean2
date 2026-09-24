import IntegerPolynomial
import RealDeterminantBound
import NormalizerBound
import FinalAssembly

/-!
# Irrationality of ζ(5)

This endpoint combines the actual integer polynomial construction, the
prime-normalization estimate, and the real determinant estimate. Its statement
has no hypotheses and its proof uses no additional axioms.
-/

noncomputable section
open Filter Polynomial

namespace Zeta5

/-- The real value of the Riemann zeta function at five is irrational. -/
theorem irrational_zeta_five : Irrational ((riemannZeta (5:ℂ)).re) := by
  apply Zeta5FinalAssembly.irrational_of_paperPolynomial_integer_log_decay 100000
  · exact Zeta5Parameters.eventually_paperPolynomial_integer 100000 (by norm_num)
  · apply Zeta5FinalAssembly.paperPolynomial_log_decay_of_bounds 100000
      ((Zeta5NormalizationTail.normalizationCoefficient:ℝ)+1/10000)
      (-(2733991/2000000:ℝ)+1/10000)
    · norm_num [Zeta5NormalizationTail.normalizationCoefficient]
    · exact Zeta5Parameters.eventually_log_normalizer_upper (1/10000) (by norm_num)
    · simpa only [Zeta5Parameters.N,Zeta5Parameters.h,Nat.cast_mul,Nat.cast_ofNat] using
        Zeta5Construction.actual_eventually_normalizedDeterminant_log_upper (1/10000) (by norm_num)

/-- Equivalent statement for the convergent reciprocal-fifth-power series. -/
theorem irrational_reciprocal_fifth_power_sum :
    Irrational (∑' n : ℕ, (1:ℝ)/(n:ℝ)^5) := by
  have he := Zeta5Reduction.zeta5_eq_series
  exact he ▸ irrational_zeta_five

#print axioms irrational_zeta_five
#print axioms irrational_reciprocal_fifth_power_sum
end Zeta5
