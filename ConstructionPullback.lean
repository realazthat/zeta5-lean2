import Construction
import PolynomialDistribution

/-! Exact connection from the manuscript's μ polynomial functional to its
p-adic τ coefficient kernel, through t=-x². -/
namespace Zeta5Construction
open Polynomial

lemma pullback_monomial (e : ℕ) (a : ℚ) :
    (X : ℚ[X]) ^ 5 * (monomial e a).comp (-(X ^ 2)) =
      monomial (2 * e + 5) (a * (-1) ^ e) := by
  rw [Polynomial.monomial_comp, ← Polynomial.C_mul_X_pow_eq_monomial]
  rw [neg_pow, ← pow_mul, map_mul, map_pow, map_neg, map_one, pow_add]
  ring

/-- Equation3.1 for the complete polynomial contribution, with the actual
μ functional used in the determinant construction. -/
theorem polynomialFunctional_pullback (P : ℚ[X]) :
    polynomialFunctional P =
      Zeta5Local.rationalTauFunctional ((X : ℚ[X]) ^ 5 * P.comp (-(X ^ 2))) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      rw [map_add, hP, hQ, Polynomial.add_comp, mul_add, map_add]
  | monomial e a =>
      rw [pullback_monomial, Zeta5Local.rationalTauFunctional_monomial]
      simp only [polynomialFunctional, Polynomial.lsum_apply, Polynomial.sum_monomial_index,
        LinearMap.smul_apply, LinearMap.id_coe, id_eq, smul_eq_mul, mul_zero]
      have he : 2 * e + 5 - 3 = 2 * e + 2 := by omega
      simp only [Zeta5Local.rationalTauMoment, moment, he]
      push_cast
      ring

/-- The actual μ polynomial functional therefore agrees with the bounded
p-adic kernel extension after the pullback. -/
theorem polynomialFunctional_padic_pullback {p : ℕ} [Fact p.Prime] (P : ℚ[X]) :
    (polynomialFunctional P : ℚ_[p]) =
      Zeta5Local.tauPolynomial
        (((X : ℚ[X]) ^ 5 * P.comp (-(X ^ 2))).map (Rat.castHom ℚ_[p])) := by
  rw [Zeta5Local.tauPolynomial_map_rat, polynomialFunctional_pullback]

#print axioms polynomialFunctional_padic_pullback
end Zeta5Construction
