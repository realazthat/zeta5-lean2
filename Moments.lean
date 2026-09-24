import Construction
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.ZetaValues
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open scoped BigOperators
open MeasureTheory Set Polynomial

namespace Zeta5Construction

lemma power_exp_integrable (m : ℕ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun y : ℝ => y^m * Real.exp (-(r*y))) (Ioi 0) := by
  have hb : IntegrableOn (fun t : ℝ => Real.exp (-t) * t^m) (Ioi 0) := by
    simpa only [add_sub_cancel_right, Real.rpow_natCast] using
      (Real.GammaIntegral_convergent (s := (m : ℝ)+1) (by positivity))
  have hc : IntegrableOn (fun y : ℝ => Real.exp (-(r*y)) * (r*y)^m) (Ioi 0) := by
    simpa only [mul_zero] using
      (integrableOn_Ioi_comp_mul_left_iff (fun t : ℝ => Real.exp (-t) * t^m) 0 hr).mpr
        (by simpa only [mul_zero] using hb)
  have hfun : (fun y : ℝ => y^m * Real.exp (-(r*y))) =
      (fun y : ℝ => (r^m)⁻¹ * (Real.exp (-(r*y)) * (r*y)^m)) := by
    ext y
    rw [mul_pow]
    field_simp [ne_of_gt hr] <;> ring
  rw [hfun]
  exact hc.const_mul _

lemma power_exp_integral (m : ℕ) {r : ℝ} (hr : 0 < r) :
    (∫ y : ℝ in Ioi 0, y^m * Real.exp (-(r*y))) = (Nat.factorial m : ℝ) / r^(m+1) := by
  have hh := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (m : ℝ)+1) (by positivity) hr
  simp only [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at hh
  rw [hh]
  rw [show (m : ℝ)+1 = ((m+1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  field_simp [ne_of_gt hr]
  simp only [one_div, ← mul_pow, inv_mul_cancel₀ (ne_of_gt hr), one_pow]

/-- The lth nonnegative term of y^(2e)w(y). -/
def momentTerm (e l : ℕ) (y : ℝ) : ℝ :=
  (2*Real.pi)^4 / 12 * (l : ℝ)^4 * y^(2*e+5) *
    Real.exp (-((2*Real.pi*l)*y))

lemma momentTerm_integrable (e l : ℕ) : IntegrableOn (momentTerm e l) (Ioi 0) := by
  change Integrable (fun y : ℝ =>
    (2*Real.pi)^4 / 12 * (l : ℝ)^4 * y^(2*e+5) *
      Real.exp (-((2*Real.pi*l)*y))) (volume.restrict (Ioi 0))
  by_cases hl : l = 0
  · subst l
    simp only [Nat.cast_zero, zero_pow (by decide : 4 ≠ 0), mul_zero, zero_mul]
    exact integrable_zero _ _ _
  · have hlpos : (0 : ℝ) < l := by exact_mod_cast Nat.pos_of_ne_zero hl
    have hc := (power_exp_integrable (2*e+5) (r := 2*Real.pi*l)
      (by positivity)).const_mul ((2*Real.pi)^4 / 12 * (l : ℝ)^4)
    apply hc.congr
    filter_upwards with y
    ring

def momentIntegralConstant (e : ℕ) : ℝ :=
  (Nat.factorial (2*e+5) : ℝ) / (12 * (2*Real.pi)^(2*e+2))

lemma momentTerm_integral (e l : ℕ) :
    (∫ y : ℝ in Ioi 0, momentTerm e l y) =
      momentIntegralConstant e * (1 / (l : ℝ)^(2*e+2)) := by
  by_cases hl : l = 0
  · subst l
    simp [momentTerm]
  · have hlpos : (0 : ℝ) < l := by exact_mod_cast Nat.pos_of_ne_zero hl
    have hh := power_exp_integral (2*e+5) (r := 2*Real.pi*l) (by positivity)
    simp only [momentTerm, mul_assoc, integral_const_mul]
    simp only [mul_assoc] at hh
    rw [hh]
    unfold momentIntegralConstant
    have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    have hlne : (l : ℝ) ≠ 0 := ne_of_gt hlpos
    simp only [pow_add, mul_pow]
    field_simp <;> ring

lemma momentTerm_nonneg (e l : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ momentTerm e l y := by
  unfold momentTerm
  positivity

lemma momentTerm_integral_norm (e l : ℕ) :
    (∫ y : ℝ in Ioi 0, ‖momentTerm e l y‖) =
      momentIntegralConstant e * (1 / (l : ℝ)^(2*e+2)) := by
  rw [← momentTerm_integral]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  exact Real.norm_of_nonneg (momentTerm_nonneg e l (le_of_lt hy))

lemma momentTerm_norm_summable (e : ℕ) :
    Summable (fun l : ℕ => ∫ y : ℝ in Ioi 0, ‖momentTerm e l y‖) := by
  simp only [momentTerm_integral_norm]
  apply Summable.mul_left
  simpa only [Nat.mul_add, Nat.mul_one] using
    (hasSum_zeta_nat (k := e+1) (by omega)).summable

/-- The original series weight, multiplied by the even power, is the
termwise integrand used in the justified interchange of sum and integral. -/
lemma evenPowerWeight_eq_tsum (e : ℕ) (y : ℝ) :
    y^(2*e) * integralWeight y = ∑' l : ℕ, momentTerm e l y := by
  unfold integralWeight
  rw [← mul_assoc, ← tsum_mul_left]
  apply tsum_congr
  intro l
  unfold momentTerm
  have he : -(2*Real.pi*y) * (l : ℝ) = -((2*Real.pi*l)*y) := by ring
  rw [he]
  simp only [pow_add]
  ring

/-- The full monomial moment identity, first in zeta-series form.
All exchanges of infinite summation and integration are justified above. -/
theorem integral_evenPowerWeight_series (e : ℕ) :
    (∫ y : ℝ in Ioi 0, y^(2*e) * integralWeight y) =
      momentIntegralConstant e * (∑' l : ℕ, 1/(l : ℝ)^(2*e+2)) := by
  simp only [evenPowerWeight_eq_tsum]
  rw [← integral_tsum_of_summable_integral_norm (momentTerm_integrable e)
    (momentTerm_norm_summable e)]
  simp only [momentTerm_integral, tsum_mul_left]

lemma momentIntegralConstant_zeta (e : ℕ) :
    momentIntegralConstant e * (∑' l : ℕ, 1/(l : ℝ)^(2*e+2)) = (moment e : ℝ) := by
  have hz := (hasSum_zeta_nat (k := e+1) (by omega)).tsum_eq
  simp only [Nat.mul_add, Nat.mul_one] at hz
  rw [hz]
  unfold momentIntegralConstant moment
  push_cast
  have hf : (Nat.factorial (2*e+5) : ℝ) =
      (2*(e : ℝ)+5)*(2*(e : ℝ)+4)*(2*(e : ℝ)+3)*
        (Nat.factorial (2*e+2) : ℝ) := by
    rw [show 2*e+5 = (2*e+4)+1 by omega, Nat.factorial_succ,
      show 2*e+4 = (2*e+3)+1 by omega, Nat.factorial_succ,
      show 2*e+3 = (2*e+2)+1 by omega, Nat.factorial_succ]
    push_cast
    ring
  rw [hf]
  simp only [pow_add, mul_pow]
  norm_num
  have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hfac : (Nat.factorial (2*e+2) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2*e+2)
  field_simp
  ring

/-- Proposition 2.2 for every monomial t^e, with the paper's exact
Bernoulli normalization. This theorem has no analytic hypotheses. -/
theorem integral_evenPowerWeight (e : ℕ) :
    (∫ y : ℝ in Ioi 0, y^(2*e) * integralWeight y) = (moment e : ℝ) := by
  rw [integral_evenPowerWeight_series, momentIntegralConstant_zeta]

lemma integral_evenPowerWeight_pos (e : ℕ) :
    0 < ∫ y : ℝ in Ioi 0, y^(2*e) * integralWeight y := by
  rw [integral_evenPowerWeight_series]
  apply mul_pos
  · unfold momentIntegralConstant
    apply div_pos
    · exact_mod_cast Nat.factorial_pos (2*e+5)
    · positivity
  · have hs : Summable (fun l : ℕ => 1/(l : ℝ)^(2*e+2)) := by
      simpa only [Nat.mul_add, Nat.mul_one] using
        (hasSum_zeta_nat (k := e+1) (by omega)).summable
    apply hs.tsum_pos (fun l => by positivity) 1
    norm_num

/-- Integrability of every even-power multiple of the actual weight. -/
theorem evenPowerWeight_integrable (e : ℕ) :
    IntegrableOn (fun y : ℝ => y^(2*e) * integralWeight y) (Ioi 0) :=
  Integrable.of_integral_ne_zero (ne_of_gt (integral_evenPowerWeight_pos e))

/-- Integrability for every polynomial in y², including polynomial quotients
arising in the rational-function division in the paper. -/
theorem polynomialWeight_integrable (p : ℚ[X]) :
    IntegrableOn (fun y : ℝ => p.eval₂ (Rat.castHom ℝ) (y^2) * integralWeight y)
      (Ioi 0) := by
  simp only [Polynomial.eval₂_eq_sum, Polynomial.sum_def, Finset.sum_mul]
  apply integrable_finset_sum
  intro e he
  have hh := (evenPowerWeight_integrable e).const_mul ((p.coeff e : ℚ) : ℝ)
  apply hh.congr
  filter_upwards with y
  simp only [Rat.castHom, pow_mul, mul_assoc]
  rfl

/-- Proposition 2.2 on the complete polynomial subspace of the functional's
domain, with no unproved integrability or moment assumptions. -/
theorem polynomialFunctional_eq_integral (p : ℚ[X]) :
    (polynomialFunctional p : ℝ) =
      ∫ y : ℝ in Ioi 0, p.eval₂ (Rat.castHom ℝ) (y^2) * integralWeight y := by
  symm
  simp only [Polynomial.eval₂_eq_sum, Polynomial.sum_def, Finset.sum_mul]
  rw [integral_finset_sum]
  · simp only [← pow_mul, mul_assoc, integral_const_mul, integral_evenPowerWeight]
    simp only [polynomialFunctional, Polynomial.lsum_apply, Polynomial.sum_def,
      LinearMap.smul_apply, LinearMap.id_coe, id_eq, smul_eq_mul, Rat.cast_sum,
      Rat.cast_mul, Rat.castHom]
    apply Finset.sum_congr rfl
    intro e he
    exact mul_comm _ _
  · intro e he
    have hh := (evenPowerWeight_integrable e).const_mul ((p.coeff e : ℚ) : ℝ)
    apply hh.congr
    filter_upwards with y
    simp only [Rat.castHom, pow_mul, mul_assoc]
    rfl

end Zeta5Construction
