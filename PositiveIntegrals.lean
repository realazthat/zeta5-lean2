import Moments
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

noncomputable section
open scoped BigOperators
open MeasureTheory Set Polynomial

namespace Zeta5Construction

lemma realPolynomialWeight_integrable (p : ℝ[X]) :
    IntegrableOn (fun y : ℝ => p.eval (y^2) * integralWeight y) (Ioi 0) := by
  simp only [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.sum_mul]
  apply integrable_finset_sum
  intro e he
  have hh := (evenPowerWeight_integrable e).const_mul (p.coeff e)
  apply hh.congr
  filter_upwards with y
  simp only [pow_mul, mul_assoc]

lemma integralWeight_integrable : IntegrableOn integralWeight (Ioi 0) := by
  simpa only [mul_zero, pow_zero, one_mul] using evenPowerWeight_integrable 0

/-- D_N regarded as a real polynomial. -/
def realDenominator (N : ℕ) : ℝ[X] := (denominator N).map (Rat.castHom ℝ)

lemma realDenominator_eval (N : ℕ) (t : ℝ) :
    (realDenominator N).eval t = ∏ k ∈ Finset.range N, (t+(k+1 : ℝ)^2) := by
  rw [realDenominator, Polynomial.eval_map, denominator, eval₂_finset_prod]
  apply Finset.prod_congr rfl
  intro k hk
  simp only [eval₂_add, eval₂_X, eval₂_C]
  norm_cast

lemma realDenominator_eval_ge_one (N : ℕ) (y : ℝ) :
    1 ≤ (realDenominator N).eval (y^2) := by
  rw [realDenominator_eval]
  calc
    1 = ∏ k ∈ Finset.range N, (1 : ℝ) := by simp
    _ ≤ _ := by
      apply Finset.prod_le_prod (fun k hk => zero_le_one)
      intro k hk
      have hkpos : (1 : ℝ) ≤ k+1 := by linarith [(show (0 : ℝ) ≤ k from Nat.cast_nonneg k)]
      nlinarith [sq_nonneg y]

lemma realDenominator_eval_pos (N : ℕ) (y : ℝ) :
    0 < (realDenominator N).eval (y^2) :=
  lt_of_lt_of_le zero_lt_one (realDenominator_eval_ge_one N y)

/-- The actual positive integrand in the last display of Proposition 2.2. -/
def quadraticIntegrand (N K : ℕ) (q : ℝ[X]) (y : ℝ) : ℝ :=
  (realDenominator N).eval (y^2)^6 * (q.eval (y^2))^2 /
    (realDenominator K).eval (y^2) * integralWeight y

lemma quadraticIntegrand_nonneg (N K : ℕ) (q : ℝ[X]) {y : ℝ} (hy : 0 < y) :
    0 ≤ quadraticIntegrand N K q y := by
  unfold quadraticIntegrand
  exact mul_nonneg
    (div_nonneg (mul_nonneg (pow_nonneg (realDenominator_eval_pos N y).le _) (sq_nonneg _))
      (realDenominator_eval_pos K y).le) (integralWeight_pos hy).le

lemma quadraticIntegrand_pos (N K : ℕ) (q : ℝ[X]) {y : ℝ}
    (hy : 0 < y) (hq : q.eval (y^2) ≠ 0) : 0 < quadraticIntegrand N K q y := by
  unfold quadraticIntegrand
  exact mul_pos
    (div_pos (mul_pos (pow_pos (realDenominator_eval_pos N y) _) (sq_pos_of_ne_zero hq))
      (realDenominator_eval_pos K y)) (integralWeight_pos hy)

/-- No denominator estimates are assumed: D_K(y²)≥1 gives an explicit
integrable polynomial majorant for the actual rational quadratic form. -/
theorem quadraticIntegrand_integrable (N K : ℕ) (q : ℝ[X]) :
    IntegrableOn (quadraticIntegrand N K q) (Ioi 0) := by
  let p : ℝ[X] := (realDenominator N)^6*q^2
  apply (realPolynomialWeight_integrable p).mono'
  · have hm : Measurable (fun y : ℝ =>
        (realDenominator N).eval (y^2)^6 * (q.eval (y^2))^2 /
          (realDenominator K).eval (y^2)) := by fun_prop
    exact hm.aestronglyMeasurable.mul integralWeight_integrable.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [Real.norm_of_nonneg (quadraticIntegrand_nonneg N K q hy)]
    dsimp [quadraticIntegrand, p]
    simp only [eval_mul, eval_pow]
    apply mul_le_mul_of_nonneg_right _ (integralWeight_pos hy).le
    apply div_le_self
    · positivity
    · exact realDenominator_eval_ge_one K y

/-- A nonzero polynomial q remains nonzero after substituting y². -/
lemma comp_square_ne_zero {q : ℝ[X]} (hq : q ≠ 0) : q.comp (X^2) ≠ 0 := by
  rw [ne_eq, Polynomial.comp_eq_zero_iff]
  simp only [hq, false_or, not_and]
  intro h
  intro heq
  have hc := congrArg (fun p : ℝ[X] => p.coeff 2) heq
  simp at hc

/-- The exceptional y for which q(y²)=0 form a finite set. -/
lemma finite_square_roots {q : ℝ[X]} (hq : q ≠ 0) :
    Set.Finite {y : ℝ | q.eval (y^2) = 0} := by
  simpa only [Polynomial.IsRoot, eval_comp, eval_pow, eval_X] using
    Polynomial.finite_setOf_isRoot (comp_square_ne_zero hq)

/-- The actual quadratic form integral is strictly positive for every
nonzero real polynomial. No rational-functional integral identity is assumed. -/
theorem quadraticIntegral_pos (N K : ℕ) {q : ℝ[X]} (hq : q ≠ 0) :
    0 < ∫ y : ℝ in Ioi 0, quadraticIntegrand N K q y := by
  have hpos : ∀ᵐ y : ℝ ∂volume.restrict (Ioi 0), 0 < quadraticIntegrand N K q y := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi,
      (finite_square_roots hq).countable.ae_notMem (volume.restrict (Ioi 0))] with y hy hqy
    exact quadraticIntegrand_pos N K q hy hqy
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi 0)] quadraticIntegrand N K q :=
    hpos.mono (fun y hy => hy.le)
  have hne : (∫ y : ℝ in Ioi 0, quadraticIntegrand N K q y) ≠ 0 := by
    intro hz
    have hae := (integral_eq_zero_iff_of_nonneg_ae hnonneg
      (quadraticIntegrand_integrable N K q)).mp hz
    have hfalse : ∀ᵐ y : ℝ ∂volume.restrict (Ioi 0), False := by
      filter_upwards [hpos, hae] with y hy hz
      exact (ne_of_gt hy) hz
    have hn := (ae_iff.mp hfalse)
    simpa only [not_false_eq_true, setOf_true, Measure.restrict_apply_univ, Real.volume_Ioi, ENNReal.top_ne_zero] using hn

  exact lt_of_le_of_ne (integral_nonneg_of_ae hnonneg) hne.symm

end Zeta5Construction
