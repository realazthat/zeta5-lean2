import GramIntegral

noncomputable section
open scoped BigOperators
open MeasureTheory Set Polynomial Matrix

namespace Zeta5Construction

lemma gramWeight_pos (N h : ℕ) {y : ℝ} (hy : 0 < y) : 0 < gramWeight N h y := by
  unfold gramWeight
  exact mul_pos (div_pos (pow_pos (realDenominator_eval_pos N y) _)
    (realDenominator_eval_pos (N+h) y)) (integralWeight_pos hy)

lemma rationalMomentIntegrand_eq_weight (N h e : ℕ) (y : ℝ) :
    rationalMomentIntegrand N h e y = (y^2)^e * gramWeight N h y := by
  rw [rationalMomentIntegrand_eq]
  unfold gramWeight
  ring

lemma rationalMomentIntegral_pos (N h e : ℕ) :
    0 < ∫ y : ℝ in Ioi 0, rationalMomentIntegrand N h e y := by
  have hp (y : ℝ) (hy : 0 < y) : 0 < rationalMomentIntegrand N h e y := by
    rw [rationalMomentIntegrand_eq_weight]
    exact mul_pos (pow_pos (sq_pos_of_pos hy) _) (gramWeight_pos N h hy)
  have hn : 0 ≤ᵐ[volume.restrict (Ioi 0)] rationalMomentIntegrand N h e := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact (hp y hy).le
  rw [setIntegral_pos_iff_support_of_nonneg_ae hn (rationalMomentIntegrand_integrable N h e)]
  have hs : Ioi (0 : ℝ) ⊆ Function.support (rationalMomentIntegrand N h e) ∩ Ioi 0 := by
    intro y hy
    exact ⟨ne_of_gt (hp y hy), hy⟩
  exact lt_of_lt_of_le (by simp) (measure_mono hs)

/-- The exact Jacobian-weighted one-variable measure after y=K√t. -/
def scaledGramWeight (N h : ℕ) (K : ℝ) (t : ℝ) : ℝ :=
  (K/2)*t^(-(1/2 : ℝ))*gramWeight N h (K*Real.sqrt t)

def scaledMomentIntegrand (N h : ℕ) (K : ℝ) (e : ℕ) (t : ℝ) : ℝ :=
  t^e * scaledGramWeight N h K t

lemma scaledMoment_pointwise (N h e : ℕ) {K t : ℝ} (ht : 0 < t) :
    K*((1/2)*t^(-(1/2 : ℝ))) * rationalMomentIntegrand N h e (K*Real.sqrt t) =
      K^(2*e)*scaledMomentIntegrand N h K e t := by
  rw [rationalMomentIntegrand_eq_weight]
  unfold scaledMomentIntegrand scaledGramWeight
  rw [mul_pow, Real.sq_sqrt ht.le, mul_pow, pow_mul]
  ring

/-- The scalar change of variables behind the paper's multivariate scaling.
This equality uses the unrestricted Bochner change-of-variables theorem. -/
theorem rationalMomentIntegral_scaled (N h e : ℕ) {K : ℝ} (hK : 0 < K) :
    (∫ y : ℝ in Ioi 0, rationalMomentIntegrand N h e y) =
      K^(2*e)*(∫ t : ℝ in Ioi 0, scaledMomentIntegrand N h K e t) := by
  let g := rationalMomentIntegrand N h e
  have hs := integral_comp_mul_left_Ioi g 0 hK
  simp only [mul_zero, smul_eq_mul] at hs
  have hr := integral_comp_rpow_Ioi (fun y : ℝ => g (K*y)) (p := (1/2 : ℝ)) (by norm_num)
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1/2)] at hr
  simp only [← Real.sqrt_eq_rpow, smul_eq_mul] at hr
  calc
    _ = K*(∫ y : ℝ in Ioi 0, g (K*y)) := by
      rw [hs]
      field_simp
      rfl
    _ = K*(∫ t : ℝ in Ioi 0, ((1/2)*t^(-(1/2 : ℝ))) * g (K*Real.sqrt t)) := by rw [hr]
    _ = ∫ t : ℝ in Ioi 0, K*(((1/2)*t^(-(1/2 : ℝ))) * g (K*Real.sqrt t)) :=
      (integral_const_mul _ _).symm
    _ = ∫ t : ℝ in Ioi 0, K^(2*e)*scaledMomentIntegrand N h K e t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      simpa only [mul_assoc] using scaledMoment_pointwise N h e (K := K) ht
    _ = _ := integral_const_mul _ _

lemma scaledMomentIntegral_pos (N h e : ℕ) {K : ℝ} (hK : 0 < K) :
    0 < ∫ t : ℝ in Ioi 0, scaledMomentIntegrand N h K e t := by
  have hp := rationalMomentIntegral_pos N h e
  rw [rationalMomentIntegral_scaled N h e hK] at hp
  exact pos_of_mul_pos_right hp (pow_pos hK _).le

lemma scaledMomentIntegrand_integrable (N h e : ℕ) {K : ℝ} (hK : 0 < K) :
    IntegrableOn (scaledMomentIntegrand N h K e) (Ioi 0) :=
  Integrable.of_integral_ne_zero (ne_of_gt (scaledMomentIntegral_pos N h e hK))

def scaledHankelMatrix (N h : ℕ) (K : ℝ) : Matrix (Fin h) (Fin h) ℝ :=
  fun i j => ∫ t : ℝ in Ioi 0, scaledMomentIntegrand N h K (i.val+j.val) t

lemma realHankelMatrix_scaled (N h : ℕ) {K : ℝ} (hK : 0 < K) :
    realHankelMatrix N h =
      diagonal (fun i : Fin h => K^(2*i.val)) * scaledHankelMatrix N h K *
        diagonal (fun i : Fin h => K^(2*i.val)) := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, realHankelMatrix_entry,
    rationalMomentIntegral_scaled N h _ hK]
  unfold scaledHankelMatrix
  rw [Nat.mul_add, pow_add]
  ring

lemma realHankelMatrix_det_scaled (N h : ℕ) {K : ℝ} (hK : 0 < K) :
    (realHankelMatrix N h).det =
      (∏ i : Fin h, K^(2*i.val))^2 * (scaledHankelMatrix N h K).det := by
  rw [realHankelMatrix_scaled N h hK, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_diagonal]
  ring

lemma sum_fin_twice (h : ℕ) : (∑ i : Fin h, 2*i.val) = h*(h-1) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih, Nat.succ_sub_one]
    cases h with
    | zero => norm_num
    | succ k => simp only [Nat.succ_sub_one]; ring

lemma scaleDiagonal_product_sq (h : ℕ) (K : ℝ) :
    (∏ i : Fin h, K^(2*i.val))^2 = K^(2*h*(h-1)) := by
  rw [Finset.prod_pow_eq_pow_sum, sum_fin_twice, ← pow_mul]
  congr 1
  ring

lemma realHankelMatrix_det_scaled_power (N h : ℕ) {K : ℝ} (hK : 0 < K) :
    (realHankelMatrix N h).det =
      K^(2*h*(h-1)) * (scaledHankelMatrix N h K).det := by
  rw [realHankelMatrix_det_scaled N h hK, scaleDiagonal_product_sq]

/-- Monomials in the new variable t. -/
def scaledGramFunctions (h : ℕ) (i : Fin h) (t : ℝ) : ℝ := t^i.val

def weightedScaledGramFunctions (N h : ℕ) (K : ℝ) (i : Fin h) (t : ℝ) : ℝ :=
  scaledGramFunctions h i t * scaledGramWeight N h K t

lemma scaledGramFunctions_pair_eq (N h : ℕ) (K : ℝ) (i j : Fin h) (t : ℝ) :
    scaledGramFunctions h i t*weightedScaledGramFunctions N h K j t =
      scaledMomentIntegrand N h K (i.val+j.val) t := by
  unfold weightedScaledGramFunctions scaledGramFunctions scaledMomentIntegrand
  rw [pow_add]
  ring

lemma scaledGramFunctions_pair_integrable (N h : ℕ) {K : ℝ} (hK : 0 < K) (i j : Fin h) :
    IntegrableOn (fun t => scaledGramFunctions h i t*weightedScaledGramFunctions N h K j t)
      (Ioi 0) := by
  simp_rw [scaledGramFunctions_pair_eq]
  exact scaledMomentIntegrand_integrable N h _ hK

lemma scaledGramMomentMatrix_eq (N h : ℕ) (K : ℝ) :
    Zeta5Andreief.momentMatrix (volume.restrict (Ioi 0))
      (scaledGramFunctions h) (weightedScaledGramFunctions N h K) = scaledHankelMatrix N h K := by
  ext i j
  simp only [Zeta5Andreief.momentMatrix, scaledGramFunctions_pair_eq, scaledHankelMatrix]

lemma scaledGramEvaluationMatrix_eq (h : ℕ) (t : Fin h → ℝ) :
    Zeta5Andreief.evaluationMatrix (scaledGramFunctions h) t =
      (Matrix.vandermonde t)ᵀ := by
  ext i j
  rfl

lemma weightedScaledGramEvaluationMatrix_det (N h : ℕ) (K : ℝ) (t : Fin h → ℝ) :
    (Zeta5Andreief.evaluationMatrix (weightedScaledGramFunctions N h K) t).det =
      (∏ i : Fin h, scaledGramWeight N h K (t i)) *
        (Zeta5Andreief.evaluationMatrix (scaledGramFunctions h) t).det := by
  have he : Zeta5Andreief.evaluationMatrix (weightedScaledGramFunctions N h K) t =
      Matrix.of (fun i j => scaledGramWeight N h K (t j) *
        Zeta5Andreief.evaluationMatrix (scaledGramFunctions h) t i j) := by
    ext i j
    simp only [Zeta5Andreief.evaluationMatrix, weightedScaledGramFunctions, Matrix.of_apply]
    ring
  rw [he, Matrix.det_mul_row]

/-- Vandermonde square in the scaled variables t_i. -/
def scaledVandermondeSquare (h : ℕ) (t : Fin h → ℝ) : ℝ :=
  ∏ i : Fin h, ∏ j ∈ Finset.Ioi i, (t i-t j)^2

lemma scaledVandermonde_det_sq (h : ℕ) (t : Fin h → ℝ) :
    (Matrix.vandermonde t).det^2 = scaledVandermondeSquare h t := by
  rw [Matrix.det_vandermonde]
  simp only [← Finset.prod_pow]
  unfold scaledVandermondeSquare
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro j hj
  ring

def scaledGramIntegrand (N h : ℕ) (K : ℝ) (t : Fin h → ℝ) : ℝ :=
  scaledVandermondeSquare h t * ∏ i : Fin h, scaledGramWeight N h K (t i)

lemma scaledGramDeterminantProduct_eq (N h : ℕ) (K : ℝ) (t : Fin h → ℝ) :
    (Zeta5Andreief.evaluationMatrix (scaledGramFunctions h) t).det *
      (Zeta5Andreief.evaluationMatrix (weightedScaledGramFunctions N h K) t).det =
        scaledGramIntegrand N h K t := by
  rw [weightedScaledGramEvaluationMatrix_det, scaledGramEvaluationMatrix_eq, Matrix.det_transpose]
  unfold scaledGramIntegrand
  rw [← scaledVandermonde_det_sq]
  ring

theorem scaledGramIntegrand_integrable (N h : ℕ) {K : ℝ} (hK : 0 < K) :
    Integrable (scaledGramIntegrand N h K)
      (Measure.pi (fun _ : Fin h => volume.restrict (Ioi (0 : ℝ)))) := by
  have hh := Zeta5Andreief.determinant_product_integrable
    (volume.restrict (Ioi 0)) (scaledGramFunctions h) (weightedScaledGramFunctions N h K)
    (scaledGramFunctions_pair_integrable N h hK)
  apply hh.congr
  filter_upwards with t
  exact scaledGramDeterminantProduct_eq N h K t

lemma scaledGramIntegral_eq_factorial_det (N h : ℕ) {K : ℝ} (hK : 0 < K) :
    (∫ t : Fin h → ℝ, scaledGramIntegrand N h K t
      ∂Measure.pi (fun _ : Fin h => volume.restrict (Ioi (0 : ℝ)))) =
        (Nat.factorial h : ℝ) * (scaledHankelMatrix N h K).det := by
  have hh := Zeta5Andreief.andreief
    (volume.restrict (Ioi 0)) (scaledGramFunctions h) (weightedScaledGramFunctions N h K)
    (scaledGramFunctions_pair_integrable N h hK)
  simpa only [scaledGramDeterminantProduct_eq, scaledGramMomentMatrix_eq] using hh

/-- Exact scaling y_i=K√t_i, including the Vandermonde exponent and the
Jacobian. This is the integral to which the real-energy estimates apply. -/
theorem determinant_eq_scaledGramIntegral (N h : ℕ) {K : ℝ} (hK : 0 < K) :
    (determinant N h).eval₂ (Rat.castHom ℝ) zetaSeries =
      K^(2*h*(h-1))/(Nat.factorial h : ℝ) *
        (∫ t : Fin h → ℝ, scaledGramIntegrand N h K t
          ∂Measure.pi (fun _ : Fin h => volume.restrict (Ioi (0 : ℝ)))) := by
  have he := (Polynomial.eval₂RingHom (Rat.castHom ℝ) zetaSeries).map_det
    (hankelMatrix N h)
  change (determinant N h).eval₂ (Rat.castHom ℝ) zetaSeries =
    (realHankelMatrix N h).det at he
  rw [he, scaledGramIntegral_eq_factorial_det N h hK,
    realHankelMatrix_det_scaled_power N h hK]
  have hf : (Nat.factorial h : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero h
  field_simp

#print axioms determinant_eq_scaledGramIntegral

end Zeta5Construction
