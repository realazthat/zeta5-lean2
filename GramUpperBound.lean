import ScaledWeightBounds
import ResidualIntegral

noncomputable section
open scoped BigOperators
open MeasureTheory Set Matrix

namespace Zeta5Construction

lemma scaledVandermondeSquare_pos {h : ℕ} {t : Fin h → ℝ} (ht : Function.Injective t) :
    0 < scaledVandermondeSquare h t := by
  rw [← scaledVandermonde_det_sq]
  exact sq_pos_of_ne_zero (Matrix.det_vandermonde_ne_zero_iff.mpr ht)

lemma log_scaledVandermondeSquare {h : ℕ} {t : Fin h → ℝ} (ht : Function.Injective t) :
    Real.log (scaledVandermondeSquare h t) =
      2*∑ i : Fin h, ∑ j ∈ Finset.Ioi i, Real.log |t i-t j| := by
  have hn (i j : Fin h) (hij : j ∈ Finset.Ioi i) : t i-t j ≠ 0 := by
    intro he
    exact (Finset.mem_Ioi.mp hij).ne (ht (sub_eq_zero.mp he))
  unfold scaledVandermondeSquare
  rw [Real.log_prod (fun i hi => Finset.prod_ne_zero_iff.mpr
    (fun j hj => pow_ne_zero _ (hn i j hj)))]
  simp_rw [Real.log_prod (fun j hj => pow_ne_zero 2 (hn _ j hj)), Real.log_pow, Real.log_abs]
  norm_num only [Nat.cast_ofNat]
  simp only [← Finset.mul_sum]

lemma log_residualWeight {t : ℝ} (ht : 0 < t) :
    Real.log (residualWeight t) =
      -(1/2:ℝ)*Real.log t+5*Real.log (1+Real.sqrt t)-Real.sqrt t := by
  unfold residualWeight
  simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_pow, Real.log_exp]
  ring

lemma scaledGramIntegrand_eq_zero_of_not_injective (N h : ℕ) (K : ℝ) {t : Fin h → ℝ}
    (ht : ¬ Function.Injective t) : scaledGramIntegrand N h K t = 0 := by
  have hv : (Matrix.vandermonde t).det = 0 := by
    by_contra hn
    exact ht (Matrix.det_vandermonde_ne_zero_iff.mp hn)
  unfold scaledGramIntegrand
  rw [← scaledVandermonde_det_sq, hv]
  simp

def gramExponentConstant (N h : ℕ) (K B : ℝ) : ℝ :=
  h*Real.log 4096+12*h+h*(12*N-2*K+18)*Real.log K+B

/-- Pointwise conversion of the discrete energy bound to an integrable majorant. -/
theorem scaledGramIntegrand_upper {N h : ℕ} {K B : ℝ} {t : Fin h → ℝ}
    (hN : 0 < N) (hh : 0 < h) (hK : K=(N+h:ℕ)) (ht : ∀ i, 0 < t i)
    (henergy : Function.Injective t →
      2*∑ i : Fin h, ∑ j ∈ Finset.Ioi i, Real.log |t i-t j| -
        K*∑ i, externalField ((N:ℝ)/K) (t i)+∑ i, Real.sqrt (t i) ≤ B) :
    scaledGramIntegrand N h K t ≤
      Real.exp (gramExponentConstant N h K B) * ∏ i, residualWeight (t i) := by
  have hKp : 0 < K := by rw [hK]; positivity
  have hr : 0 < ∏ i, residualWeight (t i) := Finset.prod_pos (fun i hi => residualWeight_pos (ht i))
  by_cases hinj : Function.Injective t
  · have hg : 0 < scaledGramIntegrand N h K t :=
      mul_pos (scaledVandermondeSquare_pos hinj)
        (Finset.prod_pos (fun i hi => scaledGramWeight_pos N h hKp (ht i)))
    apply (Real.log_le_log_iff hg (mul_pos (Real.exp_pos _) hr)).mp
    rw [scaledGramIntegrand, Real.log_mul (scaledVandermondeSquare_pos hinj).ne'
      (ne_of_gt (Finset.prod_pos (fun i hi => scaledGramWeight_pos N h hKp (ht i)))),
      log_scaledVandermondeSquare hinj,
      Real.log_prod (fun i hi => (scaledGramWeight_pos N h hKp (ht i)).ne'),
      Real.log_mul (Real.exp_pos _).ne' hr.ne', Real.log_exp,
      Real.log_prod (fun i hi => (residualWeight_pos (ht i)).ne')]
    simp only [log_residualWeight (ht _)]
    have hs := Finset.sum_le_sum (s := Finset.univ)
      (fun i hi => log_scaledGramWeight_upper hN hh hK (ht i))
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum] at hs ⊢
    unfold gramExponentConstant
    have he := henergy hinj
    nlinarith
  · rw [scaledGramIntegrand_eq_zero_of_not_injective N h K hinj]
    positivity

/-- Integration of the energy majorant, using the exact residual integral 652. -/
theorem scaledGramIntegral_upper {N h : ℕ} {K B : ℝ}
    (hN : 0 < N) (hh : 0 < h) (hK : K=(N+h:ℕ))
    (henergy : ∀ t : Fin h → ℝ, (∀ i, 0 < t i) → Function.Injective t →
      2*∑ i : Fin h, ∑ j ∈ Finset.Ioi i, Real.log |t i-t j| -
        K*∑ i, externalField ((N:ℝ)/K) (t i)+∑ i, Real.sqrt (t i) ≤ B) :
    (∫ t : Fin h → ℝ, scaledGramIntegrand N h K t
      ∂Measure.pi (fun _ => volume.restrict (Ioi (0:ℝ)))) ≤
        Real.exp (gramExponentConstant N h K B)*652^h := by
  have hKp : 0 < K := by rw [hK]; positivity
  have hae : ∀ᵐ t : Fin h → ℝ ∂Measure.pi (fun _ => volume.restrict (Ioi (0:ℝ))),
      ∀ i, 0 < t i := by
    apply Filter.eventually_all.mpr
    intro i
    exact Measure.tendsto_eval_ae_ae.eventually (ae_restrict_mem measurableSet_Ioi)
  have hi := integral_mono_ae (scaledGramIntegrand_integrable N h hKp)
    ((residualProduct_integrable h).const_mul (Real.exp (gramExponentConstant N h K B)))
    (hae.mono (fun t ht => scaledGramIntegrand_upper hN hh hK ht (henergy t ht)))
  rw [integral_const_mul, residualProduct_integral] at hi
  exact hi

/-- The complete logarithmic determinant bound obtained from a discrete energy estimate. -/
theorem log_determinant_upper_of_energy {N h : ℕ} {K B : ℝ}
    (hN : 0 < N) (hh : 0 < h) (hK : K=(N+h:ℕ))
    (henergy : ∀ t : Fin h → ℝ, (∀ i, 0 < t i) → Function.Injective t →
      2*∑ i : Fin h, ∑ j ∈ Finset.Ioi i, Real.log |t i-t j| -
        K*∑ i, externalField ((N:ℝ)/K) (t i)+∑ i, Real.sqrt (t i) ≤ B) :
    Real.log ((determinant N h).eval₂ (Rat.castHom ℝ) zetaSeries) ≤
      2*h*(h+6*N-K)*Real.log K+B+16*h*Real.log K+
        h*(Real.log 4096+12+Real.log 652) := by
  have hKp : 0 < K := by rw [hK]; positivity
  have hi := scaledGramIntegral_upper hN hh hK henergy
  have hd : (determinant N h).eval₂ (Rat.castHom ℝ) zetaSeries ≤
      K^(2*h*(h-1))/(h.factorial:ℝ)*
        (Real.exp (gramExponentConstant N h K B)*652^h) := by
    rw [determinant_eq_scaledGramIntegral N h hKp]
    exact mul_le_mul_of_nonneg_left hi (by positivity)
  have hl := Real.log_le_log (determinant_eval_pos N h) hd
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_exp] at hl
  have hf : 0 ≤ Real.log (h.factorial:ℝ) := Real.log_nonneg (by
    exact_mod_cast Nat.factorial_pos h)
  have hpred : ((h-1:ℕ):ℝ)=h-1 := by rw [Nat.cast_sub hh, Nat.cast_one]
  push_cast at hl
  rw [hpred] at hl
  unfold gramExponentConstant at hl
  nlinarith only [hl, hf]

/-- The normalized determinant estimate, including cancellation of K² log K. -/
theorem log_normalizedDeterminant_upper_of_energy {N h : ℕ} {α lam K B : ℝ}
    (hN : 0 < N) (hh : 0 < h) (hK : K=(N+h:ℕ))
    (hα : 0 < α) (hlam : 0 < lam) (hs : α+lam=1)
    (hNr : (N:ℝ)=α*K) (hhr : (h:ℝ)=lam*K)
    (henergy : ∀ t : Fin h → ℝ, (∀ i, 0 < t i) → Function.Injective t →
      2*∑ i : Fin h, ∑ j ∈ Finset.Ioi i, Real.log |t i-t j| -
        K*∑ i, externalField ((N:ℝ)/K) (t i)+∑ i, Real.sqrt (t i) ≤ B) :
    Real.log ((normalizedDeterminant N h).eval₂ (Rat.castHom ℝ) zetaSeries) ≤
      normalizationConstant α lam*K^2+B+22*h*Real.log K+
        h*(Real.log 4096+18+Real.log 652) := by
  have hKp : 0 < K := by rw [hK]; positivity
  have hd := log_determinant_upper_of_energy hN hh hK henergy
  have hn := log_normalizedDeterminant_upper (E := 0)
    (R := B+16*h*Real.log K+h*(Real.log 4096+12+Real.log 652))
    hN hh hα hlam hKp hs hNr hhr (by simpa only [zero_mul, add_zero, add_assoc] using hd)
  nlinarith only [hn]

#print axioms log_determinant_upper_of_energy
#print axioms log_normalizedDeterminant_upper_of_energy

end Zeta5Construction

