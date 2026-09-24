import DenominatorRiemann

noncomputable section
open MeasureTheory Set

namespace Zeta5Construction

/-- The external field of (6.1), with the ratio α left variable. -/
def externalField (α t : ℝ) : ℝ :=
  2*Real.pi*Real.sqrt t + (∫ u in (0:ℝ)..1, Real.log (t+u^2)) -
    6*(∫ u in (0:ℝ)..α, Real.log (t+u^2))

lemma logQuadratic_antiderivative {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun u : ℝ => u*Real.log (t+u^2)-2*u+
      2*Real.sqrt t*Real.arctan (u/Real.sqrt t)) (Real.log (t+x^2)) x := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hq : t+x^2 ≠ 0 := ne_of_gt (by positivity)
  have h1 := (hasDerivAt_id x).mul
    (((hasDerivAt_id x).pow 2).const_add t |>.log hq)
  have h2 := (hasDerivAt_id x).const_mul 2
  have h3 := ((hasDerivAt_id x).div_const (Real.sqrt t)).arctan.const_mul (2*Real.sqrt t)
  apply ((h1.sub h2).add h3).congr_deriv
  simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, one_mul, mul_one]
  have ha : 1+(x/Real.sqrt t)^2 ≠ 0 := by positivity
  field_simp
  nlinarith [Real.sq_sqrt ht.le]

theorem integral_logQuadratic {t : ℝ} (ht : 0 < t) (b : ℝ) :
    (∫ u in (0:ℝ)..b, Real.log (t+u^2)) =
      b*Real.log (t+b^2)-2*b+2*Real.sqrt t*Real.arctan (b/Real.sqrt t) := by
  have hi : IntervalIntegrable (fun u : ℝ => Real.log (t+u^2)) volume 0 b := by
    have hc : Continuous (fun u : ℝ => Real.log (t+u^2)) := by
      apply Continuous.log (by fun_prop)
      intro u
      exact ne_of_gt (by positivity)
    exact hc.intervalIntegrable 0 b
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => logQuadratic_antiderivative ht x) hi
  simpa using he

theorem externalField_eq_explicit (α : ℝ) {t : ℝ} (ht : 0 < t) :
    externalField α t =
      Real.log (1+t)-6*α*Real.log (t+α^2)-2+12*α +
        2*Real.sqrt t*(Real.pi+Real.arctan (1/Real.sqrt t)-
          6*Real.arctan (α/Real.sqrt t)) := by
  unfold externalField
  rw [integral_logQuadratic ht 1, integral_logQuadratic ht α]
  norm_num only [one_pow, one_mul]
  rw [add_comm t 1]
  ring

/-- The elementary external-field lower bound used on t≥2. -/
theorem externalField_lower {α t : ℝ} (hα : 0 ≤ α) (ht : 0 < t) :
    2*Real.pi*Real.sqrt t+(1-6*α)*Real.log t-6*α^3/t ≤ externalField α t := by
  have hc : Continuous (fun u : ℝ => Real.log (t+u^2)) := by
    apply Continuous.log (by fun_prop)
    intro u
    exact ne_of_gt (by positivity)
  have hlow := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ)≤1)
    (intervalIntegrable_const (c := Real.log t)) (hc.intervalIntegrable (μ := volume) 0 1)
    (fun u hu => Real.log_le_log ht (by nlinarith [sq_nonneg u]))
  have hupper := intervalIntegral.integral_mono_on hα (hc.intervalIntegrable (μ := volume) 0 α)
    (intervalIntegrable_const (c := Real.log t+α^2/t))
    (fun u hu => by
      have ha := Real.log_le_sub_one_of_pos (div_pos (by positivity : 0<t+u^2) ht)
      rw [Real.log_div (by positivity) ht.ne'] at ha
      have he : (t+u^2)/t-1=u^2/t := by field_simp; ring
      rw [he] at ha
      have hb : u^2/t ≤ α^2/t := by
        apply div_le_div_of_nonneg_right _ ht.le
        nlinarith [hu.1, hu.2]
      linarith)
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul] at hlow hupper
  unfold externalField
  have he : α*(Real.log t+α^2/t)=α*Real.log t+α^3/t := by ring
  rw [he] at hupper
  calc
    _ = 2*Real.pi*Real.sqrt t+Real.log t-6*(α*Real.log t+α^3/t) := by ring
    _ ≤ _ := sub_le_sub (add_le_add le_rfl hlow)
      (mul_le_mul_of_nonneg_left hupper (by norm_num))

#print axioms externalField_eq_explicit
#print axioms externalField_lower

end Zeta5Construction
