import Moments
import Mathlib.MeasureTheory.Integral.Pi

noncomputable section
open scoped BigOperators
open MeasureTheory Set

namespace Zeta5Construction

def residualWeight (t : ℝ) : ℝ :=
  t^(-(1/2:ℝ))*(1+Real.sqrt t)^5*Real.exp (-Real.sqrt t)

lemma residualWeight_pos {t : ℝ} (ht : 0 < t) : 0 < residualWeight t := by
  unfold residualWeight
  positivity

lemma residualWeight_integral : (∫ t : ℝ in Ioi 0, residualWeight t) = 652 := by
  let g : ℝ → ℝ := fun y => 2*(1+y)^5*Real.exp (-y)
  have hg : g = fun y : ℝ => ∑ e ∈ Finset.range 6,
      2*(Nat.choose 5 e : ℝ)*(y^e*Real.exp (-y)) := by
    funext y
    dsimp [g]
    norm_num [Finset.sum_range_succ, Nat.choose]
    ring
  have he : ∀ e, IntegrableOn (fun y : ℝ => y^e*Real.exp (-y)) (Ioi 0) := by
    intro e
    simpa only [one_mul] using power_exp_integrable e (r := 1) (by norm_num)
  have hi : (∫ y : ℝ in Ioi 0, g y) = 326*2 := by
    rw [hg, integral_finsetSum]
    · simp only [integral_const_mul]
      have hv (e : ℕ) : (∫ y : ℝ in Ioi 0, y^e*Real.exp (-y)) = (e.factorial:ℝ) := by
        simpa using power_exp_integral e (r := 1) (by norm_num)
      simp only [hv]
      norm_num [Finset.sum_range_succ, Nat.choose]
    · intro e he'
      exact (he e).const_mul _
  have hs := integral_comp_rpow_Ioi g (p := (1/2:ℝ)) (by norm_num)
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<1/2)] at hs
  simp only [← Real.sqrt_eq_rpow, smul_eq_mul] at hs
  have hfun : (fun t : ℝ => (1/2)*t^(-(1/2:ℝ))*g (Real.sqrt t)) = residualWeight := by
    funext t
    dsimp [g, residualWeight]
    ring
  rw [hfun] at hs
  rw [hs, hi]
  norm_num

lemma residualWeight_integrable : IntegrableOn residualWeight (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [residualWeight_integral]
  norm_num

lemma residualProduct_integrable (h : ℕ) : Integrable
    (fun t : Fin h → ℝ => ∏ i, residualWeight (t i))
    (Measure.pi (fun _ => volume.restrict (Ioi 0))) := by
  exact Integrable.fintype_prod (fun i => residualWeight_integrable)

lemma residualProduct_integral (h : ℕ) :
    (∫ t : Fin h → ℝ, (∏ i, residualWeight (t i))
      ∂Measure.pi (fun _ => volume.restrict (Ioi 0))) = 652^h := by
  rw [integral_fintype_prod_eq_prod (fun _ => residualWeight)]
  simp [residualWeight_integral]

#print axioms residualProduct_integral

end Zeta5Construction
