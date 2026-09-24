import InnerRealKernel
import NormalizationTail

noncomputable section
namespace Zeta5RealKernel
open MeasureTheory Set

def tailMajorant (x : ℝ) : ℝ := x*linearPart x+13/8

theorem remainder_integrableOn (a b : ℝ) : IntegrableOn remainder (Icc a b) := by
  apply Measure.integrableOn_of_bounded (M:=2) (measure_Icc_lt_top.ne)
    measurable_remainder.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> linarith [(remainder_bounds x).1,(remainder_bounds x).2]

theorem tailMajorant_integrableOn (a b : ℝ) : IntegrableOn tailMajorant (Icc a b) := by
  have he : tailMajorant=(fun x => kernel x-remainder x+(13/8:ℝ)) := by
    funext x
    rw [kernel_decomposition]
    unfold tailMajorant
    ring
  rw [he]
  exact ((kernel_integrableOn a b).sub (remainder_integrableOn a b)).add
    (integrableOn_const measure_Icc_lt_top.ne)

theorem tailMajorant_div_cube_integrableOn (a b : ℝ) (ha : 0<a) :
    IntegrableOn (fun x => tailMajorant x/x^3) (Icc a b) := by
  have hc : ContinuousOn (fun x : ℝ => (x^3)⁻¹) (Icc a b) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx
    exact pow_ne_zero _ (ne_of_gt (ha.trans_le hx.1))
  simpa only [div_eq_mul_inv] using (tailMajorant_integrableOn a b).mul_continuousOn hc isCompact_Icc

theorem tailMajorant_tail_upper :
    (∫ x in (20:ℝ)..100000, tailMajorant x/x^3) ≤ -(6970198065777/125000000000000) := by
  apply Zeta5NormalizationTail.tail_integral_bound_100000
    (tailMajorant_div_cube_integrableOn _ _ (by norm_num))
  intro x hx
  rfl

theorem kernel_tail_upper :
    (∫ x in (20:ℝ)..100000, kernel x/x^3) ≤ -(6970198065777/125000000000000) := by
  apply Zeta5NormalizationTail.tail_integral_bound_100000
    (kernel_div_cube_integrableOn _ _ (by norm_num))
  intro x hx
  rw [kernel_decomposition]
  have hf : linearPart x=Zeta5NormalizationTail.F x := rfl
  rw [hf]
  exact add_le_add_right (remainder_bounds x).2 _

#print axioms kernel_tail_upper
end Zeta5RealKernel
