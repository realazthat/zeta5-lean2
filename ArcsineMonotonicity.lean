import ArcsineMixture

namespace Zeta5CirclePotential
open MeasureTheory Real Metric Set

 theorem arcsine_potential_lower (a b t : ℝ) (hab : a < b) :
    Real.log ((b-a)/4) ≤ arcsinePotential a b t := by
  have hr : 0 < (b-a)/2 := by linarith
  rw [arcsine_potential_scaling a b t hab, normalized_arcsine_potential_closedform]
  calc
    _ = Real.log ((b-a)/2)+Real.log (1/2 : ℝ) := by
      rw [← Real.log_mul (ne_of_gt hr) (by norm_num : (1/2 : ℝ) ≠ 0)]
      congr 1
      ring
    _ ≤ _ := by
      apply add_le_add le_rfl
      apply Real.log_le_log (by norm_num)
      have hm : 1 ≤ max 1 |(t-(a+b)/2)/((b-a)/2)| := le_max_left _ _
      have hs := Real.sqrt_nonneg (((t-(a+b)/2)/((b-a)/2))^2-1)
      linarith

 theorem arcsine_potential_monotone_right (a b q : ℝ) (hab : a < b)
    (hq : a ≤ q ∧ q ≤ b) : MonotoneOn (arcsinePotential a b) (Ici q) := by
  intro t ht u hu htu
  have hqt : q ≤ t := ht
  have hqu : q ≤ u := hu
  by_cases htb : t ≤ b
  · rw [arcsine_potential_inside a b t hab ⟨hq.1.trans hqt,htb⟩]
    exact arcsine_potential_lower a b u hab
  · have hbt : b < t := lt_of_not_ge htb
    have hbu : b < u := hbt.trans_le htu
    rw [arcsine_potential_outside a b t hab (Or.inr hbt),
      arcsine_potential_outside a b u hab (Or.inr hbu),
      abs_of_pos (by linarith : 0 < t-(a+b)/2),
      abs_of_pos (by linarith : 0 < u-(a+b)/2)]
    apply Real.log_le_log (by have hs := Real.sqrt_nonneg ((t-a)*(t-b)); linarith)
    have hs : Real.sqrt ((t-a)*(t-b)) ≤ Real.sqrt ((u-a)*(u-b)) := by
      apply Real.sqrt_le_sqrt
      exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    linarith

 theorem arcsine_potential_antitone_left (a b q : ℝ) (hab : a < b)
    (hq : a ≤ q ∧ q ≤ b) : AntitoneOn (arcsinePotential a b) (Iic q) := by
  intro t ht u hu htu
  have htq : t ≤ q := ht
  have huq : u ≤ q := hu
  by_cases hau : a ≤ u
  · rw [arcsine_potential_inside a b u hab ⟨hau,huq.trans hq.2⟩]
    exact arcsine_potential_lower a b t hab
  · have hua : u < a := lt_of_not_ge hau
    have hta : t < a := htu.trans_lt hua
    rw [arcsine_potential_outside a b t hab (Or.inl hta),
      arcsine_potential_outside a b u hab (Or.inl hua),
      abs_of_neg (by linarith : u-(a+b)/2 < 0),
      abs_of_neg (by linarith : t-(a+b)/2 < 0)]
    apply Real.log_le_log (by have hs := Real.sqrt_nonneg ((u-a)*(u-b)); linarith)
    have hp (x : ℝ) : (x-a)*(x-b)=(a-x)*(b-x) := by ring
    have hs : Real.sqrt ((u-a)*(u-b)) ≤ Real.sqrt ((t-a)*(t-b)) := by
      rw [hp u,hp t]
      apply Real.sqrt_le_sqrt
      exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    linarith

end Zeta5CirclePotential

namespace Zeta5ArcsineMixture
open MeasureTheory Real Metric Set Zeta5CirclePotential

noncomputable def commonCenter : ℝ := (left 0+right 0)/2

 theorem commonCenter_mem (i : Component) : left i ≤ commonCenter ∧ commonCenter ≤ right i := by
  have hn := data_nested 0 i (Fin.zero_le i)
  have hp := (data_properties 0).2.1
  unfold commonCenter
  constructor <;> linarith [hn.1,hn.2]

 theorem potential_monotone_right : MonotoneOn potential (Ici commonCenter) := by
  intro t ht u hu htu
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left
    (arcsine_potential_monotone_right _ _ _ (data_properties i).2.1 (commonCenter_mem i) ht hu htu)
    (data_properties i).2.2.2.le

 theorem potential_antitone_left : AntitoneOn potential (Iic commonCenter) := by
  intro t ht u hu htu
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left
    (arcsine_potential_antitone_left _ _ _ (data_properties i).2.1 (commonCenter_mem i) ht hu htu)
    (data_properties i).2.2.2.le

/-- A grid cell's endpoint maximum bounds the complete nested-mixture potential. -/
 theorem potential_cell_max (l t r : ℝ) (hlt : l ≤ t) (htr : t ≤ r) :
    potential t ≤ max (potential l) (potential r) := by
  rcases le_total t commonCenter with ht | ht
  · exact (potential_antitone_left (hlt.trans ht) ht hlt).trans (le_max_left _ _)
  · exact (potential_monotone_right ht (ht.trans htr) htr).trans (le_max_right _ _)

 theorem potential_tail_upper (t : ℝ) (ht : 2 ≤ t) :
    potential t ≤ (37/40 : ℝ)*Real.log t := by
  have ht0 : 0 < t := by linarith
  have hc (i : Component) : arcsinePotential (left i) (right i) t ≤ Real.log t := by
    rw [← Zeta5CircleMeasures.arcsine_real_log_integral]
    calc
      _ ≤ ∫ _z : ℂ, Real.log t ∂Zeta5CircleMeasures.arcsineMeasure (left i) (right i) := by
        apply integral_mono_ae
          (Zeta5CircleMeasures.arcsine_real_log_integrable _ _ t (data_properties i).2.1)
          (integrable_const _)
        filter_upwards [Zeta5CircleMeasures.arcsineMeasure_ae_interval
          (left i) (right i) (data_properties i).2.1.le] with z hz
        rw [Zeta5CircleMeasures.complex_eq_real_of_im_zero z hz.1,← Complex.ofReal_sub,
          Complex.norm_real,Real.norm_eq_abs]
        have hzt : 0 < t-z.re := by linarith [(data_properties i).2.2.1,hz.2.2]
        rw [abs_of_pos hzt]
        apply Real.log_le_log hzt
        have hz0 : 0 ≤ z.re := (data_properties i).1.le.trans hz.2.1
        linarith
      _ = _ := by simp
  calc
    _ ≤ ∑ i, mass i*Real.log t := Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (hc i) (data_properties i).2.2.2.le)
    _ = _ := by rw [← Finset.sum_mul,mass_sum]

#print axioms potential_tail_upper
#print axioms potential_cell_max
end Zeta5ArcsineMixture
