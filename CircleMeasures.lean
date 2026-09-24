import CirclePotential
import Mathlib.MeasureTheory.Integral.Prod

/-! Actual probability measures underlying the circle and arcsine averages. -/
namespace Zeta5CircleMeasures
open MeasureTheory Real Metric Set
open Zeta5CirclePotential

noncomputable def angleMeasure : Measure ℝ :=
  ENNReal.ofReal ((2*Real.pi)⁻¹) • volume.restrict (Ioc 0 (2*Real.pi))

instance angleMeasure_probability : IsProbabilityMeasure angleMeasure := by
  constructor
  simp only [angleMeasure, Measure.smul_apply, Measure.restrict_apply_univ,
    Real.volume_Ioc, sub_zero, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ (by positivity)]
  simp

noncomputable def circleMeasure (c : ℂ) (R : ℝ) : Measure ℂ :=
  Measure.map (circleMap c R) angleMeasure

instance circleMeasure_probability (c : ℂ) (R : ℝ) :
    IsProbabilityMeasure (circleMeasure c R) := by
  unfold circleMeasure
  infer_instance

noncomputable def arcsineMap (a b : ℝ) (z : ℂ) : ℂ :=
  (((a+b)/2+(b-a)/2*z.re : ℝ) : ℂ)

noncomputable def arcsineMeasure (a b : ℝ) : Measure ℂ :=
  Measure.map (arcsineMap a b) (circleMeasure 0 1)

instance arcsineMeasure_probability (a b : ℝ) :
    IsProbabilityMeasure (arcsineMeasure a b) := by
  unfold arcsineMeasure
  infer_instance

theorem integral_circleMeasure (f : ℂ → ℝ) (hf : Measurable f) (c : ℂ) (R : ℝ) :
    (∫ z, f z ∂circleMeasure c R) = circleAverage f c R := by
  rw [circleMeasure, integral_map (by fun_prop) hf.aestronglyMeasurable]
  rw [angleMeasure, integral_smul_measure, ENNReal.toReal_ofReal (by positivity)]
  rw [circleAverage, intervalIntegral.integral_of_le (by positivity)]

 theorem integrable_circleMeasure_iff (f : ℂ → ℝ) (hf : Measurable f) (c : ℂ) (R : ℝ) :
    Integrable f (circleMeasure c R) ↔ CircleIntegrable f c R := by
  rw [circleMeasure, integrable_map_measure hf.aestronglyMeasurable (by fun_prop),
    angleMeasure, integrable_smul_measure (by positivity) ENNReal.ofReal_ne_top]
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).symm

 theorem integral_arcsineMeasure (f : ℂ → ℝ) (hf : Measurable f) (a b : ℝ) :
    (∫ z, f z ∂arcsineMeasure a b) =
      circleAverage (fun z => f (arcsineMap a b z)) 0 1 := by
  rw [arcsineMeasure, integral_map (by unfold arcsineMap; fun_prop) hf.aestronglyMeasurable]
  exact integral_circleMeasure _ (hf.comp (by unfold arcsineMap; fun_prop)) 0 1

 theorem circleMeasure_ae_mem_sphere (c : ℂ) (R : ℝ) :
    ∀ᵐ z ∂circleMeasure c R, z ∈ sphere c |R| := by
  unfold circleMeasure
  apply (ae_map_iff (by fun_prop) (show MeasurableSet {z : ℂ | z ∈ sphere c |R|} from isClosed_sphere.measurableSet)).2
  filter_upwards with θ
  exact circleMap_mem_sphere' c R θ

 theorem arcsineMeasure_ae_interval (a b : ℝ) (hab : a ≤ b) :
    ∀ᵐ z ∂arcsineMeasure a b, z.im = 0 ∧ a ≤ z.re ∧ z.re ≤ b := by
  rw [arcsineMeasure, ae_map_iff (by unfold arcsineMap; fun_prop)
    (by measurability)]
  filter_upwards [circleMeasure_ae_mem_sphere 0 1] with z hz
  have h := arcsine_point_mem_interval a b hab z hz
  simpa [arcsineMap] using h

 theorem circle_log_integrable (c w : ℂ) (R : ℝ) :
    Integrable (fun z => Real.log ‖z-w‖) (circleMeasure c R) := by
  apply (integrable_circleMeasure_iff _ (by fun_prop) c R).2
  exact circleIntegrable_log_norm_sub_const R

 theorem circle_log_integral (c w : ℂ) {R : ℝ} (hR : 0 < R) :
    (∫ z, Real.log ‖z-w‖ ∂circleMeasure c R) = Real.log (max ‖c-w‖ R) := by
  rw [integral_circleMeasure _ (by fun_prop), circle_average_log_distance c w hR]

 theorem arcsine_real_log_integrable (a b t : ℝ) (hab : a < b) :
    Integrable (fun z : ℂ => Real.log ‖(t : ℂ)-z‖) (arcsineMeasure a b) := by
  rw [arcsineMeasure, integrable_map_measure (Measurable.aestronglyMeasurable (by fun_prop)) (by unfold arcsineMap; fun_prop)]
  apply (integrable_circleMeasure_iff _ (by unfold arcsineMap; fun_prop) 0 1).2
  change CircleIntegrable (fun z : ℂ => Real.log ‖(t : ℂ)-arcsineMap a b z‖) 0 1
  simp only [arcsineMap, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact arcsine_log_circleIntegrable a b t hab

 theorem arcsine_real_log_integral (a b t : ℝ) :
    (∫ z : ℂ, Real.log ‖(t : ℂ)-z‖ ∂arcsineMeasure a b) = arcsinePotential a b t := by
  rw [integral_arcsineMeasure _ (by fun_prop)]
  simp only [arcsineMap, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    arcsinePotential]

theorem angleMeasure_ae_of_volume {p : ℝ → Prop} (h : ∀ᵐ θ : ℝ, p θ) :
    ∀ᵐ θ ∂angleMeasure, p θ :=
  Measure.ae_smul_measure (ae_restrict_of_ae h) _

open Filter in
 theorem circleMeasure_nullSingleton (c : ℂ) {R : ℝ} (hR : R ≠ 0) :
    NullSingletonClass (circleMeasure c R) := by
  constructor
  intro w
  have he : ∀ᵐ z ∂circleMeasure c R, z ≠ w := by
    unfold circleMeasure
    apply (ae_map_iff (by fun_prop) (by measurability)).2
    apply angleMeasure_ae_of_volume
    have hpre := circleMap_preimage_codiscrete (c := c) (R := R) hR
      (compl_singleton_mem_codiscreteWithin (s := sphere c |R|) w)
    have hae : ae (volume : Measure ℝ) ≤ codiscrete ℝ := by
      simpa [Filter.codiscrete] using
        (ae_restrict_le_codiscreteWithin (μ := (volume : Measure ℝ)) MeasurableSet.univ)
    filter_upwards [hae hpre] with θ hθ
    simpa only [mem_preimage, mem_compl_iff, mem_singleton_iff] using hθ
  simpa only [ae_iff, not_not, setOf_eq_eq_singleton] using he

 theorem arcsineMeasure_nullSingleton (a b : ℝ) (hab : a < b) :
    NullSingletonClass (arcsineMeasure a b) := by
  constructor
  intro w
  have he : ∀ᵐ z ∂arcsineMeasure a b, z ≠ w := by
    unfold arcsineMeasure circleMeasure
    rw [Measure.map_map (by unfold arcsineMap; fun_prop) (by fun_prop)]
    apply (ae_map_iff (by unfold arcsineMap; fun_prop) (by measurability)).2
    apply angleMeasure_ae_of_volume
    filter_upwards [arcsine_argument_ae_nonzero a b w.re hab] with θ hθ
    intro heq
    have hr := congrArg Complex.re heq
    apply hθ
    simpa [Function.comp_apply, arcsineMap] using sub_eq_zero.mpr hr.symm
  simpa only [ae_iff, not_not, setOf_eq_eq_singleton] using he

 theorem continuous_integrable_circle (f : ℂ → ℝ) (hf : Continuous f) (c : ℂ) (R : ℝ) :
    Integrable f (circleMeasure c R) :=
  (integrable_circleMeasure_iff f hf.measurable c R).2 hf.continuousOn.circleIntegrable'

 theorem continuous_integrable_arcsine (f : ℂ → ℝ) (hf : Continuous f) (a b : ℝ) :
    Integrable f (arcsineMeasure a b) := by
  rw [arcsineMeasure, integrable_map_measure hf.aestronglyMeasurable
    (by unfold arcsineMap; fun_prop)]
  apply continuous_integrable_circle
  unfold arcsineMap
  fun_prop

 theorem complex_eq_real_of_im_zero (z : ℂ) (hz : z.im = 0) : z = (z.re : ℂ) := by
  apply Complex.ext <;> simp [hz]

 theorem arcsine_real_norm_log_integral (a b t : ℝ) (hab : a < b)
    (ha : 0 ≤ a) (hb : b ≤ 1) (ht : 0 ≤ t ∧ t ≤ 1) :
    (∫ z : ℂ, ‖Real.log ‖(t : ℂ)-z‖‖ ∂arcsineMeasure a b) =
      -arcsinePotential a b t := by
  rw [← arcsine_real_log_integral a b t, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [arcsineMeasure_ae_interval a b hab.le] with z hz
  rw [complex_eq_real_of_im_zero z hz.1, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  apply abs_of_nonpos
  apply Real.log_nonpos (abs_nonneg _)
  apply abs_le.2
  constructor <;> linarith [hz.2.1,hz.2.2,ht.1,ht.2]

 theorem arcsine_arcsine_log_integrable (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (ha : 0 ≤ a) (hb : b ≤ 1) (hc : 0 ≤ c) (hd : d ≤ 1) :
    Integrable (fun p : ℂ × ℂ => Real.log ‖p.1-p.2‖)
      ((arcsineMeasure c d).prod (arcsineMeasure a b)) := by
  apply (integrable_prod_iff (Measurable.aestronglyMeasurable (by fun_prop))).2
  constructor
  · filter_upwards [arcsineMeasure_ae_interval c d hcd.le] with w hw
    rw [complex_eq_real_of_im_zero w hw.1]
    exact arcsine_real_log_integrable a b w.re hab
  · have hi := continuous_integrable_arcsine
      (fun w : ℂ => -arcsinePotential a b w.re)
      ((continuous_arcsine_potential a b hab).comp Complex.continuous_re).neg c d
    apply hi.congr
    filter_upwards [arcsineMeasure_ae_interval c d hcd.le] with w hw
    rw [complex_eq_real_of_im_zero w hw.1]
    exact (arcsine_real_norm_log_integral a b w.re hab ha hb
      ⟨hc.trans hw.2.1, hw.2.2.trans hd⟩).symm

 theorem nested_arcsine_energy (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (hac : a ≤ c) (hdb : d ≤ b) :
    (∫ w : ℂ, ∫ z : ℂ, Real.log ‖w-z‖ ∂arcsineMeasure a b ∂arcsineMeasure c d) =
      Real.log ((b-a)/4) := by
  calc
    _ = ∫ _w : ℂ, Real.log ((b-a)/4) ∂arcsineMeasure c d := by
      apply integral_congr_ae
      filter_upwards [arcsineMeasure_ae_interval c d hcd.le] with w hw
      rw [complex_eq_real_of_im_zero w hw.1, arcsine_real_log_integral]
      exact arcsine_potential_inside a b w.re hab ⟨hac.trans hw.2.1, hw.2.2.trans hdb⟩
    _ = _ := by simp

theorem circleMeasure_ae_norm_le (c : ℂ) (R : ℝ) :
    ∀ᵐ z ∂circleMeasure c R, ‖z‖ ≤ ‖c‖+|R| := by
  filter_upwards [circleMeasure_ae_mem_sphere c R] with z hz
  have hn : ‖z-c‖ = |R| := by simpa only [mem_sphere,dist_eq_norm] using hz
  calc
    ‖z‖ = ‖(z-c)+c‖ := by congr 1; ring
    _ ≤ ‖z-c‖+‖c‖ := norm_add_le _ _
    _ = _ := by rw [hn]; ring

 theorem arcsineMeasure_ae_norm_le_one (a b : ℝ) (hab : a ≤ b)
    (ha : 0 ≤ a) (hb : b ≤ 1) :
    ∀ᵐ z ∂arcsineMeasure a b, ‖z‖ ≤ 1 := by
  filter_upwards [arcsineMeasure_ae_interval a b hab] with z hz
  rw [complex_eq_real_of_im_zero z hz.1,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (ha.trans hz.2.1)]
  exact hz.2.2.trans hb

/-- Integrability of the logarithm against any bounded outer measure and one
circle follows from the explicit finite continuous circle potential. -/
 theorem measure_circle_log_integrable (μ : Measure ℂ) [IsFiniteMeasure μ]
    (c : ℂ) {R : ℝ} (hR : 0 < R) (B : ℝ)
    (hB : ∀ᵐ w ∂μ, ‖w‖ ≤ B)
    (hpotential : Integrable (fun w : ℂ => Real.log (max ‖c-w‖ R)) μ) :
    Integrable (fun p : ℂ × ℂ => Real.log ‖p.1-p.2‖)
      (μ.prod (circleMeasure c R)) := by
  have hmeas : AEStronglyMeasurable (fun p : ℂ × ℂ => Real.log ‖p.1-p.2‖)
      (μ.prod (circleMeasure c R)) := Measurable.aestronglyMeasurable (by fun_prop)
  have hinner (w : ℂ) : Integrable (fun z : ℂ => Real.log ‖w-z‖) (circleMeasure c R) := by
    simpa only [norm_sub_rev] using circle_log_integrable c w R
  apply (integrable_prod_iff hmeas).2
  constructor
  · exact Filter.Eventually.of_forall hinner
  · let C : ℝ := ‖c‖+|R|+B
    have hi : Integrable (fun w : ℂ => 2*C-Real.log (max ‖c-w‖ R)) μ :=
      (integrable_const (2*C)).sub hpotential
    apply hi.mono' hmeas.norm.integral_prod_right'
    filter_upwards [hB] with w hw
    rw [norm_of_nonneg (integral_nonneg (fun z => norm_nonneg _))]
    have hbound : (∫ z : ℂ, ‖Real.log ‖w-z‖‖ ∂circleMeasure c R) ≤
        ∫ z : ℂ, 2*C-Real.log ‖w-z‖ ∂circleMeasure c R := by
      apply integral_mono_ae (hinner w).norm ((integrable_const (2*C)).sub (hinner w))
      filter_upwards [circleMeasure_ae_norm_le c R] with z hz
      have hn : ‖w-z‖ ≤ C := (norm_sub_le w z).trans (by dsimp [C]; linarith)
      have hl : Real.log ‖w-z‖ ≤ C := (Real.log_le_self (norm_nonneg _)).trans hn
      change ‖Real.log ‖w-z‖‖ ≤ 2*C-Real.log ‖w-z‖
      rw [Real.norm_eq_abs]
      by_cases hlog : 0 ≤ Real.log ‖w-z‖
      · rw [abs_of_nonneg hlog]; linarith
      · rw [abs_of_nonpos (le_of_not_ge hlog)]
        have hC : 0 ≤ C := (norm_nonneg _).trans hn
        linarith
    calc
      _ ≤ _ := hbound
      _ = 2*C-Real.log (max ‖c-w‖ R) := by
        rw [integral_sub (integrable_const (2*C)) (hinner w)]
        simp only [integral_const, probReal_univ, one_smul]
        congr 1
        simpa only [norm_sub_rev] using circle_log_integral c w hR

 theorem circle_circle_log_integrable (c d : ℂ) {R : ℝ} (hR : 0 < R) (S : ℝ) :
    Integrable (fun p : ℂ × ℂ => Real.log ‖p.1-p.2‖)
      ((circleMeasure d S).prod (circleMeasure c R)) := by
  apply measure_circle_log_integrable (circleMeasure d S) c hR (‖d‖+|S|)
    (circleMeasure_ae_norm_le d S)
  apply continuous_integrable_circle
  apply Continuous.log
  · fun_prop
  · intro w
    exact ne_of_gt (hR.trans_le (le_max_right _ _))

 theorem arcsine_circle_log_integrable (a b : ℝ) (hab : a ≤ b)
    (ha : 0 ≤ a) (hb : b ≤ 1) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    Integrable (fun p : ℂ × ℂ => Real.log ‖p.1-p.2‖)
      ((arcsineMeasure a b).prod (circleMeasure c R)) := by
  apply measure_circle_log_integrable (arcsineMeasure a b) c hR 1
    (arcsineMeasure_ae_norm_le_one a b hab ha hb)
  apply continuous_integrable_arcsine
  apply Continuous.log
  · fun_prop
  · intro w
    exact ne_of_gt (hR.trans_le (le_max_right _ _))

theorem circle_arcsine_cross_energy (a b t : ℝ) {R : ℝ} (hR : 0 < R) :
    (∫ w : ℂ, ∫ z : ℂ, Real.log ‖w-z‖ ∂circleMeasure (t : ℂ) R
      ∂arcsineMeasure a b) = truncatedArcsinePotential a b R t := by
  have he : (fun w : ℂ => ∫ z : ℂ, Real.log ‖w-z‖ ∂circleMeasure (t : ℂ) R) =
      (fun w : ℂ => Real.log (max ‖(t : ℂ)-w‖ R)) := by
    funext w
    simpa only [norm_sub_rev] using circle_log_integral (t : ℂ) w hR
  rw [he, integral_arcsineMeasure _ (by fun_prop)]
  simp only [arcsineMap, ← Complex.ofReal_sub, Complex.norm_real,Real.norm_eq_abs,
    truncatedArcsinePotential]

 theorem circle_measure_self_energy (c : ℂ) {R : ℝ} (hR : 0 < R) :
    (∫ w : ℂ, ∫ z : ℂ, Real.log ‖z-w‖ ∂circleMeasure c R ∂circleMeasure c R) =
      Real.log R := by
  calc
    _ = ∫ _w : ℂ, Real.log R ∂circleMeasure c R := by
      apply integral_congr_ae
      filter_upwards [circleMeasure_ae_mem_sphere c R] with w hw
      rw [circle_log_integral c w hR]
      have hn : ‖c-w‖ = R := by
        simpa only [mem_sphere,dist_eq_norm,norm_sub_rev,abs_of_pos hR] using hw
      rw [hn,max_self]
    _ = _ := by simp

 theorem circle_measure_mutual_energy (c d : ℂ) {R : ℝ} (hR : 0 < R) (hcd : c ≠ d) :
    Real.log ‖c-d‖ ≤
      ∫ w : ℂ, ∫ z : ℂ, Real.log ‖z-w‖ ∂circleMeasure c R ∂circleMeasure d R := by
  have hi : Measurable (fun w : ℂ => Real.log (max ‖c-w‖ R)) := by fun_prop
  calc
    _ ≤ circleAverage (fun w : ℂ =>
        circleAverage (fun z : ℂ => Real.log ‖z-w‖) c R) d R :=
      mutual_circle_energy_ge_log_distance c d hR hcd
    _ = _ := by
      simp_rw [circle_average_log_distance c _ hR,circle_log_integral c _ hR]
      exact (integral_circleMeasure _ hi d R).symm

#print axioms circle_arcsine_cross_energy
#print axioms circle_measure_self_energy
#print axioms circle_measure_mutual_energy
#print axioms circle_circle_log_integrable
#print axioms arcsine_circle_log_integrable
#print axioms circleMeasure_nullSingleton
#print axioms arcsineMeasure_nullSingleton
#print axioms arcsine_arcsine_log_integrable
#print axioms nested_arcsine_energy
end Zeta5CircleMeasures
