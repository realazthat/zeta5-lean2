import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
import Mathlib.Topology.UniformSpace.Dini
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# Circle regularization in the logarithmic-energy bound

Lean 4.32.2 and mathlib v4.32.2.
-/
namespace Zeta5CirclePotential
open MeasureTheory Real Metric

/-- Averaging log-distance around a circle truncates it below at the log radius. -/
theorem circle_average_log_distance (c a : ℂ) {R : ℝ} (hR : 0 < R) :
    circleAverage (fun z : ℂ => Real.log ‖z-a‖) c R =
      Real.log (max ‖c-a‖ R) := by
  rcases le_total ‖c-a‖ R with h | h
  · rw [max_eq_right h]
    apply circleAverage_log_norm_sub_const_of_mem_closedBall
    rw [mem_closedBall, abs_of_pos hR, dist_eq_norm']
    exact h
  · rw [max_eq_left h,
      circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (ne_of_gt hR),
      posLog_eq_log]
    · rw [Real.log_mul (inv_ne_zero (ne_of_gt hR))
        (ne_of_gt (hR.trans_le h)), Real.log_inv]
      ring
    · rw [abs_of_nonneg (mul_nonneg (inv_nonneg.2 hR.le) (norm_nonneg _))]
      exact (one_le_inv_mul₀ hR).2 h

open Filter Set in
/-- Circle averages respect inequalities that fail at one point. This keeps the
`log 0 = 0` convention from introducing a false pointwise inequality. -/
theorem circle_average_mono_off_point {f g : ℂ → ℝ} {c p : ℂ} {R : ℝ}
    (hR : R ≠ 0) (hf : CircleIntegrable f c R) (hg : CircleIntegrable g c R)
    (hfg : ∀ z ∈ sphere c |R|, z ≠ p → f z ≤ g z) :
    circleAverage f c R ≤ circleAverage g c R := by
  let f' : ℂ → ℝ := fun z => if z = p then g z else f z
  have he : f =ᶠ[codiscreteWithin (sphere c |R|)] f' := by
    filter_upwards [compl_singleton_mem_codiscreteWithin (s := sphere c |R|) p] with z hz
    have hz' : z ≠ p := by simpa using hz
    simp [f', hz']
  rw [circleAverage_congr_codiscreteWithin he hR]
  apply circleAverage_mono (CircleIntegrable.congr_codiscreteWithin he hf) hg
  intro z hz
  by_cases hzp : z = p
  · simp [f', hzp]
  · simpa [f', hzp] using hfg z hz hzp

/-- Averaging twice over two equal-radius circles can only increase the
log-distance between their distinct centers. This is the mutual-energy
inequality used immediately before (6.6). -/
theorem mutual_circle_energy_ge_log_distance (c d : ℂ) {R : ℝ}
    (hR : 0 < R) (hcd : c ≠ d) :
    Real.log ‖c-d‖ ≤ circleAverage
      (fun w : ℂ => circleAverage (fun z : ℂ => Real.log ‖z-w‖) c R) d R := by
  have hcont : Continuous (fun w : ℂ => Real.log (max ‖c-w‖ R)) := by
    apply Continuous.log
    · fun_prop
    · intro w
      exact ne_of_gt (hR.trans_le (le_max_right _ _))
  have hi : CircleIntegrable (fun w : ℂ => Real.log (max ‖c-w‖ R)) d R :=
    hcont.continuousOn.circleIntegrable'
  have hlogi : CircleIntegrable (fun w : ℂ => Real.log ‖c-w‖) d R := by
    simpa only [norm_sub_rev] using (circleIntegrable_log_norm_sub_const (a := c) (c := d) R)
  have hmono : circleAverage (fun w : ℂ => Real.log ‖c-w‖) d R ≤
      circleAverage (fun w : ℂ => Real.log (max ‖c-w‖ R)) d R := by
    apply circle_average_mono_off_point (p := c) (ne_of_gt hR) hlogi hi
    intro w _ hw
    apply Real.log_le_log
    · exact norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hw))
    · exact le_max_left _ _
  have he : circleAverage (fun w : ℂ => Real.log ‖c-w‖) d R =
      Real.log (max ‖c-d‖ R) := by
    simpa only [norm_sub_rev] using circle_average_log_distance d c hR
  rw [he] at hmono
  have hlow : Real.log ‖c-d‖ ≤ Real.log (max ‖c-d‖ R) :=
    Real.log_le_log (norm_pos_iff.2 (sub_ne_zero.2 hcd)) (le_max_left _ _)
  simpa only [circle_average_log_distance c _ hR] using hlow.trans hmono

/-- The self-energy of one normalized circle is its log radius. -/
theorem circle_self_energy (c : ℂ) {R : ℝ} (hR : 0 < R) :
    circleAverage (fun w : ℂ =>
      circleAverage (fun z : ℂ => Real.log ‖z-w‖) c R) c R = Real.log R := by
  apply circleAverage_const_on_circle
  intro w hw
  rw [circle_average_log_distance c w hR]
  have hn : ‖c-w‖ = R := by
    rw [mem_sphere, dist_eq_norm', abs_of_pos hR] at hw
    exact hw
  rw [hn, max_self]

open Filter Set Complex in
/-- Pointwise factorization of the arcsine logarithm away from its at most two
circle singularities, including the nonvanishing needed for scaling. -/
theorem normalized_arcsine_factorization (t : ℝ) (u v : ℂ)
    (hsum : u+v = 2*(t : ℂ)) (hprod : u*v = 1) :
    ∀ᶠ z : ℂ in codiscreteWithin (sphere (0 : ℂ) |(1 : ℝ)|),
      |t-z.re| ≠ 0 ∧ Real.log |t-z.re| =
      Real.log ‖z-u‖+Real.log ‖z-v‖-Real.log 2 := by
  filter_upwards [Filter.self_mem_codiscreteWithin (sphere (0 : ℂ) |(1 : ℝ)|),
    compl_singleton_mem_codiscreteWithin (s := sphere (0 : ℂ) |(1 : ℝ)|) u,
    compl_singleton_mem_codiscreteWithin (s := sphere (0 : ℂ) |(1 : ℝ)|) v] with z hz hzu hzv
  have hzn : ‖z‖ = 1 := by simpa only [mem_sphere, dist_zero_right, abs_one] using hz
  have hzu' : z ≠ u := by simpa using hzu
  have hzv' : z ≠ v := by simpa using hzv
  have hzc : z * (starRingEnd ℂ) z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hzn]
    norm_num
  have hzr : (2 : ℂ)*(z.re : ℂ) = z+(starRingEnd ℂ) z := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using (Complex.add_conj z).symm
  have hp : (z-u)*(z-v) = (-2 : ℂ)*z*((t : ℂ)-(z.re : ℂ)) := by
    calc
      _ = z^2-(u+v)*z+u*v := by ring
      _ = z^2-2*(t : ℂ)*z+1 := by rw [hsum,hprod]
      _ = z*(z+(starRingEnd ℂ) z)-2*z*(t : ℂ) := by rw [mul_add,hzc]; ring
      _ = _ := by rw [← hzr]; ring
  have hn : ‖z-u‖*‖z-v‖ = 2*|t-z.re| := by
    rw [← norm_mul,hp]
    simp only [norm_mul, norm_neg, Complex.norm_ofNat, hzn, mul_one,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hnu : ‖z-u‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hzu')
  have hnv : ‖z-v‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hzv')
  have habs : |t-z.re| ≠ 0 := by
    intro h
    rw [h,mul_zero] at hn
    exact mul_ne_zero hnu hnv hn
  have hlog := congrArg Real.log hn
  rw [Real.log_mul hnu hnv,Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) habs] at hlog
  exact ⟨habs, by linarith⟩

open Filter Set Complex in
/-- The potential of the normalized arcsine distribution expressed through the
two roots of its associated quadratic. This avoids choosing square-root
branches before treating the inside/outside interval cases. -/
theorem normalized_arcsine_potential_via_roots (t : ℝ) (u v : ℂ)
    (hsum : u+v = 2*(t : ℂ)) (hprod : u*v = 1) :
    circleAverage (fun z : ℂ => Real.log |t-z.re|) 0 1 =
      Real.log (max ‖u‖ 1)+Real.log (max ‖v‖ 1)-Real.log 2 := by
  have he := (normalized_arcsine_factorization t u v hsum hprod).mono
    (fun _ h => h.2)
  rw [circleAverage_congr_codiscreteWithin he (by norm_num)]
  have hiadd : CircleIntegrable
      (fun z : ℂ => Real.log ‖z-u‖+Real.log ‖z-v‖) 0 1 := by
    exact (circleIntegrable_log_norm_sub_const (a := u) (c := 0) 1).add
      (circleIntegrable_log_norm_sub_const (a := v) (c := 0) 1)
  rw [circleAverage_fun_sub hiadd (circleIntegrable_const (Real.log 2) (0 : ℂ) 1),
    circleAverage_fun_add
      (circleIntegrable_log_norm_sub_const (a := u) (c := 0) 1)
      (circleIntegrable_log_norm_sub_const (a := v) (c := 0) 1), circleAverage_const,
    circle_average_log_distance 0 u (by norm_num),
    circle_average_log_distance 0 v (by norm_num)]
  simp

/-- The arcsine potential is constant throughout its support, including endpoints. -/
theorem normalized_arcsine_potential_inside {t : ℝ} (ht : -1 ≤ t ∧ t ≤ 1) :
    circleAverage (fun z : ℂ => Real.log |t-z.re|) 0 1 = -Real.log 2 := by
  let q := Real.sqrt (1-t^2)
  let u : ℂ := ⟨t,q⟩
  let v : ℂ := ⟨t,-q⟩
  have hq : q^2 = 1-t^2 := Real.sq_sqrt (by nlinarith [ht.1,ht.2])
  have hsum : u+v = 2*(t : ℂ) := by
    apply Complex.ext <;> simp [u,v] <;> ring
  have hprod : u*v = 1 := by
    apply Complex.ext <;> simp [u,v]
    · nlinarith
    · ring
  have hnu : ‖u‖ = 1 := by
    have hsq := Complex.sq_norm u
    rw [Complex.normSq_apply] at hsq
    dsimp [u] at hsq
    nlinarith [norm_nonneg u]
  have hnv : ‖v‖ = 1 := by
    have hsq := Complex.sq_norm v
    rw [Complex.normSq_apply] at hsq
    dsimp [v] at hsq
    nlinarith [norm_nonneg v]
  rw [normalized_arcsine_potential_via_roots t u v hsum hprod,hnu,hnv]
  simp

/-- The right-hand exterior branch of the arcsine potential. -/
theorem normalized_arcsine_potential_right {t : ℝ} (ht : 1 < t) :
    circleAverage (fun z : ℂ => Real.log |t-z.re|) 0 1 =
      Real.log ((t+Real.sqrt (t^2-1))/2) := by
  let q := Real.sqrt (t^2-1)
  let u : ℂ := (t+q : ℝ)
  let v : ℂ := (t-q : ℝ)
  have hq : q^2 = t^2-1 := Real.sq_sqrt (by nlinarith)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqt : q < t := by nlinarith
  have hqt1 : t-1 < q := by nlinarith
  have hsum : u+v = 2*(t : ℂ) := by dsimp [u,v]; push_cast; ring
  have hprod : u*v = 1 := by
    change ((t+q : ℝ) : ℂ)*((t-q : ℝ) : ℂ) = 1
    exact_mod_cast (show (t+q)*(t-q) = 1 by nlinarith)
  have hnu : ‖u‖ = t+q := by
    change ‖((t+q : ℝ) : ℂ)‖ = t+q
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith : 0 < t+q)]
  have hnv : ‖v‖ = t-q := by
    change ‖((t-q : ℝ) : ℂ)‖ = t-q
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith : 0 < t-q)]
  rw [normalized_arcsine_potential_via_roots t u v hsum hprod,hnu,hnv,
    max_eq_left (by linarith : 1 ≤ t+q),max_eq_right (by linarith : t-q ≤ 1),Real.log_one,add_zero]
  rw [Real.log_div (by linarith : t+q ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]

/-- The left-hand exterior branch of the arcsine potential. -/
theorem normalized_arcsine_potential_left {t : ℝ} (ht : t < -1) :
    circleAverage (fun z : ℂ => Real.log |t-z.re|) 0 1 =
      Real.log ((-t+Real.sqrt (t^2-1))/2) := by
  let q := Real.sqrt (t^2-1)
  let u : ℂ := (t+q : ℝ)
  let v : ℂ := (t-q : ℝ)
  have hq : q^2 = t^2-1 := Real.sq_sqrt (by nlinarith)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqt : q < -t := by nlinarith
  have hqt1 : -t-1 < q := by nlinarith
  have hsum : u+v = 2*(t : ℂ) := by dsimp [u,v]; push_cast; ring
  have hprod : u*v = 1 := by
    change ((t+q : ℝ) : ℂ)*((t-q : ℝ) : ℂ) = 1
    exact_mod_cast (show (t+q)*(t-q) = 1 by nlinarith)
  have hnu : ‖u‖ = -(t+q) := by
    change ‖((t+q : ℝ) : ℂ)‖ = -(t+q)
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_neg (by linarith : t+q < 0)]
  have hnv : ‖v‖ = -t+q := by
    change ‖((t-q : ℝ) : ℂ)‖ = -t+q
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_neg (by linarith : t-q < 0)]
    ring
  rw [normalized_arcsine_potential_via_roots t u v hsum hprod,hnu,hnv,
    max_eq_right (by linarith : -(t+q) ≤ 1),max_eq_left (by linarith : 1 ≤ -t+q),Real.log_one,zero_add]
  rw [Real.log_div (by linarith : -t+q ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]

/-- Both exterior branches of the normalized arcsine potential. -/
theorem normalized_arcsine_potential_outside {t : ℝ} (ht : 1 < |t|) :
    circleAverage (fun z : ℂ => Real.log |t-z.re|) 0 1 =
      Real.log ((|t|+Real.sqrt (t^2-1))/2) := by
  rcases le_or_gt 0 t with h | h
  · rw [abs_of_nonneg h] at ht ⊢
    exact normalized_arcsine_potential_right ht
  · rw [abs_of_neg h] at ht ⊢
    exact normalized_arcsine_potential_left (by linarith)

open Filter Set in
/-- Multiplying the arcsine argument by a positive scale adds its logarithm.
The finite singularities are handled explicitly rather than using log(0). -/
theorem scaled_arcsine_potential_via_roots (t r : ℝ) (hr : 0 < r) (u v : ℂ)
    (hsum : u+v = 2*(t : ℂ)) (hprod : u*v = 1) :
    CircleIntegrable (fun z : ℂ => Real.log |r*(t-z.re)|) 0 1 ∧
    circleAverage (fun z : ℂ => Real.log |r*(t-z.re)|) 0 1 =
      Real.log r+Real.log (max ‖u‖ 1)+Real.log (max ‖v‖ 1)-Real.log 2 := by
  have he : (fun z : ℂ => Real.log |r*(t-z.re)|) =ᶠ[codiscreteWithin (sphere (0 : ℂ) |(1 : ℝ)|)]
      (fun z : ℂ => Real.log r+(Real.log ‖z-u‖+Real.log ‖z-v‖-Real.log 2)) := by
    filter_upwards [normalized_arcsine_factorization t u v hsum hprod] with z hz
    rw [abs_mul,abs_of_pos hr,Real.log_mul (ne_of_gt hr) hz.1,hz.2]
  have hiadd : CircleIntegrable
      (fun z : ℂ => Real.log ‖z-u‖+Real.log ‖z-v‖) 0 1 :=
    (circleIntegrable_log_norm_sub_const (a := u) (c := 0) 1).add
      (circleIntegrable_log_norm_sub_const (a := v) (c := 0) 1)
  have hisub : CircleIntegrable
      (fun z : ℂ => Real.log ‖z-u‖+Real.log ‖z-v‖-Real.log 2) 0 1 :=
    hiadd.sub (circleIntegrable_const (Real.log 2) 0 1)
  have hirhs : CircleIntegrable
      (fun z : ℂ => Real.log r+(Real.log ‖z-u‖+Real.log ‖z-v‖-Real.log 2)) 0 1 :=
    (circleIntegrable_const (Real.log r) 0 1).add hisub
  refine ⟨CircleIntegrable.congr_codiscreteWithin he.symm hirhs, ?_⟩
  rw [circleAverage_congr_codiscreteWithin he (by norm_num),
    circleAverage_fun_add (circleIntegrable_const (Real.log r) 0 1) hisub,
    circleAverage_fun_sub hiadd (circleIntegrable_const (Real.log 2) 0 1),
    circleAverage_fun_add
      (circleIntegrable_log_norm_sub_const (a := u) (c := 0) 1)
      (circleIntegrable_log_norm_sub_const (a := v) (c := 0) 1),
    circleAverage_const,circleAverage_const,
    circle_average_log_distance 0 u (by norm_num),
    circle_average_log_distance 0 v (by norm_num)]
  simp only [zero_sub,norm_neg]
  ring

/-- The reciprocal quadratic has two complex roots for every real parameter. -/
theorem arcsine_roots_exist (t : ℝ) :
    ∃ u v : ℂ, u+v = 2*(t : ℂ) ∧ u*v = 1 := by
  rcases le_total 1 (t^2) with h | h
  · let q := Real.sqrt (t^2-1)
    have hq : q^2 = t^2-1 := Real.sq_sqrt (by linarith)
    refine ⟨((t+q : ℝ) : ℂ),((t-q : ℝ) : ℂ), ?_, ?_⟩
    · push_cast; ring
    · exact_mod_cast (show (t+q)*(t-q) = 1 by nlinarith)
  · let q := Real.sqrt (1-t^2)
    have hq : q^2 = 1-t^2 := Real.sq_sqrt (by linarith)
    refine ⟨⟨t,q⟩,⟨t,-q⟩, ?_, ?_⟩
    · apply Complex.ext <;> simp <;> ring
    · apply Complex.ext <;> simp
      · nlinarith
      · ring

/-- Exact scaling and integrability of every real arcsine potential. -/
theorem circle_average_arcsine_scale (t r : ℝ) (hr : 0 < r) :
    CircleIntegrable (fun z : ℂ => Real.log |r*(t-z.re)|) 0 1 ∧
    circleAverage (fun z : ℂ => Real.log |r*(t-z.re)|) 0 1 =
      Real.log r+circleAverage (fun z : ℂ => Real.log |t-z.re|) 0 1 := by
  obtain ⟨u,v,hsum,hprod⟩ := arcsine_roots_exist t
  obtain ⟨hi,he⟩ := scaled_arcsine_potential_via_roots t r hr u v hsum hprod
  refine ⟨hi, ?_⟩
  rw [he,normalized_arcsine_potential_via_roots t u v hsum hprod]
  ring

/-- The arcsine measure on `[a,b]` is the image of uniform angle under
`(a+b)/2 + (b-a)/2*cos θ`. Its potential is defined by that actual integral. -/
noncomputable def arcsinePotential (a b t : ℝ) : ℝ :=
  circleAverage (fun z : ℂ =>
    Real.log |t-((a+b)/2+(b-a)/2*z.re)|) 0 1

/-- Reducing an arbitrary interval to the normalized one. -/
theorem arcsine_potential_scaling (a b t : ℝ) (hab : a < b) :
    arcsinePotential a b t = Real.log ((b-a)/2)+
      circleAverage (fun z : ℂ => Real.log |(t-(a+b)/2)/((b-a)/2)-z.re|) 0 1 := by
  have hr : 0 < (b-a)/2 := by linarith
  have hid (z : ℂ) : t-((a+b)/2+(b-a)/2*z.re) =
      ((b-a)/2)*((t-(a+b)/2)/((b-a)/2)-z.re) := by
    field_simp [ne_of_gt hr, sub_ne_zero.mpr (ne_of_gt hab)]
    ring
  simp only [arcsinePotential,hid]
  exact (circle_average_arcsine_scale _ _ hr).2

/-- The first branch of Appendix A, equation (A.1), for an actual arcsine
potential integral. -/
theorem arcsine_potential_inside (a b t : ℝ) (hab : a < b) (ht : a ≤ t ∧ t ≤ b) :
    arcsinePotential a b t = Real.log ((b-a)/4) := by
  have hr : 0 < (b-a)/2 := by linarith
  have hx : -1 ≤ (t-(a+b)/2)/((b-a)/2) ∧ (t-(a+b)/2)/((b-a)/2) ≤ 1 := by
    constructor
    · apply (le_div_iff₀ hr).2
      linarith [ht.1]
    · apply (div_le_iff₀ hr).2
      linarith [ht.2]
  rw [arcsine_potential_scaling a b t hab,normalized_arcsine_potential_inside hx]
  rw [← sub_eq_add_neg, ← Real.log_div (ne_of_gt hr) (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  ring

/-- The exterior branch of Appendix A, equation (A.1), for the same actual
arcsine potential integral. -/
theorem arcsine_potential_outside (a b t : ℝ) (hab : a < b) (ht : t < a ∨ b < t) :
    arcsinePotential a b t =
      Real.log ((|t-(a+b)/2|+Real.sqrt ((t-a)*(t-b)))/2) := by
  let m := (a+b)/2
  let r := (b-a)/2
  let x := (t-m)/r
  have hr : 0 < r := by dsimp [r]; linarith
  have hrep : r*x = t-m := by dsimp [x]; field_simp [ne_of_gt hr]
  have hx : 1 < |x| := by
    rcases ht with h | h
    · have hx' : x < -1 := by
        apply (div_lt_iff₀ hr).2
        dsimp [r,m]
        linarith
      rw [abs_of_neg (by linarith : x < 0)]
      linarith
    · have hx' : 1 < x := by
        apply (lt_div_iff₀ hr).2
        dsimp [r,m]
        linarith
      rw [abs_of_pos (by linarith : 0 < x)]
      exact hx'
  have hx2 : 0 ≤ x^2-1 := by nlinarith [sq_abs x]
  have hD : 0 ≤ (t-a)*(t-b) := by
    rcases ht with h | h
    · apply mul_nonneg_of_nonpos_of_nonpos <;> linarith
    · apply mul_nonneg <;> linarith
  have hDexpr : r^2*(x^2-1) = (t-a)*(t-b) := by
    calc
      _ = (r*x)^2-r^2 := by ring
      _ = _ := by rw [hrep]; dsimp [m,r]; ring
  have habs : r*|x| = |t-m| := by
    rw [← abs_of_pos hr, ← abs_mul, hrep]
  have hsqrt : r*Real.sqrt (x^2-1) = Real.sqrt ((t-a)*(t-b)) := by
    have hsq : (r*Real.sqrt (x^2-1))^2 = (t-a)*(t-b) := by
      rw [mul_pow,Real.sq_sqrt hx2]
      exact hDexpr
    nlinarith [Real.sq_sqrt hD, Real.sqrt_nonneg ((t-a)*(t-b)),
      mul_nonneg hr.le (Real.sqrt_nonneg (x^2-1))]
  rw [arcsine_potential_scaling a b t hab]
  change Real.log r+circleAverage (fun z : ℂ => Real.log |x-z.re|) 0 1 = _
  rw [normalized_arcsine_potential_outside hx]
  rw [← Real.log_mul (ne_of_gt hr)
    (show (|x|+Real.sqrt (x^2-1))/2 ≠ 0 by
      have : 0 < |x| := by linarith
      positivity)]
  congr 1
  change r*((|x|+Real.sqrt (x^2-1))/2) = (|t-m|+Real.sqrt ((t-a)*(t-b)))/2
  nlinarith

/-- A branch-free formula makes continuity of the arcsine potential explicit.
Lean's nonnegative square root vanishes when `t²-1 ≤ 0`. -/
theorem normalized_arcsine_potential_closedform (t : ℝ) :
    circleAverage (fun z : ℂ => Real.log |t-z.re|) 0 1 =
      Real.log ((max 1 |t|+Real.sqrt (t^2-1))/2) := by
  by_cases ht : |t| ≤ 1
  · have hi : -1 ≤ t ∧ t ≤ 1 := abs_le.1 ht
    have hs : t^2-1 ≤ 0 := by nlinarith [sq_abs t, abs_nonneg t]
    rw [normalized_arcsine_potential_inside hi, max_eq_left ht,
      Real.sqrt_eq_zero_of_nonpos hs,add_zero]
    simp [Real.log_div]
  · have ho : 1 < |t| := lt_of_not_ge ht
    rw [max_eq_right ho.le]
    exact normalized_arcsine_potential_outside ho

/-- The real arcsine potential is continuous, including at both endpoints. -/
theorem continuous_arcsine_potential (a b : ℝ) (hab : a < b) :
    Continuous (arcsinePotential a b) := by
  have he : arcsinePotential a b = (fun t : ℝ => Real.log ((b-a)/2)+
      Real.log ((max 1 |(t-(a+b)/2)/((b-a)/2)|+
        Real.sqrt (((t-(a+b)/2)/((b-a)/2))^2-1))/2)) := by
    funext t
    rw [arcsine_potential_scaling a b t hab,normalized_arcsine_potential_closedform]
  rw [he]
  apply Continuous.add continuous_const
  apply Continuous.log
  · fun_prop
  · intro t
    have hmax : 1 ≤ max 1 |(t-(a+b)/2)/((b-a)/2)| := le_max_left _ _
    have hs := Real.sqrt_nonneg ((((t-(a+b)/2)/((b-a)/2))^2-1))
    linarith

/-- Integrability of the arcsine logarithm as an angle integral. -/
theorem arcsine_log_circleIntegrable (a b t : ℝ) (hab : a < b) :
    CircleIntegrable (fun z : ℂ => Real.log |t-((a+b)/2+(b-a)/2*z.re)|) 0 1 := by
  have hr : 0 < (b-a)/2 := by linarith
  have hid (z : ℂ) : t-((a+b)/2+(b-a)/2*z.re) =
      ((b-a)/2)*((t-(a+b)/2)/((b-a)/2)-z.re) := by
    field_simp [ne_of_gt hr, sub_ne_zero.mpr (ne_of_gt hab)]
    ring
  simp only [hid]
  exact (circle_average_arcsine_scale _ _ hr).1

open Filter Set in
/-- The finitely many angle singularities have Lebesgue measure zero. -/
theorem arcsine_argument_ae_nonzero (a b t : ℝ) (hab : a < b) :
    ∀ᵐ θ : ℝ, t-((a+b)/2+(b-a)/2*(circleMap 0 1 θ).re) ≠ 0 := by
  let x := (t-(a+b)/2)/((b-a)/2)
  have hr : 0 < (b-a)/2 := by linarith
  obtain ⟨u,v,hsum,hprod⟩ := arcsine_roots_exist x
  have he := (normalized_arcsine_factorization x u v hsum hprod).mono (fun _ h => h.1)
  have hpre := circleMap_preimage_codiscrete (c := (0 : ℂ)) (R := (1 : ℝ)) (by norm_num) he
  have hae : (ae (volume : Measure ℝ)) ≤ codiscrete ℝ := by
    simpa [Filter.codiscrete] using (ae_restrict_le_codiscreteWithin (μ := (volume : Measure ℝ)) MeasurableSet.univ)
  have ha : ∀ᵐ θ : ℝ, |x-(circleMap 0 1 θ).re| ≠ 0 := hae hpre
  filter_upwards [ha] with θ hθ
  have hx : x-(circleMap 0 1 θ).re ≠ 0 := by simpa only [abs_ne_zero] using hθ
  have hid : t-((a+b)/2+(b-a)/2*(circleMap 0 1 θ).re) =
      ((b-a)/2)*(x-(circleMap 0 1 θ).re) := by
    dsimp [x]
    field_simp [ne_of_gt hr, sub_ne_zero.mpr (ne_of_gt hab)]
    ring
  rw [hid]
  exact mul_ne_zero (ne_of_gt hr) hx

/-- Truncation toward zero decreases the magnitude of the logarithm when the
cutoff is at most one. -/
theorem abs_log_max_le {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |Real.log (max d ε)| ≤ |Real.log d| := by
  rcases le_total d ε with h | h
  · rw [max_eq_right h]
    have hlε : Real.log ε ≤ 0 := Real.log_nonpos hε.le hε1
    have hld : Real.log d ≤ Real.log ε := Real.log_le_log hd h
    rw [abs_of_nonpos hlε,abs_of_nonpos (hld.trans hlε)]
    linarith
  · rw [max_eq_left h]

/-- The regularized real potential. -/
noncomputable def truncatedArcsinePotential (a b ε t : ℝ) : ℝ :=
  circleAverage (fun z : ℂ =>
    Real.log (max |t-((a+b)/2+(b-a)/2*z.re)| ε)) 0 1

/-- Every positive truncation is continuous as a function of its center. -/
theorem continuous_truncated_arcsine_potential (a b ε : ℝ) (hε : 0 < ε) :
    Continuous (truncatedArcsinePotential a b ε) := by
  let F : ℝ → ℝ → ℝ := fun t θ =>
    Real.log (max |t-((a+b)/2+(b-a)/2*(circleMap 0 1 θ).re)| ε)
  have hF : Continuous (Function.uncurry F) := by
    apply Continuous.log
    · fun_prop
    · intro p
      exact ne_of_gt (hε.trans_le (le_max_right _ _))
  have hi := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) hF 0 (2*Real.pi)
  change Continuous (((2*Real.pi)⁻¹ : ℝ) •
    (fun t : ℝ => ∫ θ in 0..2*Real.pi, F t θ))
  exact hi.const_smul ((2*Real.pi)⁻¹)

open Filter Topology Set in
/-- Pointwise convergence of the truncated potentials, with the actual
logarithm as an integrable dominating function. -/
theorem truncated_arcsine_potential_tendsto (a b t : ℝ) (hab : a < b) :
    Tendsto (fun n : ℕ => truncatedArcsinePotential a b (1/((n : ℝ)+1)) t)
      atTop (𝓝 (arcsinePotential a b t)) := by
  unfold truncatedArcsinePotential arcsinePotential circleAverage
  apply Filter.Tendsto.const_smul
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun θ : ℝ => |Real.log (|t-((a+b)/2+(b-a)/2*(circleMap 0 1 θ).re)|)|)
  · apply Filter.Eventually.of_forall
    intro n
    apply Continuous.aestronglyMeasurable
    apply Continuous.log
    · fun_prop
    · intro θ
      have he : (0 : ℝ) < 1/((n : ℝ)+1) := by positivity
      exact ne_of_gt (he.trans_le (le_max_right _ _))
  · apply Filter.Eventually.of_forall
    intro n
    filter_upwards [arcsine_argument_ae_nonzero a b t hab] with θ hθ _
    rw [Real.norm_eq_abs]
    apply abs_log_max_le (abs_pos.2 hθ) (by positivity)
    apply (div_le_one (by positivity : (0 : ℝ) < (n : ℝ)+1)).2
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · exact (arcsine_log_circleIntegrable a b t hab).abs
  · filter_upwards [arcsine_argument_ae_nonzero a b t hab] with θ hθ _
    have hd : 0 < |t-((a+b)/2+(b-a)/2*(circleMap 0 1 θ).re)| := abs_pos.2 hθ
    have hc : Tendsto (fun _ : ℕ => |t-((a+b)/2+(b-a)/2*(circleMap 0 1 θ).re)|)
        atTop (𝓝 |t-((a+b)/2+(b-a)/2*(circleMap 0 1 θ).re)|) := tendsto_const_nhds
    have hmax := hc.max (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hmax' : Tendsto
        (fun n : ℕ => max |t-((a+b)/2+(b-a)/2*(circleMap 0 1 θ).re)| (1/((n : ℝ)+1)))
        atTop (𝓝 |t-((a+b)/2+(b-a)/2*(circleMap 0 1 θ).re)|) := by
      simpa only [max_eq_left hd.le] using hmax
    exact (Real.continuousAt_log (ne_of_gt hd)).tendsto.comp hmax'

theorem truncated_arcsine_circleIntegrable (a b ε t : ℝ) (hε : 0 < ε) :
    CircleIntegrable (fun z : ℂ => Real.log (max |t-((a+b)/2+(b-a)/2*z.re)| ε)) 0 1 := by
  apply ContinuousOn.circleIntegrable'
  apply Continuous.continuousOn
  apply Continuous.log
  · fun_prop
  · intro z
    exact ne_of_gt (hε.trans_le (le_max_right _ _))

/-- Truncation decreases monotonically when its cutoff decreases. -/
theorem truncated_arcsine_antitone (a b t : ℝ) :
    Antitone (fun n : ℕ => truncatedArcsinePotential a b (1/((n : ℝ)+1)) t) := by
  intro i j hij
  unfold truncatedArcsinePotential
  apply circleAverage_mono
    (truncated_arcsine_circleIntegrable a b _ t (by positivity))
    (truncated_arcsine_circleIntegrable a b _ t (by positivity))
  intro z _
  apply Real.log_le_log (by
    have hj : (0 : ℝ) < 1/((j : ℝ)+1) := by positivity
    exact hj.trans_le (le_max_right _ _))
  apply max_le_max le_rfl
  apply one_div_le_one_div_of_le (by positivity)
  have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
  linarith

open Filter in
/-- Dini's theorem gives uniform regularization on every compact set. -/
theorem truncated_arcsine_potential_uniform_on (a b : ℝ) (hab : a < b)
    {S : Set ℝ} (hS : IsCompact S) :
    TendstoUniformlyOn
      (fun n : ℕ => truncatedArcsinePotential a b (1/((n : ℝ)+1)))
      (arcsinePotential a b) atTop S := by
  exact Antitone.tendstoUniformlyOn_of_forall_tendsto hS
    (fun n => (continuous_truncated_arcsine_potential a b _ (by positivity)).continuousOn)
    (fun t _ => truncated_arcsine_antitone a b t)
    (continuous_arcsine_potential a b hab).continuousOn
    (fun t _ => truncated_arcsine_potential_tendsto a b t hab)

/-- The real image of a unit circle point lies in the corresponding interval. -/
theorem arcsine_point_mem_interval (a b : ℝ) (hab : a ≤ b) (z : ℂ)
    (hz : z ∈ sphere (0 : ℂ) |(1 : ℝ)|) :
    a ≤ (a+b)/2+(b-a)/2*z.re ∧ (a+b)/2+(b-a)/2*z.re ≤ b := by
  have hzn : ‖z‖ = 1 := by simpa only [mem_sphere,dist_zero_right,abs_one] using hz
  have hre := Complex.abs_re_le_norm z
  rw [hzn] at hre
  obtain ⟨hl,hu⟩ := abs_le.1 hre
  have hr : 0 ≤ (b-a)/2 := by linarith
  have hleft := mul_le_mul_of_nonneg_left hl hr
  have hright := mul_le_mul_of_nonneg_left hu hr
  constructor <;> nlinarith

/-- On the exterior half-line the regularization is already exact. -/
theorem truncated_arcsine_tail_eq (a b ε t : ℝ) (hab : a < b)
    (hb : b ≤ 1) (hε : ε ≤ 1) (ht : 2 ≤ t) :
    truncatedArcsinePotential a b ε t = arcsinePotential a b t := by
  unfold truncatedArcsinePotential arcsinePotential
  apply circleAverage_congr_sphere
  intro z hz
  have hpoint := (arcsine_point_mem_interval a b hab.le z hz).2
  have hd : 1 ≤ t-((a+b)/2+(b-a)/2*z.re) := by linarith
  change Real.log (max |t-((a+b)/2+(b-a)/2*z.re)| ε) =
    Real.log |t-((a+b)/2+(b-a)/2*z.re)|
  rw [max_eq_left (hε.trans (hd.trans (le_abs_self _)))]

open Filter in
/-- Uniform error control on the whole nonnegative half-line, sufficient for
the `o(K²)` error in the determinant exponent. No quantitative Hölder rate is
needed for the irrationality proof. -/
theorem eventually_truncated_arcsine_le (a b : ℝ) (hab : a < b) (hb : b ≤ 1)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, 0 ≤ t →
      truncatedArcsinePotential a b (1/((n : ℝ)+1)) t ≤ arcsinePotential a b t+η := by
  have hu := truncated_arcsine_potential_uniform_on a b hab
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 2))
  have he := (Metric.tendstoUniformlyOn_iff.1 hu) η hη
  filter_upwards [he] with n hn t ht
  rcases le_total t 2 with ht2 | ht2
  · have h := hn t ⟨ht,ht2⟩
    rw [Real.dist_eq] at h
    have := (abs_lt.1 h).1
    linarith
  · have hε : 1/((n : ℝ)+1) ≤ 1 := by
      apply (div_le_one (by positivity : (0 : ℝ) < (n : ℝ)+1)).2
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    rw [truncated_arcsine_tail_eq a b _ t hab hb hε ht2]
    linarith

#print axioms continuous_arcsine_potential
#print axioms arcsine_argument_ae_nonzero
#print axioms truncated_arcsine_potential_tendsto
#print axioms truncated_arcsine_potential_uniform_on
#print axioms eventually_truncated_arcsine_le
end Zeta5CirclePotential
