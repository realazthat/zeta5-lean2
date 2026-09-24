import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-!
# Verified ingredients of the real-energy argument

Source: Aabir Fauzan, Zenodo 22826419, Appendix A and Section 6.
This file proves the zero-mass logarithmic-energy inequality of Lemma 6.2,
using real densities against positive measures on the plane. It includes
Gaussian convolution, Gaussian energy positivity, Frullani's formula with
absolute convergence, and the Fubini justifications. An explicit off-diagonal
condition handles Lean's convention `Real.log 0 = 0`; a nonatomic measure
implies this condition. The usual log-distance theorem is
`zero_mass_log_distance_energy_nonpos`.

It also verifies Table 1's finite data and the half-line estimate after (6.8).
It does NOT prove the full determinant estimate, the arcsine potential formula,
or the circle-regularization argument. The separate Python audit reproduces
Appendix A's 684 numerical enclosures, but is not imported as a Lean axiom.
-/
namespace Zeta5RealEnergy

/-- Table 1, written as exact rational triples `(a, b, c)`. -/
def arcsineData : List (ℚ × ℚ × ℚ) := [
  (3906748086 / 10^12, 8992695531 / 10^12, 10515596180 / 10^12),
  (2312248264 / 10^12, 15340997855 / 10^12, 29471737793 / 10^12),
  (1402286665 / 10^12, 25730180724 / 10^12, 42934365099 / 10^12),
  (881725356 / 10^12, 41909578246 / 10^12, 58204231966 / 10^12),
  (578197906 / 10^12, 65851089563 / 10^12, 69037621310 / 10^12),
  (396324613 / 10^12, 99481037884 / 10^12, 78873099189 / 10^12),
  (283911191 / 10^12, 144325727458 / 10^12, 84856120711 / 10^12),
  (212206188 / 10^12, 201105762729 / 10^12, 88396082127 / 10^12),
  (165097686 / 10^12, 269345996903 / 10^12, 88303382125 / 10^12),
  (133347132 / 10^12, 347089554156 / 10^12, 85472321255 / 10^12),
  (111522114 / 10^12, 430806704415 / 10^12, 78899184238 / 10^12),
  (96349355 / 10^12, 515561896511 / 10^12, 70353471918 / 10^12),
  (85815639 / 10^12, 595448778546 / 10^12, 58838976615 / 10^12),
  (78667711 / 10^12, 664241383483 / 10^12, 44421321106 / 10^12),
  (74129565 / 10^12, 716160577112 / 10^12, 30462865791 / 10^12),
  (71741310 / 10^12, 746637295669 / 10^12, 5959622577 / 10^12)]

theorem sixteen_components : arcsineData.length = 16 := by rfl

/-- The comparison measure has exactly the required total mass. -/
theorem total_mass : (arcsineData.map fun row => row.2.2).sum = 37 / 40 := by
  norm_num [arcsineData]

/-- Every component has positive mass and satisfies the geometric bounds. -/
theorem component_properties : ∀ row ∈ arcsineData,
    0 < row.1 ∧ row.1 < row.2.1 ∧ row.2.1 < 2 ∧
      1 / 225 < row.2.1 - row.1 ∧ 0 < row.2.2 := by
  norm_num [arcsineData]

/-- Every interval is strictly contained in every subsequent interval. -/
theorem intervals_nested : arcsineData.Pairwise
    (fun earlier later => later.1 < earlier.1 ∧ earlier.2.1 < later.2.1) := by
  norm_num [arcsineData, List.pairwise_cons]

/-- A convenient elementary bound avoids differentiation of the tail field. -/
theorem log_le_twice_sqrt_sub_two {t : ℝ} (ht : 0 < t) :
    Real.log t ≤ 2 * Real.sqrt t - 2 := by
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 ht)
  rw [Real.log_sqrt ht.le] at h
  linarith

/-- The tail estimate needed for (6.7), including the integrability correction.
This holds for every real `K ≥ 2`, a stronger domain than the integer parameters
used in the paper. -/
theorem tail_field_bound {t K : ℝ} (ht : 2 ≤ t) (hK : 2 ≤ K) :
    (13 / 10 : ℝ) * Real.log t + 6 * (3 / 40 : ℝ)^3 / t -
      (2 * Real.pi - 1 / K) * Real.sqrt t < -(1329 / 200 : ℝ) := by
  have ht0 : 0 < t := by linarith
  have hs0 : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hs : 7 / 5 ≤ Real.sqrt t := by
    nlinarith [Real.sq_sqrt ht0.le]
  have hlog := log_le_twice_sqrt_sub_two ht0
  have hinvt : 1 / t ≤ (1 / 2 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) ht
  have hinvK : 1 / K ≤ (1 / 2 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hK
  have hpi := Real.pi_gt_three
  have hmul : (11 / 2 : ℝ) * Real.sqrt t ≤
      (2 * Real.pi - 1 / K) * Real.sqrt t := by
    exact mul_le_mul_of_nonneg_right (by linarith) hs0
  have hterm : 6 * (3 / 40 : ℝ)^3 / t ≤ 81 / 64000 := by
    calc
      6 * (3 / 40 : ℝ)^3 / t = (81 / 32000 : ℝ) * (1 / t) := by ring
      _ ≤ (81 / 32000 : ℝ) * (1 / 2) := by gcongr
      _ = 81 / 64000 := by norm_num
  nlinarith

open MeasureTheory in
/-- The Gaussian convolution identity in the proof of Lemma 6.2, in real
coordinates on the plane. All integrals are Lebesgue integrals. -/
theorem gaussian_convolution (s : ℝ) (hs : 0 < s) (z w : ℝ × ℝ) :
    (∫ u : ℝ × ℝ,
      Real.exp (-2 * s * ((z.1-u.1)^2 + (z.2-u.2)^2)) *
      Real.exp (-2 * s * ((w.1-u.1)^2 + (w.2-u.2)^2))) =
    Real.pi / (4*s) *
      Real.exp (-s * ((z.1-w.1)^2 + (z.2-w.2)^2)) := by
  have shifted (a : ℝ) :
      (∫ x : ℝ, Real.exp (-(4*s)*(x-a)^2)) = Real.sqrt (Real.pi/(4*s)) := by
    calc
      _ = ∫ x : ℝ, Real.exp (-(4*s)*x^2) := by
        simpa only [sub_eq_add_neg] using
          integral_add_right_eq_self (fun x : ℝ => Real.exp (-(4*s)*x^2)) (-a)
      _ = _ := integral_gaussian (4*s)
  have identity (u : ℝ × ℝ) :
      Real.exp (-2*s*((z.1-u.1)^2+(z.2-u.2)^2)) *
      Real.exp (-2*s*((w.1-u.1)^2+(w.2-u.2)^2)) =
      Real.exp (-s*((z.1-w.1)^2+(z.2-w.2)^2)) *
        (Real.exp (-(4*s)*(u.1-(z.1+w.1)/2)^2) *
         Real.exp (-(4*s)*(u.2-(z.2+w.2)/2)^2)) := by
    repeat rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [identity]
  rw [integral_const_mul, Measure.volume_eq_prod,
    integral_prod_mul (fun x : ℝ => Real.exp (-(4*s)*(x-(z.1+w.1)/2)^2))
      (fun y : ℝ => Real.exp (-(4*s)*(y-(z.2+w.2)/2)^2)), shifted, shifted]
  rw [Real.mul_self_sqrt (by positivity)]
  ring


open MeasureTheory in
/-- Integrability required when the Gaussian convolution is inserted into
finite signed energies. -/
theorem gaussian_product_integrable (s : ℝ) (hs : 0 < s) (z w : ℝ × ℝ) :
    Integrable (fun u : ℝ × ℝ =>
      Real.exp (-2*s*((z.1-u.1)^2+(z.2-u.2)^2)) *
      Real.exp (-2*s*((w.1-u.1)^2+(w.2-u.2)^2))) := by
  have shifted (a : ℝ) : Integrable (fun x : ℝ =>
      Real.exp (-(4*s)*(x-a)^2)) :=
    (integrable_exp_neg_mul_sq (by positivity : 0 < 4*s)).comp_sub_right a
  have h := ((shifted ((z.1+w.1)/2)).mul_prod (shifted ((z.2+w.2)/2))).const_mul
    (Real.exp (-s*((z.1-w.1)^2+(z.2-w.2)^2)))
  apply h.congr
  filter_upwards with u
  repeat rw [← Real.exp_add]
  congr 1
  ring

open MeasureTheory in
/-- Gaussian kernels have nonnegative energy for arbitrary finite signed
configurations in the plane. This is the finite-measure analogue of `J(s) ≥ 0`
in Lemma 6.2; no mass-zero or sign restriction on the coefficients is required. -/
theorem gaussian_finite_energy_nonneg {ι : Type*} [Fintype ι]
    (s : ℝ) (hs : 0 < s) (z : ι → ℝ × ℝ) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j *
      Real.exp (-s * (((z i).1-(z j).1)^2 + ((z i).2-(z j).2)^2)) := by
  let g : ι → (ℝ × ℝ) → ℝ := fun i u =>
    Real.exp (-2*s*(((z i).1-u.1)^2+((z i).2-u.2)^2))
  have hint (i j : ι) : Integrable (fun u => (c i*c j)*(g i u*g j u)) :=
    (gaussian_product_integrable s hs (z i) (z j)).const_mul (c i*c j)
  have hsquare (u : ℝ × ℝ) : (∑ i, c i*g i u)^2 =
      ∑ i, ∑ j, (c i*c j)*(g i u*g j u) := by
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have heq : (∫ u : ℝ × ℝ, (∑ i, c i*g i u)^2) =
      Real.pi/(4*s) * ∑ i, ∑ j, c i*c j*
        Real.exp (-s*(((z i).1-(z j).1)^2+((z i).2-(z j).2)^2)) := by
    simp_rw [hsquare]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => hint i j)]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_const_mul]
    change (c i*c j)*(∫ u : ℝ × ℝ,
      Real.exp (-2*s*(((z i).1-u.1)^2+((z i).2-u.2)^2)) *
      Real.exp (-2*s*(((z j).1-u.1)^2+((z j).2-u.2)^2))) = _
    rw [gaussian_convolution s hs (z i) (z j)]
    ring
  have hnonneg : 0 ≤ ∫ u : ℝ × ℝ, (∑ i, c i*g i u)^2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  rw [heq] at hnonneg
  exact (mul_nonneg_iff_of_pos_left (by positivity : 0 < Real.pi/(4*s))).mp hnonneg

open MeasureTheory in
/-- Nonnegative Gaussian energy for every integrable real density against any
sigma-finite positive measure on the plane. This is the measure-theoretic
`J(s) ≥ 0` step of Lemma 6.2, including justification of Fubini. -/
theorem gaussian_energy_nonneg
    (μ : Measure (ℝ × ℝ)) [SFinite μ] (f : (ℝ × ℝ) → ℝ)
    (hf : Integrable f μ) (s : ℝ) (hs : 0 < s) :
    0 ≤ ∫ p : (ℝ × ℝ) × (ℝ × ℝ), f p.1*f p.2*
      Real.exp (-s*((p.1.1-p.2.1)^2+(p.1.2-p.2.2)^2)) ∂μ.prod μ := by
  let g : (ℝ × ℝ) → (ℝ × ℝ) → ℝ := fun z u =>
    Real.exp (-2*s*((z.1-u.1)^2+(z.2-u.2)^2))
  let H : ((ℝ × ℝ) × (ℝ × ℝ)) → (ℝ × ℝ) → ℝ := fun p u =>
    (f p.1*f p.2)*(g p.1 u*g p.2 u)
  let C : ℝ := Real.pi/(4*s)
  have hC : 0 < C := by dsimp [C]; positivity
  have hbase : Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => f p.1*f p.2) (μ.prod μ) :=
    hf.mul_prod hf
  have hcont : Continuous (fun q : (((ℝ × ℝ) × (ℝ × ℝ)) × (ℝ × ℝ)) =>
      g q.1.1 q.2*g q.1.2 q.2) := by unfold g; fun_prop
  have hHm : AEStronglyMeasurable (Function.uncurry H) ((μ.prod μ).prod volume) :=
    hbase.aestronglyMeasurable.comp_fst.mul hcont.aestronglyMeasurable
  have hnorm (p : (ℝ × ℝ) × (ℝ × ℝ)) :
      (∫ u : ℝ × ℝ, ‖H p u‖) =
      ‖f p.1*f p.2‖*(C*Real.exp (-s*((p.1.1-p.2.1)^2+(p.1.2-p.2.2)^2))) := by
    have hpoint (u : ℝ × ℝ) : ‖H p u‖ = ‖f p.1*f p.2‖*(g p.1 u*g p.2 u) := by
      change ‖(f p.1*f p.2)*(g p.1 u*g p.2 u)‖ = _
      rw [norm_mul]
      congr 1
      exact Real.norm_of_nonneg (by dsimp [g]; positivity)
    simp_rw [hpoint]
    rw [integral_const_mul]
    change _ * (∫ u : ℝ × ℝ,
      Real.exp (-2*s*((p.1.1-u.1)^2+(p.1.2-u.2)^2))*
      Real.exp (-2*s*((p.2.1-u.1)^2+(p.2.2-u.2)^2))) = _
    rw [gaussian_convolution s hs p.1 p.2]
  have hH : Integrable (Function.uncurry H) ((μ.prod μ).prod volume) := by
    apply (integrable_prod_iff hHm).2
    constructor
    · filter_upwards with p
      exact (gaussian_product_integrable s hs p.1 p.2).const_mul (f p.1*f p.2)
    · apply (hbase.norm.const_mul C).mono' hHm.norm.integral_prod_right'
      filter_upwards with p
      change |∫ u : ℝ × ℝ, ‖H p u‖| ≤ C * ‖f p.1*f p.2‖
      rw [abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _)), hnorm]
      have he : Real.exp (-s*((p.1.1-p.2.1)^2+(p.1.2-p.2.2)^2)) ≤ 1 := by
        apply Real.exp_le_one_iff.2
        nlinarith [sq_nonneg (p.1.1-p.2.1),sq_nonneg (p.1.2-p.2.2)]
      have hm := mul_le_mul_of_nonneg_left he
        (mul_nonneg hC.le (norm_nonneg (f p.1*f p.2)))
      nlinarith
  have hswap := integral_integral_swap hH
  have hleft : (∫ p, ∫ u, H p u ∂volume ∂μ.prod μ) =
      C * ∫ p, f p.1*f p.2*
        Real.exp (-s*((p.1.1-p.2.1)^2+(p.1.2-p.2.2)^2)) ∂μ.prod μ := by
    simp_rw [H, integral_const_mul]
    simp_rw [g, gaussian_convolution s hs]
    rw [← integral_const_mul]
    congr 1
    funext p
    dsimp [C]
    ring
  have hright : (∫ u, ∫ p, H p u ∂μ.prod μ ∂volume) =
      ∫ u : ℝ × ℝ, (∫ z, f z*g z u ∂μ)^2 := by
    apply integral_congr_ae
    filter_upwards with u
    have hp : (fun p => H p u) = (fun p => (f p.1*g p.1 u)*(f p.2*g p.2 u)) := by
      funext p
      dsimp [H]
      ring
    rw [hp, integral_prod_mul (fun z => f z*g z u) (fun z => f z*g z u)]
    ring
  rw [hleft, hright] at hswap
  have hnonneg : 0 ≤ ∫ u : ℝ × ℝ, (∫ z, f z*g z u ∂μ)^2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  rw [← hswap] at hnonneg
  exact (mul_nonneg_iff_of_pos_left hC).mp hnonneg


open Real Set Filter MeasureTheory intervalIntegral
/-- Frullani's logarithm formula with positive ordered parameters. -/
theorem frullani_ordered {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntegrableOn (fun s : ℝ => (Real.exp (-a*s)-Real.exp (-b*s))/s) (Ioi 0) ∧
    (∫ s : ℝ in Ioi 0, (Real.exp (-a*s)-Real.exp (-b*s))/s) =
      Real.log b-Real.log a := by
  have hb : 0 < b := ha.trans_le hab
  have hi (v : ℝ) (hv : 0 < v) :
      (∫ s : ℝ in Ioi 0, Real.exp (-v*s)) = 1/v := by
    rw [integral_exp_mul_Ioi (by linarith : -v < 0) 0]
    simp
  have hinv : IntegrableOn (fun v : ℝ => 1/v) (Icc a b) := by
    apply ContinuousOn.integrableOn_Icc
    exact continuousOn_const.div continuousOn_id (fun v hv => ne_of_gt (ha.trans_le hv.1))
  have hsm : AEStronglyMeasurable (fun p : ℝ × ℝ => Real.exp (-p.1*p.2))
      ((volume.restrict (Icc a b)).prod (volume.restrict (Ioi 0))) := by
    apply Continuous.aestronglyMeasurable
    fun_prop
  have hint : Integrable (fun p : ℝ × ℝ => Real.exp (-p.1*p.2))
      ((volume.restrict (Icc a b)).prod (volume.restrict (Ioi 0))) := by
    apply (integrable_prod_iff hsm).2
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
      exact integrableOn_exp_mul_Ioi (by linarith [hv.1] : -v < 0) 0
    · apply hinv.congr
      filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
      simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact (hi v (ha.trans_le hv.1)).symm
  have hv (s : ℝ) (hs : 0 < s) :
      (∫ v : ℝ in Icc a b, Real.exp (-v*s)) =
      (Real.exp (-a*s)-Real.exp (-b*s))/s := by
    rw [integral_Icc_eq_integral_Ioc, ← integral_of_le hab]
    have he : (fun v : ℝ => Real.exp (-v*s)) = (fun v : ℝ => Real.exp ((-s)*v)) := by
      funext v
      congr 1
      ring
    rw [he, integral_comp_mul_left _ (by linarith : -s ≠ 0), integral_exp]
    simp only [smul_eq_mul]
    field_simp [ne_of_gt hs]
    ring
  have hae : (fun s : ℝ => ∫ v : ℝ in Icc a b, Real.exp (-v*s)) =ᶠ[ae (volume.restrict (Ioi 0))]
      (fun s : ℝ => (Real.exp (-a*s)-Real.exp (-b*s))/s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact hv s hs
  refine ⟨hint.integral_prod_right.congr hae, ?_⟩
  rw [← MeasureTheory.integral_congr_ae hae, ← integral_integral_swap hint]
  calc
    _ = ∫ v : ℝ in Icc a b, 1/v := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
      exact hi v (ha.trans_le hv.1)
    _ = ∫ v : ℝ in a..b, 1/v := by rw [integral_Icc_eq_integral_Ioc, integral_of_le hab]
    _ = Real.log (b/a) := integral_one_div (by
      rw [uIcc_of_le hab]
      intro h
      linarith [h.1])
    _ = Real.log b-Real.log a := Real.log_div (ne_of_gt hb) (ne_of_gt ha)

/-- Frullani's formula for all positive parameters, with absolute convergence. -/
theorem frullani {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun s : ℝ => (Real.exp (-a*s)-Real.exp (-b*s))/s) (Ioi 0) ∧
    (∫ s : ℝ in Ioi 0, (Real.exp (-a*s)-Real.exp (-b*s))/s) =
      Real.log b-Real.log a := by
  rcases le_total a b with hab | hba
  · exact frullani_ordered ha hab
  · obtain ⟨hi, he⟩ := frullani_ordered hb hba
    have hneg : (fun s : ℝ => (Real.exp (-a*s)-Real.exp (-b*s))/s) =
        (fun s : ℝ => -((Real.exp (-b*s)-Real.exp (-a*s))/s)) := by
      funext s
      ring
    rw [hneg]
    exact ⟨hi.neg, by rw [MeasureTheory.integral_neg, he]; ring⟩

/-- The logarithmic difference kernel has constant sign, so its absolute
integral is exactly the absolute logarithmic difference. -/
theorem frullani_abs {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ s : ℝ in Ioi 0, |(Real.exp (-a*s)-Real.exp (-b*s))/s|) =
      |Real.log b-Real.log a| := by
  rcases le_total a b with hab | hba
  · have hlog : 0 ≤ Real.log b-Real.log a := sub_nonneg.2 (Real.log_le_log ha hab)
    rw [abs_of_nonneg hlog, ← (frullani ha hb).2]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    apply abs_of_nonneg
    apply div_nonneg _ hs.le
    apply sub_nonneg.2
    apply Real.exp_le_exp.2
    exact mul_le_mul_of_nonneg_right (neg_le_neg hab) hs.le
  · have hlog : Real.log b-Real.log a ≤ 0 := sub_nonpos.2 (Real.log_le_log hb hba)
    rw [abs_of_nonpos hlog, ← (frullani ha hb).2, ← MeasureTheory.integral_neg]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    apply abs_of_nonpos
    apply div_nonpos_of_nonpos_of_nonneg _ hs.le
    apply sub_nonpos.2
    apply Real.exp_le_exp.2
    exact mul_le_mul_of_nonneg_right (neg_le_neg hba) hs.le


/-- Squared Euclidean distance, kept explicit to avoid log(0) conventions. -/
def planeDistSq (z w : ℝ × ℝ) : ℝ := (z.1-w.1)^2+(z.2-w.2)^2

/-- Zero-mass logarithmic energy is nonpositive. The logarithm is of squared
Euclidean distance, hence this integral is twice the usual logarithmic energy.
The explicit off-diagonal condition is necessary because Lean defines log 0 = 0.
A density against a positive measure represents the finite signed measure.
No compact-support assumption is needed once the indicated integrability holds. -/
theorem zero_mass_log_energy_nonpos
    (μ : Measure (ℝ × ℝ)) [SFinite μ] (f : (ℝ × ℝ) → ℝ)
    (hf : Integrable f μ) (hmass : (∫ z, f z ∂μ) = 0)
    (hdiag : ∀ᵐ p : (ℝ × ℝ) × (ℝ × ℝ) ∂μ.prod μ, 0 < planeDistSq p.1 p.2)
    (hlog : Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      f p.1*f p.2*Real.log (planeDistSq p.1 p.2)) (μ.prod μ)) :
    (∫ p : (ℝ × ℝ) × (ℝ × ℝ),
      f p.1*f p.2*Real.log (planeDistSq p.1 p.2) ∂μ.prod μ) ≤ 0 := by
  let H : ((ℝ × ℝ) × (ℝ × ℝ)) → ℝ → ℝ := fun p s =>
    (f p.1*f p.2)*((Real.exp (-s)-Real.exp (-planeDistSq p.1 p.2*s))/s)
  have hbase : Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => f p.1*f p.2) (μ.prod μ) :=
    hf.mul_prod hf
  have hkm : Measurable (fun q : (((ℝ × ℝ) × (ℝ × ℝ)) × ℝ) =>
      (Real.exp (-q.2)-Real.exp (-planeDistSq q.1.1 q.1.2*q.2))/q.2) := by
    dsimp [planeDistSq]
    fun_prop
  have hHm : AEStronglyMeasurable (Function.uncurry H)
      ((μ.prod μ).prod (volume.restrict (Ioi 0))) :=
    hbase.aestronglyMeasurable.comp_fst.mul hkm.aestronglyMeasurable
  have hH : Integrable (Function.uncurry H)
      ((μ.prod μ).prod (volume.restrict (Ioi 0))) := by
    apply (integrable_prod_iff hHm).2
    constructor
    · filter_upwards [hdiag] with p hp
      have hi := (frullani (by norm_num : (0 : ℝ) < 1) hp).1.const_mul (f p.1*f p.2)
      simpa only [neg_one_mul, H, Function.uncurry] using hi
    · apply hlog.norm.congr
      filter_upwards [hdiag] with p hp
      change ‖f p.1*f p.2*Real.log (planeDistSq p.1 p.2)‖ = ∫ s : ℝ in Ioi 0, ‖H p s‖
      simp_rw [H, norm_mul, Real.norm_eq_abs]
      rw [MeasureTheory.integral_const_mul]
      have he := frullani_abs (by norm_num : (0 : ℝ) < 1) hp
      simp only [neg_one_mul, Real.log_one, sub_zero] at he
      rw [he]
  have hswap := MeasureTheory.integral_integral_swap hH
  have hleft : (∫ p, (∫ s : ℝ in Ioi 0, H p s) ∂μ.prod μ) =
      ∫ p, f p.1*f p.2*Real.log (planeDistSq p.1 p.2) ∂μ.prod μ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hdiag] with p hp
    simp only [H, MeasureTheory.integral_const_mul]
    have he := (frullani (by norm_num : (0 : ℝ) < 1) hp).2
    simp only [neg_one_mul, Real.log_one, sub_zero] at he
    rw [he]
  rw [hleft] at hswap
  rw [hswap]
  apply MeasureTheory.integral_nonpos_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  change 0 < s at hs
  have hgaussm : AEStronglyMeasurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      f p.1*f p.2*Real.exp (-planeDistSq p.1 p.2*s)) (μ.prod μ) := by
    apply hbase.aestronglyMeasurable.mul
    apply Continuous.aestronglyMeasurable
    dsimp [planeDistSq]
    fun_prop
  have hgaussi : Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      f p.1*f p.2*Real.exp (-planeDistSq p.1 p.2*s)) (μ.prod μ) := by
    apply hbase.norm.mono' hgaussm
    filter_upwards with p
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
    apply mul_le_of_le_one_right (norm_nonneg _)
    apply Real.exp_le_one_iff.2
    dsimp [planeDistSq]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2
      (add_nonneg (sq_nonneg _) (sq_nonneg _))) hs.le
  have heq : (fun p => H p s) = (fun p =>
      (Real.exp (-s)*(f p.1*f p.2)-f p.1*f p.2*Real.exp (-planeDistSq p.1 p.2*s))/s) := by
    funext p
    dsimp [H]
    ring
  rw [heq, MeasureTheory.integral_div,
    MeasureTheory.integral_sub (hbase.const_mul _) hgaussi,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_prod_mul f f, hmass]
  simp only [mul_zero, zero_sub]
  apply div_nonpos_of_nonpos_of_nonneg _ hs.le
  apply neg_nonpos.2
  have heint : (∫ p : (ℝ × ℝ) × (ℝ × ℝ),
      f p.1*f p.2*Real.exp (-planeDistSq p.1 p.2*s) ∂μ.prod μ) =
      ∫ p : (ℝ × ℝ) × (ℝ × ℝ), f p.1*f p.2*
        Real.exp (-s*((p.1.1-p.2.1)^2+(p.1.2-p.2.2)^2)) ∂μ.prod μ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with p
    congr 2
    dsimp [planeDistSq]
    ring
  rw [heint]
  exact gaussian_energy_nonneg μ f hf s hs

/-- A nonatomic measure gives the off-diagonal condition required above. -/
theorem positive_distance_ae (μ : Measure (ℝ × ℝ)) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ p : (ℝ × ℝ) × (ℝ × ℝ) ∂μ.prod μ, 0 < planeDistSq p.1 p.2 := by
  have hne : ∀ᵐ p : (ℝ × ℝ) × (ℝ × ℝ) ∂μ.prod μ, p.1 ≠ p.2 := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_eq_fun measurable_fst measurable_snd).compl).2
    filter_upwards with z
    rw [ae_iff]
    simp
  filter_upwards [hne] with p hp
  by_contra h
  have hle : planeDistSq p.1 p.2 ≤ 0 := le_of_not_gt h
  have hx : p.1.1 = p.2.1 := by
    dsimp [planeDistSq] at hle
    nlinarith [sq_nonneg (p.1.1-p.2.1), sq_nonneg (p.1.2-p.2.2)]
  have hy : p.1.2 = p.2.2 := by
    dsimp [planeDistSq] at hle
    nlinarith [sq_nonneg (p.1.1-p.2.1), sq_nonneg (p.1.2-p.2.2)]
  exact hp (Prod.ext hx hy)

/-- The usual log-distance version of the zero-mass energy inequality. -/
theorem zero_mass_log_distance_energy_nonpos
    (μ : Measure (ℝ × ℝ)) [SFinite μ] (f : (ℝ × ℝ) → ℝ)
    (hf : Integrable f μ) (hmass : (∫ z, f z ∂μ) = 0)
    (hdiag : ∀ᵐ p : (ℝ × ℝ) × (ℝ × ℝ) ∂μ.prod μ, 0 < planeDistSq p.1 p.2)
    (hlog : Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      f p.1*f p.2*Real.log (Real.sqrt (planeDistSq p.1 p.2))) (μ.prod μ)) :
    (∫ p : (ℝ × ℝ) × (ℝ × ℝ),
      f p.1*f p.2*Real.log (Real.sqrt (planeDistSq p.1 p.2)) ∂μ.prod μ) ≤ 0 := by
  have hpoint (p : (ℝ × ℝ) × (ℝ × ℝ)) :
      f p.1*f p.2*Real.log (planeDistSq p.1 p.2) =
        2*(f p.1*f p.2*Real.log (Real.sqrt (planeDistSq p.1 p.2))) := by
    rw [Real.log_sqrt (by dsimp [planeDistSq]; positivity)]
    ring
  have hsq : Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      f p.1*f p.2*Real.log (planeDistSq p.1 p.2)) (μ.prod μ) := by
    simpa only [hpoint] using hlog.const_mul 2
  have h := zero_mass_log_energy_nonpos μ f hf hmass hdiag hsq
  simp_rw [hpoint] at h
  rw [MeasureTheory.integral_const_mul] at h
  linarith

#print axioms total_mass
#print axioms component_properties
#print axioms intervals_nested
#print axioms tail_field_bound
#print axioms gaussian_convolution
#print axioms gaussian_energy_nonneg
#print axioms frullani
#print axioms frullani_abs
#print axioms zero_mass_log_energy_nonpos
#print axioms positive_distance_ae
#print axioms zero_mass_log_distance_energy_nonpos
end Zeta5RealEnergy
