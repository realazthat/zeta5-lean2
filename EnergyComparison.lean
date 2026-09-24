import RealEnergy
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Zeta5RealEnergy

section Density
variable {α : Type*} [MeasurableSpace α]

/-- Change both factors of a kernel integral using Radon–Nikodym densities. -/
theorem rn_product_integral (μ ν η : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure η]
    (hμ : μ ≪ η) (hν : ν ≪ η) (k : α × α → ℝ)
    (hk : Integrable k (μ.prod ν)) :
    Integrable (fun z => (μ.rnDeriv η z.1).toReal *
      (ν.rnDeriv η z.2).toReal * k z) (η.prod η) ∧
    (∫ z, (μ.rnDeriv η z.1).toReal * (ν.rnDeriv η z.2).toReal * k z ∂η.prod η) =
      ∫ z, k z ∂μ.prod ν := by
  let d : α × α → ℝ≥0∞ := fun z => μ.rnDeriv η z.1 * ν.rnDeriv η z.2
  have hd : Measurable d :=
    ((Measure.measurable_rnDeriv μ η).comp measurable_fst).mul
      ((Measure.measurable_rnDeriv ν η).comp measurable_snd)
  have ht : ∀ᵐ z ∂η.prod η, d z < ∞ := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (Measure.rnDeriv_lt_top μ η),
      Measure.quasiMeasurePreserving_snd.ae (Measure.rnDeriv_lt_top ν η)] with z hz hw
    exact ENNReal.mul_lt_top hz hw
  have hwd : (η.prod η).withDensity d = μ.prod ν := by
    rw [← prod_withDensity (Measure.measurable_rnDeriv μ η)
      (Measure.measurable_rnDeriv ν η), Measure.withDensity_rnDeriv_eq μ η hμ,
      Measure.withDensity_rnDeriv_eq ν η hν]
  constructor
  · have hh := (integrable_withDensity_iff_integrable_smul' hd ht).mp (hwd ▸ hk)
    simpa only [d, ENNReal.toReal_mul, smul_eq_mul] using hh
  · have hh := integral_withDensity_eq_integral_toReal_smul hd ht k
    rw [hwd] at hh
    simpa only [d, ENNReal.toReal_mul, smul_eq_mul] using hh.symm

end Density

def logKernel (z : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  Real.log (Real.sqrt (planeDistSq z.1 z.2))

lemma logKernel_swap (z : (ℝ × ℝ) × (ℝ × ℝ)) : logKernel z.swap = logKernel z := by
  rcases z with ⟨⟨x,y⟩,⟨u,v⟩⟩
  dsimp [logKernel, planeDistSq]
  congr 2
  ring

/-- The finite-positive-measure form of the logarithmic-energy comparison.
The diagonal condition is explicit because Lean defines `log 0 = 0`. -/
theorem measure_energy_comparison (μ ν : Measure (ℝ × ℝ))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmass : μ Set.univ = ν Set.univ)
    (hdiag : ∀ᵐ z ∂(μ+ν).prod (μ+ν), 0 < planeDistSq z.1 z.2)
    (hk : Integrable logKernel ((μ+ν).prod (μ+ν))) :
    (∫ z, logKernel z ∂μ.prod μ) + (∫ z, logKernel z ∂ν.prod ν) ≤
      2 * ∫ z, logKernel z ∂μ.prod ν := by
  let η := μ+ν
  let a := fun z => (μ.rnDeriv η z).toReal
  let b := fun z => (ν.rnDeriv η z).toReal
  have hμle : μ ≤ η := Measure.le_add_right le_rfl
  have hνle : ν ≤ η := Measure.le_add_left le_rfl
  have hμ : μ ≪ η := hμle.absolutelyContinuous
  have hν : ν ≪ η := hνle.absolutelyContinuous
  have ha : Integrable a η := by
    simpa [a] using (Measure.integrableOn_toReal_rnDeriv (μ := μ) (ν := η)
      (s := Set.univ) (measure_ne_top _ _))
  have hb : Integrable b η := by
    simpa [b] using (Measure.integrableOn_toReal_rnDeriv (μ := ν) (ν := η)
      (s := Set.univ) (measure_ne_top _ _))
  have h11 := rn_product_integral μ μ η hμ hμ logKernel
    (hk.mono_measure (Measure.prod_mono hμle hμle))
  have h12 := rn_product_integral μ ν η hμ hν logKernel
    (hk.mono_measure (Measure.prod_mono hμle hνle))
  have h21 := rn_product_integral ν μ η hν hμ logKernel
    (hk.mono_measure (Measure.prod_mono hνle hμle))
  have h22 := rn_product_integral ν ν η hν hν logKernel
    (hk.mono_measure (Measure.prod_mono hνle hνle))
  have hfzero : (∫ z, a z-b z ∂η) = 0 := by
    rw [integral_sub ha hb, Measure.integral_toReal_rnDeriv hμ,
      Measure.integral_toReal_rnDeriv hν]
    simp [measureReal_def, hmass]
  have hint : Integrable (fun z => (a z.1-b z.1)*(a z.2-b z.2)*logKernel z)
      (η.prod η) := by
    apply (((h11.1.sub h12.1).sub h21.1).add h22.1).congr
    filter_upwards [] with z
    dsimp [a,b]
    ring
  have hn := zero_mass_log_distance_energy_nonpos η (fun z => a z-b z)
    (ha.sub hb) hfzero hdiag hint
  have he : (∫ z, (a z.1-b z.1)*(a z.2-b z.2)*logKernel z ∂η.prod η) =
      (∫ z, logKernel z ∂μ.prod μ) - (∫ z, logKernel z ∂μ.prod ν) -
      (∫ z, logKernel z ∂ν.prod μ) + (∫ z, logKernel z ∂ν.prod ν) := by
    have hp : (fun z => (a z.1-b z.1)*(a z.2-b z.2)*logKernel z) =
        (fun z => a z.1*a z.2*logKernel z - a z.1*b z.2*logKernel z -
          b z.1*a z.2*logKernel z + b z.1*b z.2*logKernel z) := by
      funext z
      ring
    rw [hp]
    dsimp only [a,b]
    have he1 := integral_add ((h11.1.sub h12.1).sub h21.1) h22.1
    have he2 := integral_sub (h11.1.sub h12.1) h21.1
    have he3 := integral_sub h11.1 h12.1
    simp only [Pi.sub_apply, Pi.add_apply] at he1 he2 he3
    rw [he1, he2, he3]
    rw [h11.2, h12.2, h21.2, h22.2]
  have hswap : (∫ z, logKernel z ∂ν.prod μ) = ∫ z, logKernel z ∂μ.prod ν := by
    rw [← integral_prod_swap]
    simp only [logKernel_swap]
  change (∫ z, (a z.1-b z.1)*(a z.2-b z.2)*logKernel z ∂η.prod η) ≤ 0 at hn
  rw [he, hswap] at hn
  linarith

#print axioms measure_energy_comparison

def complexPlaneEquiv : ℂ ≃ᵐ (ℝ × ℝ) :=
  Complex.equivRealProdCLM.toHomeomorph.toMeasurableEquiv

lemma logKernel_complex (z w : ℂ) :
    logKernel (complexPlaneEquiv z, complexPlaneEquiv w) = Real.log ‖z-w‖ := by
  rw [Complex.norm_def]
  congr 2
  simp [logKernel, complexPlaneEquiv, planeDistSq, Complex.normSq_apply, pow_two]

theorem null_singletons_map_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] (e : α ≃ᵐ β) (μ : Measure α) [NullSingletonClass μ] :
    NullSingletonClass (μ.map e) := by
  constructor
  intro z
  rw [Measure.map_apply e.measurable (measurableSet_singleton z)]
  have hp : e ⁻¹' ({z} : Set β) = {e.symm z} := by
    ext x
    change e x = z ↔ x = e.symm z
    exact ⟨fun h => by simpa using congrArg e.symm h,
      fun h => by rw [h, e.apply_symm_apply]⟩
  rw [hp, measure_singleton]

lemma complex_kernel_integral (μ ν : Measure ℂ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (∫ z, logKernel z ∂(μ.map complexPlaneEquiv).prod (ν.map complexPlaneEquiv)) =
      ∫ z : ℂ × ℂ, Real.log ‖z.1-z.2‖ ∂μ.prod ν := by
  rw [Measure.map_prod_map _ _ complexPlaneEquiv.measurable complexPlaneEquiv.measurable]
  change (∫ z, logKernel z ∂Measure.map
    (complexPlaneEquiv.prodCongr complexPlaneEquiv) (μ.prod ν)) = _
  rw [integral_map_equiv]
  congr 1
  funext z
  exact logKernel_complex z.1 z.2

lemma complex_kernel_integrable (μ ν : Measure ℂ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hk : Integrable (fun z : ℂ × ℂ => Real.log ‖z.1-z.2‖) (μ.prod ν)) :
    Integrable logKernel ((μ.map complexPlaneEquiv).prod (ν.map complexPlaneEquiv)) := by
  rw [Measure.map_prod_map _ _ complexPlaneEquiv.measurable complexPlaneEquiv.measurable]
  apply (complexPlaneEquiv.prodCongr complexPlaneEquiv).measurableEmbedding.integrable_map_iff.mpr
  change Integrable (fun z : ℂ × ℂ =>
    logKernel (complexPlaneEquiv z.1, complexPlaneEquiv z.2)) (μ.prod ν)
  simpa only [logKernel_complex] using hk

/-- The same comparison on the complex plane, directly usable with the
circle and arcsine probability measures. -/
theorem complex_measure_energy_comparison (μ ν : Measure ℂ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [NullSingletonClass μ] [NullSingletonClass ν]
    (hmass : μ Set.univ = ν Set.univ)
    (hk : Integrable (fun z : ℂ × ℂ => Real.log ‖z.1-z.2‖) ((μ+ν).prod (μ+ν))) :
    (∫ z : ℂ × ℂ, Real.log ‖z.1-z.2‖ ∂μ.prod μ) +
      (∫ z : ℂ × ℂ, Real.log ‖z.1-z.2‖ ∂ν.prod ν) ≤
      2 * ∫ z : ℂ × ℂ, Real.log ‖z.1-z.2‖ ∂μ.prod ν := by
  letI := null_singletons_map_equiv complexPlaneEquiv μ
  letI := null_singletons_map_equiv complexPlaneEquiv ν
  letI : NullSingletonClass (μ.map complexPlaneEquiv + ν.map complexPlaneEquiv) := by
    constructor
    intro z
    simp [Measure.add_apply]
  have hmass' : (μ.map complexPlaneEquiv) Set.univ = (ν.map complexPlaneEquiv) Set.univ := by
    simpa only [Measure.map_apply complexPlaneEquiv.measurable MeasurableSet.univ,
      preimage_univ] using hmass
  have hk' := complex_kernel_integrable (μ+ν) (μ+ν) hk
  rw [Measure.map_add μ ν complexPlaneEquiv.measurable] at hk'
  have hh := measure_energy_comparison (μ.map complexPlaneEquiv) (ν.map complexPlaneEquiv)
    hmass' (positive_distance_ae _) hk'
  simpa only [complex_kernel_integral] using hh

#print axioms complex_measure_energy_comparison

end Zeta5RealEnergy
