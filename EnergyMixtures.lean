import CircleMeasures
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

namespace Zeta5EnergyMixtures
open MeasureTheory Real Metric Set
open Zeta5CirclePotential Zeta5CircleMeasures

noncomputable def logKernel (p : ℂ × ℂ) : ℝ := Real.log ‖p.1-p.2‖
noncomputable def mutualEnergy (μ ν : Measure ℂ) : ℝ := ∫ p, logKernel p ∂μ.prod ν
noncomputable def weightedMeasure {ι : Type*} (c : ι → ℝ) (μ : ι → Measure ℂ) : Measure ℂ :=
  Measure.sum (fun i => ENNReal.ofReal (c i) • μ i)

instance weightedMeasure_finite {ι : Type*} [Fintype ι] (c : ι → ℝ)
    (μ : ι → Measure ℂ) [∀ i, IsFiniteMeasure (μ i)] : IsFiniteMeasure (weightedMeasure c μ) := by
  unfold weightedMeasure
  haveI (i : ι) : IsFiniteMeasure (ENNReal.ofReal (c i) • μ i) :=
    (μ i).smul_finite ENNReal.ofReal_ne_top
  infer_instance

 theorem weightedMeasure_nullSingleton {ι : Type*} (c : ι → ℝ)
    (μ : ι → Measure ℂ) (hμ : ∀ i, NullSingletonClass (μ i)) :
    NullSingletonClass (weightedMeasure c μ) := by
  constructor
  intro z
  rw [weightedMeasure, Measure.sum_apply _ (measurableSet_singleton _)]
  have hz (i : ι) : (ENNReal.ofReal (c i) • μ i) {z} = 0 := by
    haveI := hμ i
    simp
  simp only [hz,tsum_zero]

 theorem weightedMeasure_mass {ι : Type*} [Fintype ι] (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)] :
    (weightedMeasure c μ).real univ = ∑ i, c i := by
  rw [measureReal_def, weightedMeasure, Measure.sum_apply _ MeasurableSet.univ, tsum_fintype]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [ENNReal.toReal_sum (by intro i _; finiteness)]
  apply Finset.sum_congr rfl
  intro i _
  exact ENNReal.toReal_ofReal (hc i)

 theorem integrable_weightedMeasure {ι : Type*} [Fintype ι] (c : ι → ℝ)
    (μ : ι → Measure ℂ) (f : ℂ → ℝ) (hf : ∀ i, Integrable f (μ i)) :
    Integrable f (weightedMeasure c μ) := by
  apply integrable_sum_measure (fun i => (hf i).smul_measure ENNReal.ofReal_ne_top)
  exact Summable.of_finite

 theorem integral_weightedMeasure {ι : Type*} [Fintype ι] (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (μ : ι → Measure ℂ) (f : ℂ → ℝ)
    (hf : ∀ i, Integrable f (μ i)) :
    (∫ z, f z ∂weightedMeasure c μ) = ∑ i, c i*(∫ z, f z ∂μ i) := by
  rw [weightedMeasure, integral_sum_measure (integrable_weightedMeasure c μ f hf), tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_smul_measure, ENNReal.toReal_ofReal (hc i), smul_eq_mul]

 theorem log_integrable_weighted_product {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → ℝ) (d : κ → ℝ) (μ : ι → Measure ℂ) (ν : κ → Measure ℂ)
    [∀ j, SFinite (ν j)]
    (hf : ∀ i j, Integrable logKernel ((μ i).prod (ν j))) :
    Integrable logKernel ((weightedMeasure c μ).prod (weightedMeasure d ν)) := by
  rw [weightedMeasure, weightedMeasure, Measure.prod_sum]
  apply integrable_sum_measure
  · intro p
    rw [Measure.prod_smul_left, Measure.prod_smul_right]
    exact ((hf p.1 p.2).smul_measure ENNReal.ofReal_ne_top).smul_measure ENNReal.ofReal_ne_top
  · exact Summable.of_finite

 theorem energy_weighted_product {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → ℝ) (d : κ → ℝ) (hc : ∀ i, 0 ≤ c i) (hd : ∀ j, 0 ≤ d j)
    (μ : ι → Measure ℂ) (ν : κ → Measure ℂ) [∀ j, SFinite (ν j)]
    (hf : ∀ i j, Integrable logKernel ((μ i).prod (ν j))) :
    mutualEnergy (weightedMeasure c μ) (weightedMeasure d ν) =
      ∑ i, ∑ j, c i*d j*mutualEnergy (μ i) (ν j) := by
  have hi := log_integrable_weighted_product c d μ ν hf
  unfold mutualEnergy
  rw [weightedMeasure, weightedMeasure, Measure.prod_sum] at hi ⊢
  rw [integral_sum_measure hi, tsum_fintype, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Measure.prod_smul_left, Measure.prod_smul_right,
    integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal (hc i), ENNReal.toReal_ofReal (hd j)]
  simp only [smul_eq_mul]
  ring

 theorem mutualEnergy_symm (μ ν : Measure ℂ) [SFinite μ] [SFinite ν]
    (hi : Integrable logKernel (μ.prod ν)) : mutualEnergy μ ν = mutualEnergy ν μ := by
  have hs : Integrable logKernel (ν.prod μ) := by
    have h := integrable_swap_iff.2 hi
    change Integrable (fun p : ℂ × ℂ => Real.log ‖p.2-p.1‖) (ν.prod μ) at h
    change Integrable (fun p : ℂ × ℂ => Real.log ‖p.1-p.2‖) (ν.prod μ)
    simpa only [norm_sub_rev] using h
  have hi' : Integrable (Function.uncurry (fun z w : ℂ => Real.log ‖z-w‖)) (μ.prod ν) := hi
  unfold mutualEnergy
  rw [integral_prod _ hi, integral_prod _ hs]
  change (∫ z : ℂ, ∫ w : ℂ, Real.log ‖z-w‖ ∂ν ∂μ) =
    ∫ w : ℂ, ∫ z : ℂ, Real.log ‖w-z‖ ∂μ ∂ν
  rw [integral_integral_swap hi']
  simp_rw [norm_sub_rev]

 theorem log_integrable_weighted_left {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (μ : ι → Measure ℂ) (ν : Measure ℂ) [SFinite ν]
    (hf : ∀ i, Integrable logKernel ((μ i).prod ν)) :
    Integrable logKernel ((weightedMeasure c μ).prod ν) := by
  rw [weightedMeasure, Measure.prod_sum_left]
  apply integrable_sum_measure
  · intro i
    rw [Measure.prod_smul_left]
    exact (hf i).smul_measure ENNReal.ofReal_ne_top
  · exact Summable.of_finite

 theorem energy_weighted_left {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (μ : ι → Measure ℂ)
    (ν : Measure ℂ) [SFinite ν]
    (hf : ∀ i, Integrable logKernel ((μ i).prod ν)) :
    mutualEnergy (weightedMeasure c μ) ν = ∑ i, c i*mutualEnergy (μ i) ν := by
  have hi := log_integrable_weighted_left c μ ν hf
  unfold mutualEnergy
  rw [weightedMeasure, Measure.prod_sum_left] at hi ⊢
  rw [integral_sum_measure hi,tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  rw [Measure.prod_smul_left,integral_smul_measure,ENNReal.toReal_ofReal (hc i),smul_eq_mul]

 theorem log_integrable_swap (μ ν : Measure ℂ) [SFinite μ] [SFinite ν]
    (hf : Integrable logKernel (μ.prod ν)) : Integrable logKernel (ν.prod μ) := by
  have h := integrable_swap_iff.2 hf
  change Integrable (fun p : ℂ × ℂ => Real.log ‖p.2-p.1‖) (ν.prod μ) at h
  change Integrable (fun p : ℂ × ℂ => Real.log ‖p.1-p.2‖) (ν.prod μ)
  simpa only [norm_sub_rev] using h

end Zeta5EnergyMixtures
