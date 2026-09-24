import FarUnitExpansion
import AnalyticFarPoles
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Inverse

namespace Zeta5Local
open Polynomial Filter Topology IsUltrametricDist
open scoped PowerSeries.WithPiTopology
variable {p : ℕ} [Fact p.Prime]

noncomputable def weightedPolynomialSeries (U : ℕ → Polynomial ℚ_[p]) : PowerSeries ℚ_[p] :=
  ∑' j : ℕ, ((C ((p : ℚ_[p]) ^ j) * U j : Polynomial ℚ_[p]) : PowerSeries ℚ_[p])

lemma weightedPolynomialSeries_summable (U : ℕ → Polynomial ℚ_[p])
    (hU : ∀ j n, ‖(U j).coeff n‖ ≤ 1) :
    Summable (fun j : ℕ => ((C ((p : ℚ_[p]) ^ j) * U j : Polynomial ℚ_[p]) :
      PowerSeries ℚ_[p])) := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro n
  simp only [coeff_coe, coeff_C_mul]
  exact bounded_kernel_summable _ _ 1
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one) (fun j => hU j n)

lemma weightedPolynomialSeries_coeff (U : ℕ → Polynomial ℚ_[p])
    (hU : ∀ j n, ‖(U j).coeff n‖ ≤ 1) (n : ℕ) :
    PowerSeries.coeff n (weightedPolynomialSeries U) =
      ∑' j : ℕ, (p : ℚ_[p]) ^ j * (U j).coeff n := by
  have h := (PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff ℚ_[p]).mp
    (weightedPolynomialSeries_summable U hU).hasSum n
  simpa only [weightedPolynomialSeries, coeff_coe, coeff_C_mul] using h.tsum_eq.symm

lemma weightedPolynomialSeries_division (U : ℕ → Polynomial ℚ_[p])
    (T : Polynomial ℚ_[p]) (hT : T.Monic)
    (hU : ∀ j n, ‖(U j).coeff n‖ ≤ 1) (hTc : ∀ n, ‖T.coeff n‖ ≤ 1) :
    (T : PowerSeries ℚ_[p]) * weightedPolynomialSeries (fun j => U j /ₘ T) +
      weightedPolynomialSeries (fun j => U j %ₘ T) = weightedPolynomialSeries U := by
  have hq (j n : ℕ) : ‖(U j /ₘ T).coeff n‖ ≤ 1 :=
    (integral_monic_division (U j) T hT (hU j) hTc).1 n
  have hr (j n : ℕ) : ‖(U j %ₘ T).coeff n‖ ≤ 1 :=
    (integral_monic_division (U j) T hT (hU j) hTc).2 n
  have hqs := weightedPolynomialSeries_summable _ hq
  have hrs := weightedPolynomialSeries_summable _ hr
  unfold weightedPolynomialSeries
  rw [← hqs.tsum_mul_left, ← (hqs.mul_left (T : PowerSeries ℚ_[p])).tsum_add hrs]
  apply tsum_congr
  intro j
  rw [← Polynomial.coe_mul, ← Polynomial.coe_add]
  congr 1
  have he := modByMonic_add_div (U j) T
  linear_combination C ((p : ℚ_[p]) ^ j) * he

/-- A row-finite family with uniform decay in its first index is summable
in a nonarchimedean field. No bound on the row support sizes is needed. -/
lemma summable_row_finite (f : ℕ × ℕ → ℚ_[p]) (s : ℕ → Finset ℕ) (b : ℕ → ℝ)
    (hb : Tendsto b atTop (𝓝 0))
    (hz : ∀ j n, n ∉ s j → f (j, n) = 0)
    (hf : ∀ j n, ‖f (j, n)‖ ≤ b j) : Summable f := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hb.eventually (Iio_mem_nhds hε))
  rw [eventually_cofinite]
  apply ((Finset.range N).biUnion (fun j => ({j} : Finset ℕ) ×ˢ s j)).finite_toSet.subset
  rintro ⟨j, n⟩ hbad
  by_contra hnot
  apply hbad
  rw [dist_zero_right]
  by_cases hj : N ≤ j
  · exact (hf j n).trans_lt (hN j hj)
  · have hn : n ∉ s j := by
      intro hn
      apply hnot
      simp only [Finset.mem_coe, Finset.mem_biUnion, Finset.mem_range, Finset.mem_product,
        Finset.mem_singleton]
      exact ⟨j, by omega, rfl, hn⟩
    rw [hz j n hn, norm_zero]
    exact hε

lemma polynomial_kernel_double_summable (hp7 : 7 ≤ p) (U : ℕ → Polynomial ℚ_[p])
    (hU : ∀ j n, ‖(U j).coeff n‖ ≤ 1) :
    Summable (fun jn : ℕ × ℕ => (p : ℚ_[p]) ^ jn.1 * (U jn.1).coeff jn.2 *
      (rationalTauMoment jn.2 : ℚ_[p])) := by
  apply summable_row_finite _ (fun j => (U j).support) (fun j => ‖(p : ℚ_[p])‖ ^ j * p)
  · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (p : ℚ_[p]))
      Padic.norm_p_lt_one).mul_const (p : ℝ)
  · intro j n hn
    simp [notMem_support_iff.mp hn]
  · intro j n
    rw [norm_mul, norm_mul, norm_pow]
    exact mul_le_mul
      (mul_le_of_le_one_right (by positivity) (hU j n))
      (rationalTauMoment_norm hp7 n) (norm_nonneg _) (by positivity)

noncomputable def tauPowerSeries (F : PowerSeries ℚ_[p]) : ℚ_[p] :=
  ∑' n : ℕ, PowerSeries.coeff n F * (rationalTauMoment n : ℚ_[p])

/-- The bounded Bernoulli kernel commutes with every integral p-weighted
polynomial approximation. This is the continuity bridge used for rational
functions with far-unit denominators. -/
theorem tauPowerSeries_weighted (hp7 : 7 ≤ p) (U : ℕ → Polynomial ℚ_[p])
    (hU : ∀ j n, ‖(U j).coeff n‖ ≤ 1) :
    tauPowerSeries (weightedPolynomialSeries U) =
      ∑' j : ℕ, (p : ℚ_[p]) ^ j * tauPolynomial (U j) := by
  unfold tauPowerSeries
  simp_rw [weightedPolynomialSeries_coeff U hU, ← tsum_mul_right]
  let f : ℕ → ℕ → ℚ_[p] := fun j n => (p : ℚ_[p]) ^ j * (U j).coeff n *
    (rationalTauMoment n : ℚ_[p])
  have hs : Summable (Function.uncurry f) := polynomial_kernel_double_summable hp7 U hU
  have hc := Summable.tsum_comm (f := f) hs
  change (∑' n : ℕ, ∑' j : ℕ, (p : ℚ_[p]) ^ j * (U j).coeff n *
    (rationalTauMoment n : ℚ_[p])) = _ at hc
  rw [hc]
  apply tsum_congr
  intro j
  change (∑' n : ℕ, (p : ℚ_[p]) ^ j * (U j).coeff n *
    (rationalTauMoment n : ℚ_[p])) = _
  rw [tsum_eq_sum (s := (U j).support) (fun n hn => by
    simp [notMem_support_iff.mp hn])]
  simp only [tauPolynomial, Finset.mul_sum, mul_assoc]

#print axioms tauPowerSeries_weighted
end Zeta5Local
