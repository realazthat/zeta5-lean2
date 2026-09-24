import PowerSeriesResidues

namespace Zeta5Local
open Polynomial Filter Topology
open scoped PowerSeries.WithPiTopology
variable {p : ℕ} [Fact p.Prime]
variable {ι : Type*} [DecidableEq ι]

lemma weighted_eval_sum_summable (U : ℕ → Polynomial ℚ_[p])
    (s : Finset ι) (r c : ι → ℚ_[p])
    (hU : ∀ j n, ‖(U j).coeff n‖ ≤ 1) (hr : ∀ i, ‖r i‖ ≤ 1) :
    Summable (fun j : ℕ => (p : ℚ_[p]) ^ j * ∑ i ∈ s, (U j).eval (r i) * c i) := by
  simp_rw [Finset.mul_sum, ← mul_assoc]
  exact summable_sum (fun i hi => (weighted_eval_summable U hU (r i) (hr i)).mul_right (c i))

lemma weighted_eval_finset_tsum (U : ℕ → Polynomial ℚ_[p])
    (s : Finset ι) (r c : ι → ℚ_[p])
    (hU : ∀ j n, ‖(U j).coeff n‖ ≤ 1) (hr : ∀ i, ‖r i‖ ≤ 1) :
    (∑' j : ℕ, (p : ℚ_[p]) ^ j * ∑ i ∈ s, (U j).eval (r i) * c i) =
      ∑ i ∈ s, (∑' j : ℕ, (p : ℚ_[p]) ^ j * (U j).eval (r i)) * c i := by
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Summable.tsum_finsetSum (fun i hi =>
    (weighted_eval_summable U hU (r i) (hr i)).mul_right (c i))]
  simp_rw [tsum_mul_right]

/-- The entire near-pole completion consists of its coefficient-completed
polynomial quotient and the convergent original numerator values at the poles. -/
theorem nearPoleSeries_as_powerSeries (hp7 : 7 ≤ p) (U : ℕ → Polynomial ℚ_[p])
    (s : Finset ι) (r : ι → ℚ_[p]) (d : ι → ℕ) (Y : ℚ_[p])
    (hU : ∀ j n, ‖(U j).coeff n‖ ≤ 1) (hr : ∀ i, ‖r i‖ ≤ 1) :
    (∑' j : ℕ, (p : ℚ_[p]) ^ j * nearPoleValue (U j) s r d Y) =
      tauPowerSeries (weightedPolynomialSeries (fun j => U j /ₘ poleDenominator s r)) +
      ∑ i ∈ s, ((∑' j : ℕ, (p : ℚ_[p]) ^ j * (U j).eval (r i)) /
        ∏ k ∈ s.erase i, (r i - r k)) * (localHarmonic (d i) - Y) := by
  have hq (j n : ℕ) : ‖(U j /ₘ poleDenominator s r).coeff n‖ ≤ 1 :=
    (integral_monic_division (U j) _ (poleDenominator_monic s r) (hU j)
      (poleDenominator_integral s r hr)).1 n
  have hqs : Summable (fun j => (p : ℚ_[p]) ^ j *
      tauPolynomial (U j /ₘ poleDenominator s r)) :=
    bounded_kernel_summable _ _ p
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one)
      (fun j => tauPolynomial_norm hp7 _ (hq j))
  let c (i : ι) := (∏ k ∈ s.erase i, (r i - r k))⁻¹ * (localHarmonic (d i) - Y)
  have hs := weighted_eval_sum_summable U s r c hU hr
  simp only [nearPoleValue, mul_add, div_eq_mul_inv, mul_assoc]
  rw [hqs.tsum_add hs, ← tauPowerSeries_weighted hp7 _ hq]
  congr 1
  exact weighted_eval_finset_tsum U s r c hU hr

/-- Polynomial-valued completion, retaining the affine parameter exactly. -/
theorem nearPolePolynomialSeries_as_powerSeries (hp7 : 7 ≤ p) (U : ℕ → Polynomial ℚ_[p])
    (s : Finset ι) (r : ι → ℚ_[p]) (d : ι → ℕ) (Y : Polynomial ℚ_[p])
    (hU : ∀ j n, ‖(U j).coeff n‖ ≤ 1) (hr : ∀ i, ‖r i‖ ≤ 1) :
    nearPolePolynomialSeries U s r d Y =
      C (tauPowerSeries (weightedPolynomialSeries (fun j => U j /ₘ poleDenominator s r))) +
        ∑ i ∈ s, C ((∑' j : ℕ, (p : ℚ_[p]) ^ j * (U j).eval (r i)) /
          ∏ k ∈ s.erase i, (r i - r k)) * (C (localHarmonic (d i)) - Y) := by
  rw [nearPolePolynomialSeries, nearPoleSeries_as_powerSeries hp7 U s r d 0 hU hr]
  simp only [sub_zero]
  have hs : (∑' j : ℕ, (p : ℚ_[p]) ^ j * nearPoleResidueSum (U j) s r) =
      ∑ i ∈ s, (∑' j : ℕ, (p : ℚ_[p]) ^ j * (U j).eval (r i)) /
        ∏ k ∈ s.erase i, (r i - r k) := by
    simp only [nearPoleResidueSum, div_eq_mul_inv]
    exact weighted_eval_finset_tsum U s r _ hU hr
  rw [hs]
  simp only [map_add, map_sum, map_mul, Finset.sum_mul, mul_sub, Finset.sum_sub_distrib]
  ring

#print axioms nearPolePolynomialSeries_as_powerSeries
end Zeta5Local
