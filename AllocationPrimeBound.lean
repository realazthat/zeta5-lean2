import PrimeRangePartition
import OuterPrimeUpperLimit

noncomputable section
open Filter
open scoped Topology BigOperators
namespace Zeta5Parameters
open Zeta5PrimeSums

/-- The p/2 rounding loss has normalized global cost 1/36. -/
theorem prime_allocation_loss_tendsto :
    Tendsto (fun n : ℕ => weightedTheta ((K n:ℝ)/3)/2/(K n:ℝ)^2)
      atTop (𝓝 ((1:ℝ)/36)) := by
  have h := ((scaled_weightedTheta_ratio_tendsto chebyshev_asymptotic
    (by norm_num : (0:ℝ)<1/3)).div_const 2).comp K_tendsto_atTop
  norm_num only [Function.comp_def,one_div_mul_eq_div] at h
  convert h using 1
  · funext n
    ring

/-- Uniform eventual bound for the allocation loss, also applicable to any prime subinterval. -/
theorem prime_allocation_loss_eventually_upper (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, weightedTheta ((K n:ℝ)/3)/2/(K n:ℝ)^2≤1/36+ε := by
  exact (prime_allocation_loss_tendsto.eventually
    (gt_mem_nhds (by linarith : (1:ℝ)/36<1/36+ε))).mono (fun _ h => h.le)

theorem prime_allocation_interval_eventually_upper (a : ℕ→ℕ) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,
      (∑p∈Finset.Ioc (a n) ⌊(K n:ℝ)/3⌋₊ with p.Prime,(p:ℝ)/2*Real.log p)/(K n:ℝ)^2≤1/36+ε := by
  filter_upwards [prime_allocation_loss_eventually_upper ε hε] with n hn
  exact (div_le_div_of_nonneg_right (prime_allocation_sum_le (a n) ((K n:ℝ)/3))
    (sq_nonneg _)).trans hn

#print axioms prime_allocation_loss_tendsto
#print axioms prime_allocation_interval_eventually_upper
end Zeta5Parameters
