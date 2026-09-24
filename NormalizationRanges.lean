import PrimeRangePartition
import SmallPrimeAsymptotics
import InnerPrimeBound

noncomputable section
open Filter
open scoped BigOperators Topology
namespace Zeta5PrimeSums

lemma corrected_prime_range_partition (a b c d : ℕ) (hab : a≤b) (hbc : b≤c) (hcd : c≤d)
    (f g : ℕ→ℝ) :
    (∑ p ∈ Finset.Icc 0 d with p.Prime, f p)=
      (∑ p ∈ Finset.Icc 0 a with p.Prime, f p)+
      (∑ p ∈ Finset.Ioc a b with p.Prime, (f p-g p))+
      (∑ p ∈ Finset.Ioc b c with p.Prime, (f p-g p))+
      (∑ p ∈ Finset.Ioc c d with p.Prime, f p)+
      (∑ p ∈ Finset.Ioc a c with p.Prime, g p) := by
  rw [prime_sum_Ioc_eq_difference a b hab,prime_sum_Ioc_eq_difference b c hbc,
    prime_sum_Ioc_eq_difference c d hcd,prime_sum_Ioc_eq_difference a c (hab.trans hbc)]
  simp only [Finset.sum_sub_distrib]
  ring

end Zeta5PrimeSums
namespace Zeta5Parameters
open Zeta5PrimeSums Zeta5SmallPrimeAsymptotics Zeta5InnerAsymptotics Zeta5OuterAsymptotics

/-- The finite prime partition of the literal logarithmic normalizer.
The allocation penalty is counted once across both inner ranges. -/
theorem log_normalizer_le_ranges (n M : ℕ) (hM : 40≤M) :
    Real.log (normalizer n M:ℝ) ≤
      smallLocalSum n M + tailCorrectedLocalSum n M + innerCorrectedLocalSum n M +
        outerLocalSum n M + weightedTheta ((K n:ℝ)/3)/2 := by
  have hMr : (20:ℝ)≤M := by exact_mod_cast (show 20≤M by omega)
  have hK : (0:ℝ)≤K n := by positivity
  have hab : ⌊(K n:ℝ)/(M:ℝ)⌋₊≤⌊(K n:ℝ)/20⌋₊ :=
    Nat.floor_mono (div_le_div_of_nonneg_left hK (by norm_num) hMr)
  have hbc : ⌊(K n:ℝ)/20⌋₊≤⌊(K n:ℝ)/3⌋₊ :=
    Nat.floor_mono (div_le_div_of_nonneg_left hK (by norm_num) (by norm_num))
  have hcd : ⌊(K n:ℝ)/3⌋₊≤⌊(37/20:ℝ)*(K n:ℝ)⌋₊ :=
    Nat.floor_mono (by linarith)
  rw [normalizer_prime_sum]
  have he := corrected_prime_range_partition _ _ _ _ hab hbc hcd
    (fun p => -(localExponent n M p:ℝ)*Real.log p)
    (fun p => (p:ℝ)/2*Real.log p)
  have hs (u v : ℕ) :
      (∑p∈Finset.Ioc u v with p.Prime,
        (-(localExponent n M p:ℝ)*Real.log p-(p:ℝ)/2*Real.log p)) =
      ∑p∈Finset.Ioc u v with p.Prime,
        (-(localExponent n M p:ℝ)-(p:ℝ)/2)*Real.log p := by
    apply Finset.sum_congr rfl
    intro p hp
    ring
  simp only [hs] at he
  rw [he]
  exact add_le_add (le_refl _) (prime_allocation_sum_le _ ((K n:ℝ)/3))

/-- The once-counted allocation penalty has normalized limit 1/36. -/
theorem normalizer_allocation_tendsto :
    Tendsto (fun n : ℕ => (weightedTheta ((K n:ℝ)/3)/2)/(K n:ℝ)^2)
      atTop (𝓝 ((1:ℝ)/36)) := by
  have ht := ((scaled_weightedTheta_ratio_tendsto chebyshev_asymptotic
    (by norm_num : (0:ℝ)<1/3)).div_const 2).comp K_tendsto_atTop
  convert ht using 1
  · funext n
    simp only [Function.comp_def,one_div_mul_eq_div]
    ring
  · norm_num

theorem normalizer_allocation_eventually_upper (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,
      (weightedTheta ((K n:ℝ)/3)/2)/(K n:ℝ)^2 ≤ 1/36+ε :=
  (normalizer_allocation_tendsto.eventually
    (gt_mem_nhds (by linarith : (1:ℝ)/36<1/36+ε))).mono (fun n hn => hn.le)

#print axioms log_normalizer_le_ranges
#print axioms normalizer_allocation_tendsto
end Zeta5Parameters
