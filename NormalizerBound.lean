import NormalizationRanges
import TailPrimeBound
import AllocationPrimeBound
import NormalizerConstants

noncomputable section
open Filter
open scoped Topology
namespace Zeta5Parameters
open Zeta5SmallPrimeAsymptotics Zeta5InnerAsymptotics Zeta5OuterAsymptotics

/-- The actual prime normalizer obeys the certified Section 5 quadratic
upper bound, with all arithmetic and prime-sum estimates discharged. -/
theorem eventually_log_normalizer_upper (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, Real.log (normalizer n 100000:ℝ) ≤
      ((Zeta5NormalizationTail.normalizationCoefficient:ℝ)+ε)*(40*(n:ℝ))^2 := by
  have he : 0<ε/5 := by positivity
  filter_upwards [eventually_ge_atTop (1:ℕ),
    smallLocalSum_eventually_upper 100000 (by norm_num) (ε/5) he,
    tailCorrectedLocalSum_eventually_upper (ε/5) he,
    innerCorrectedLocalSum_eventually_upper 100000 (by norm_num) (ε/5) he,
    outerLocalSum_eventually_upper 100000 (by norm_num) (ε/5) he,
    prime_allocation_loss_eventually_upper (ε/5) he] with n hn hs ht hi ho ha
  have hk : 0<(K n:ℝ)^2 := by
    have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
    unfold K
    push_cast
    positivity
  have hp := div_le_div_of_nonneg_right (log_normalizer_le_ranges n 100000 (by norm_num)) hk.le
  simp only [add_div] at hp
  have hsum : Real.log (normalizer n 100000:ℝ)/(K n:ℝ)^2≤
      (Zeta5NormalizationTail.normalizationCoefficient:ℝ)+ε := by
    rw [Zeta5NormalizationTail.normalizationCoefficient_eq_prime_contributions]
    linarith
  have hf := (div_le_iff₀ hk).mp hsum
  simpa only [K,Nat.cast_mul,Nat.cast_ofNat] using hf

#print axioms eventually_log_normalizer_upper
end Zeta5Parameters
