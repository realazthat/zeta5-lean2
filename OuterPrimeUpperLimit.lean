import OuterPrimeBound
import NormalizationLog

noncomputable section
open Filter Asymptotics
open scoped BigOperators Topology
namespace Zeta5PrimeSums

theorem theta_over_square_tendsto {c : ℝ} (hc : 0<c) :
    Tendsto (fun x : ℝ => Chebyshev.theta (c*x)/x^2) atTop (𝓝 0) := by
  have h := (scaled_asymptotic_ratio chebyshev_asymptotic hc).div_atTop tendsto_id
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  dsimp only [id_eq]
  field_simp

end Zeta5PrimeSums
namespace Zeta5Parameters

theorem K_tendsto_atTop : Tendsto (fun n : ℕ => (K n:ℝ)) atTop atTop := by
  have h : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  simpa only [K,Nat.cast_mul,Nat.cast_ofNat] using h.const_mul_atTop (by norm_num : (0:ℝ)<40)

end Zeta5Parameters
namespace Zeta5OuterAsymptotics
open Zeta5Parameters

theorem outer_model_with_error_tendsto (M : ℕ) :
    Tendsto (fun n : ℕ =>
      (outerPrimeModel (K n:ℝ)+(3+4*(M:ℝ))*Chebyshev.theta ((37/20:ℝ)*(K n:ℝ)))/(K n:ℝ)^2)
      atTop (𝓝 ((129101:ℝ)/96000)) := by
  have h := outerPrimeModel_tendsto.add
    ((Zeta5PrimeSums.theta_over_square_tendsto (by norm_num : (0:ℝ)<37/20)).const_mul (3+4*(M:ℝ)))
  have h' := h.comp K_tendsto_atTop
  convert h' using 1
  · funext n
    dsimp only [Function.comp_def]
    ring
  · norm_num

theorem outerLocalSum_eventually_upper (M : ℕ) (hM : 40≤M) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, outerLocalSum n M/(K n:ℝ)^2≤129101/96000+ε := by
  have ht := (outer_model_with_error_tendsto M).eventually (gt_mem_nhds (by linarith :
    (129101:ℝ)/96000<129101/96000+ε))
  filter_upwards [eventually_admissible M hM,ht] with n ha hn
  exact (div_le_div_of_nonneg_right (outerLocalSum_le_model n M ha) (sq_nonneg _)).trans hn.le

#print axioms outerLocalSum_eventually_upper
end Zeta5OuterAsymptotics
