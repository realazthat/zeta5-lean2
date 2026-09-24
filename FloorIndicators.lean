import InnerRealKernel
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open scoped BigOperators
namespace Zeta5RealKernel

theorem floor_finite_indicators (y : ℝ) (B : ℕ) (hy : 0≤y) (hB : ⌊y⌋₊≤B) :
    (⌊y⌋:ℝ)=∑ j ∈ Finset.Icc 1 B, if (j:ℝ)≤y then (1:ℝ) else 0 := by
  have he : (Finset.Icc 1 B).filter (fun j : ℕ => (j:ℝ)≤y)=Finset.Icc 1 ⌊y⌋₊ := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_Icc]
    rw [←Nat.le_floor_iff hy]
    omega
  rw [←Finset.sum_filter,he]
  simp only [Finset.sum_const,Nat.card_Icc,nsmul_eq_mul,mul_one,Nat.add_sub_cancel]
  norm_cast
  exact (Int.natCast_floor_eq_floor hy).symm

theorem floor_scaled_finite_indicators (c x M : ℝ) (hc : 0≤c) (hx : 0≤x) (hM : x≤M) :
    (⌊c*x⌋:ℝ)=∑ j ∈ Finset.Icc 1 ⌊c*M⌋₊, if (j:ℝ)≤c*x then (1:ℝ) else 0 :=
  floor_finite_indicators _ _ (mul_nonneg hc hx) (Nat.floor_mono (mul_le_mul_of_nonneg_left hM hc))

end Zeta5RealKernel
