import InnerPrimeGeometry
import PrimeSums
import Mathlib.Tactic

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
noncomputable section
open Filter Asymptotics
open scoped BigOperators Topology
namespace Zeta5InnerAsymptotics

def innerPrimeModel (x : ℝ) : ℝ :=
  ∑ i : Fin 143, ∑ p ∈ Finset.Ioc ⌊x/(innerCellRight i:ℝ)⌋₊
      ⌊x/(innerCellLeft i:ℝ)⌋₊ with p.Prime,
    ((innerCellSlope i:ℝ)*x+(innerCellConstant i:ℝ)*(p:ℝ))*Real.log p

theorem innerPrimeModel_tendsto :
    Tendsto (fun x : ℝ => innerPrimeModel x/x^2) atTop
      (𝓝 ((322437603634266857629:ℝ)/7535670527041937280000)) := by
  have hc (i : Fin 143) : 0<(innerCellLeft i:ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℚ)<3) (innerCell_bounds i).1)
  have hd (i : Fin 143) : (innerCellLeft i:ℝ)≤(innerCellRight i:ℝ) := by
    exact_mod_cast (innerCell_bounds i).2.1
  have hu (i : Fin 143) : 0<(1:ℝ)/(innerCellRight i:ℝ) := by
    apply div_pos zero_lt_one
    exact (hc i).trans_le (hd i)
  have huv (i : Fin 143) : (1:ℝ)/(innerCellRight i:ℝ)≤(1:ℝ)/(innerCellLeft i:ℝ) :=
    one_div_le_one_div_of_le (hc i) (hd i)
  have h := tendsto_finsetSum Finset.univ (fun i hi =>
    Zeta5PrimeSums.affine_prime_sum_tendsto chebyshev_asymptotic
      (innerCellSlope i) (innerCellConstant i) (1/(innerCellRight i:ℝ))
      (1/(innerCellLeft i:ℝ)) (hu i) (huv i))
  have he : (∑ i : Fin 143,
      ((innerCellSlope i:ℝ)*(1/(innerCellLeft i:ℝ)-1/(innerCellRight i:ℝ))+
        (innerCellConstant i:ℝ)*((1/(innerCellLeft i:ℝ))^2-(1/(innerCellRight i:ℝ))^2)/2)) =
      (322437603634266857629:ℝ)/7535670527041937280000 := by
    have hh := congrArg (fun q:ℚ => (q:ℝ)) innerIntegral_exact
    unfold innerIntegral at hh
    push_cast at hh
    convert hh using 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he] at h
  convert h using 1
  funext x
  unfold innerPrimeModel
  simp only [Finset.sum_div,one_div_mul_eq_div]

private theorem prime_sum_Ioc_eq_difference (lo hi : ℕ) (h : lo≤hi) (f : ℕ→ℝ) :
    (∑ p ∈ Finset.Ioc lo hi with p.Prime, f p) =
      (∑ p ∈ Finset.Icc 0 hi with p.Prime, f p)-
      ∑ p ∈ Finset.Icc 0 lo with p.Prime, f p := by
  simpa only [Finset.sum_filter] using
    Zeta5PrimeSums.sum_Ioc_eq_difference lo hi h (fun p => if p.Prime then f p else 0)

theorem inner_prime_partition (x : ℝ) (hx : 0≤x) (f : ℕ→ℝ) :
    (∑ i : Fin 143, ∑ p ∈ Finset.Ioc ⌊x/(innerCellRight i:ℝ)⌋₊
      ⌊x/(innerCellLeft i:ℝ)⌋₊ with p.Prime, f p) =
    ∑ p ∈ Finset.Ioc ⌊x/20⌋₊ ⌊x/3⌋₊ with p.Prime, f p := by
  have hmono (i : Fin 143) : ⌊x/(innerCellRight i:ℝ)⌋₊≤⌊x/(innerCellLeft i:ℝ)⌋₊ := by
    apply Nat.floor_mono
    apply div_le_div_of_nonneg_left hx
    · exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℚ)<3) (innerCell_bounds i).1)
    · exact_mod_cast (innerCell_bounds i).2.1
  have hwhole : ⌊x/20⌋₊≤⌊x/3⌋₊ := by apply Nat.floor_mono; linarith
  have he (i : Fin 143) := prime_sum_Ioc_eq_difference _ _ (hmono i) f
  simp_rw [he]
  rw [prime_sum_Ioc_eq_difference _ _ hwhole f]
  norm_num [innerCellLeft,innerCellRight,Fin.sum_univ_succ]
  ring

#print axioms innerPrimeModel_tendsto
end Zeta5InnerAsymptotics
