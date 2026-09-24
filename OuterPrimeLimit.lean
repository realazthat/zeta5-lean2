import OuterPrimeCells
import PrimeSums
import Mathlib.Tactic

noncomputable section
open Filter Asymptotics
open scoped BigOperators Topology
namespace Zeta5OuterAsymptotics

/-- The finite affine prime model for the outer interval K/3<p≤2h. -/
def outerPrimeModel (x : ℝ) : ℝ :=
  ∑ i : Fin 11, ∑ p ∈ Finset.Ioc ⌊(outerCellLeft i:ℝ)*x⌋₊ ⌊(outerCellRight i:ℝ)*x⌋₊ with p.Prime,
    ((outerCellConstant i:ℝ)*x+(outerCellSlope i:ℝ)*(p:ℝ))*Real.log p

/-- Unconditional PNT asymptotic for the eleven verified outer cells. -/
theorem outerPrimeModel_tendsto :
    Tendsto (fun x : ℝ => outerPrimeModel x/x^2) atTop (𝓝 ((127751:ℝ)/96000+9/640)) := by
  have hc (i : Fin 11) : 0<(outerCellLeft i:ℝ) := by
    fin_cases i <;> norm_num [outerCellLeft]
  have hcd (i : Fin 11) : (outerCellLeft i:ℝ)≤(outerCellRight i:ℝ) := by
    fin_cases i <;> norm_num [outerCellLeft,outerCellRight]
  have h := tendsto_finsetSum Finset.univ (fun i hi =>
    Zeta5PrimeSums.affine_prime_sum_tendsto chebyshev_asymptotic
      (outerCellConstant i) (outerCellSlope i) (outerCellLeft i) (outerCellRight i) (hc i) (hcd i))
  have he : (∑ i : Fin 11,
      ((outerCellConstant i:ℝ)*((outerCellRight i:ℝ)-(outerCellLeft i:ℝ))+
        (outerCellSlope i:ℝ)*((outerCellRight i:ℝ)^2-(outerCellLeft i:ℝ)^2)/2)) =
      (127751:ℝ)/96000+9/640 := by
    have hh := congrArg (fun q:ℚ => (q:ℝ)) outerIntegral_exact
    simpa only [outerIntegral,Rat.cast_sum,Rat.cast_add,Rat.cast_mul,Rat.cast_sub,
      Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using hh
  rw [he] at h
  convert h using 1
  funext x
  unfold outerPrimeModel
  rw [Finset.sum_div]

private theorem prime_sum_Ioc_eq_difference (lo hi : ℕ) (h : lo≤hi) (f : ℕ→ℝ) :
    (∑ p ∈ Finset.Ioc lo hi with p.Prime, f p) =
      (∑ p ∈ Finset.Icc 0 hi with p.Prime, f p)-
      ∑ p ∈ Finset.Icc 0 lo with p.Prime, f p := by
  simpa only [Finset.sum_filter] using
    Zeta5PrimeSums.sum_Ioc_eq_difference lo hi h (fun p => if p.Prime then f p else 0)

/-- The eleven right-closed cells partition the complete outer prime range,
including every rational endpoint without an exception term. -/
theorem outer_prime_partition (x : ℝ) (hx : 0≤x) (f : ℕ→ℝ) :
    (∑ i : Fin 11, ∑ p ∈ Finset.Ioc ⌊(outerCellLeft i:ℝ)*x⌋₊
      ⌊(outerCellRight i:ℝ)*x⌋₊ with p.Prime, f p) =
    ∑ p ∈ Finset.Ioc ⌊x/3⌋₊ ⌊(37/20:ℝ)*x⌋₊ with p.Prime, f p := by
  have hmono (i : Fin 11) : ⌊(outerCellLeft i:ℝ)*x⌋₊≤⌊(outerCellRight i:ℝ)*x⌋₊ := by
    apply Nat.floor_mono
    apply mul_le_mul_of_nonneg_right _ hx
    fin_cases i <;> norm_num [outerCellLeft,outerCellRight]
  have hwhole : ⌊x/3⌋₊≤⌊(37/20:ℝ)*x⌋₊ := by apply Nat.floor_mono; linarith
  have he (i : Fin 11) := prime_sum_Ioc_eq_difference _ _ (hmono i) f
  simp_rw [he]
  rw [prime_sum_Ioc_eq_difference _ _ hwhole f]
  norm_num [outerCellLeft,outerCellRight,Fin.sum_univ_succ]
  rw [show (1/3:ℝ)*x=x/3 by ring]
  ring

#print axioms outerPrimeModel_tendsto
end Zeta5OuterAsymptotics
