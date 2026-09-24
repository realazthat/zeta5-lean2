import FarUnitPowerSeries
import PartialFractions

namespace Zeta5Local
open Polynomial Filter Topology
open scoped PowerSeries.WithPiTopology
variable {p : ℕ} [Fact p.Prime]
variable {ι : Type*} [DecidableEq ι]

lemma remainder_barycentric (P : Polynomial ℚ_[p]) (s : Finset ι) (r : ι → ℚ_[p])
    (hinj : Set.InjOn r s) :
    P %ₘ poleDenominator s r =
      ∑ i ∈ s, C (P.eval (r i) / ∏ k ∈ s.erase i, (r i - r k)) *
        poleDenominator (s.erase i) r := by
  change P %ₘ Lagrange.nodal s r = _
  rw [remainder_eq_interpolate P s r hinj,
    Lagrange.interpolate_eq_nodalWeight_mul_nodal_div_X_sub_C]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Lagrange.nodal_erase_eq_nodal_div hi]
  simp only [Lagrange.nodalWeight, Finset.prod_inv_distrib, div_eq_mul_inv,
    map_mul, poleDenominator, Lagrange.nodal]
  ring

lemma weighted_eval_summable (U : ℕ → Polynomial ℚ_[p])
    (hU : ∀ j n, ‖(U j).coeff n‖ ≤ 1) (x : ℚ_[p]) (hx : ‖x‖ ≤ 1) :
    Summable (fun j : ℕ => (p : ℚ_[p]) ^ j * (U j).eval x) :=
  bounded_kernel_summable _ _ 1
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one)
    (fun j => integral_polynomial_eval (U j) x (hU j) hx)

/-- Monic remainders commute with the coefficient completion. Their limit
is exactly the finite barycentric interpolation of the convergent values at
all near poles. -/
theorem weighted_remainder_identity (U : ℕ → Polynomial ℚ_[p])
    (s : Finset ι) (r : ι → ℚ_[p]) (hinj : Set.InjOn r s)
    (hU : ∀ j n, ‖(U j).coeff n‖ ≤ 1) (hr : ∀ i, ‖r i‖ ≤ 1) :
    weightedPolynomialSeries (fun j => U j %ₘ poleDenominator s r) =
      ∑ i ∈ s, PowerSeries.C
        ((∑' j : ℕ, (p : ℚ_[p]) ^ j * (U j).eval (r i)) /
          ∏ k ∈ s.erase i, (r i - r k)) *
        (poleDenominator (s.erase i) r : PowerSeries ℚ_[p]) := by
  have hR (j n : ℕ) : ‖(U j %ₘ poleDenominator s r).coeff n‖ ≤ 1 :=
    (integral_monic_division (U j) _ (poleDenominator_monic s r) (hU j)
      (poleDenominator_integral s r hr)).2 n
  ext n
  rw [weightedPolynomialSeries_coeff _ hR]
  simp only [map_sum, PowerSeries.coeff_C_mul, coeff_coe]
  simp_rw [remainder_barycentric _ s r hinj, finsetSum_coeff, coeff_C_mul,
    Finset.mul_sum]
  have hs (i : ι) (_hi : i ∈ s) : Summable (fun j : ℕ =>
      (p : ℚ_[p]) ^ j * ((U j).eval (r i) /
        (∏ k ∈ s.erase i, (r i - r k)) * (poleDenominator (s.erase i) r).coeff n)) := by
    convert! (weighted_eval_summable U hU (r i) (hr i)).mul_right
      ((∏ k ∈ s.erase i, (r i - r k))⁻¹ * (poleDenominator (s.erase i) r).coeff n) using 1
    funext j
    ring
  rw [Summable.tsum_finsetSum hs]
  apply Finset.sum_congr rfl
  intro i hi
  simp_rw [div_eq_mul_inv, mul_assoc]
  rw [← tsum_mul_right]
  apply tsum_congr
  intro j
  ring

/-- For the far-unit geometric expansion the limiting near residues are
exactly the original rational numerator evaluated at each near pole. -/
theorem farUnit_remainder_identity (A V : Polynomial ℚ_[p]) (u : ℚ_[p])
    (s : Finset ι) (r : ι → ℚ_[p]) (hinj : Set.InjOn r s)
    (hA : ∀ n, ‖A.coeff n‖ ≤ 1) (hV : ∀ n, ‖V.coeff n‖ ≤ 1)
    (hu : ‖u‖ = 1) (hr : ∀ i, ‖r i‖ ≤ 1) :
    weightedPolynomialSeries (fun j => farUnitExpansion A V u j %ₘ poleDenominator s r) =
      ∑ i ∈ s, PowerSeries.C
        ((A.eval (r i) / (u + p * V.eval (r i))) /
          ∏ k ∈ s.erase i, (r i - r k)) *
        (poleDenominator (s.erase i) r : PowerSeries ℚ_[p]) := by
  rw [weighted_remainder_identity _ s r hinj (farUnitExpansion_integral A V u hA hV hu) hr]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(farUnitExpansion_hasSum A V u (r i) hV hu (hr i)).tsum_eq]

#print axioms farUnit_remainder_identity
end Zeta5Local
