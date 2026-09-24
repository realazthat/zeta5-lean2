import PowerSeriesCompletion

namespace Zeta5Local
open Polynomial Filter Topology
open scoped PowerSeries.WithPiTopology
variable {p : ℕ} [Fact p.Prime]

lemma farUnitExpansion_term (A V : Polynomial ℚ_[p]) (u : ℚ_[p]) (j : ℕ) :
    C ((p : ℚ_[p]) ^ j) * farUnitExpansion A V u j =
      C u⁻¹ * A * (C ((p : ℚ_[p]) * u⁻¹) * (-V)) ^ j := by
  simp only [farUnitExpansion, map_pow, map_mul, mul_pow, pow_succ]
  ring

/-- The geometric expansion agrees with the exact formal rational identity.
This upgrades pointwise equality to coefficient equality. -/
theorem farUnitExpansion_powerSeries_identity (A V : Polynomial ℚ_[p]) (u : ℚ_[p])
    (hA : ∀ n, ‖A.coeff n‖ ≤ 1) (hV : ∀ n, ‖V.coeff n‖ ≤ 1) (hu : ‖u‖ = 1) :
    ((C u + C (p : ℚ_[p]) * V : Polynomial ℚ_[p]) : PowerSeries ℚ_[p]) *
      weightedPolynomialSeries (farUnitExpansion A V u) = (A : PowerSeries ℚ_[p]) := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  let B : PowerSeries ℚ_[p] := ((C ((p : ℚ_[p]) * u⁻¹) * (-V) : Polynomial ℚ_[p]) :
    PowerSeries ℚ_[p])
  have hc : (C u : Polynomial ℚ_[p]) * C u⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hu0, map_one]
  have hs1 := weightedPolynomialSeries_summable (farUnitExpansion 1 V u)
    (farUnitExpansion_integral 1 V u (by intro n; simp [coeff_one]; split_ifs <;> norm_num)
      hV hu)
  have hBs : Summable (fun j : ℕ => B ^ j) := by
    have hh := hs1.mul_left ((C u : Polynomial ℚ_[p]) : PowerSeries ℚ_[p])
    apply hh.congr
    intro j
    rw [farUnitExpansion_term, ← coe_mul]
    have he : (C u : Polynomial ℚ_[p]) *
        (C u⁻¹ * 1 * (C ((p : ℚ_[p]) * u⁻¹) * (-V)) ^ j) =
        (C ((p : ℚ_[p]) * u⁻¹) * (-V)) ^ j := by
      rw [← mul_assoc, ← mul_assoc, hc]
      simp
    rw [he, coe_pow]
  have hF : weightedPolynomialSeries (farUnitExpansion A V u) =
      ((C u⁻¹ * A : Polynomial ℚ_[p]) : PowerSeries ℚ_[p]) * ∑' j : ℕ, B ^ j := by
    rw [weightedPolynomialSeries, ← hBs.tsum_mul_left]
    apply tsum_congr
    intro j
    rw [farUnitExpansion_term, coe_mul, coe_pow]
  have hD : (C u + C (p : ℚ_[p]) * V) * (C u⁻¹ : Polynomial ℚ_[p]) =
      1 - C ((p : ℚ_[p]) * u⁻¹) * (-V) := by
    rw [map_mul]
    linear_combination hc
  rw [hF, ← mul_assoc, ← coe_mul]
  have he : (C u + C (p : ℚ_[p]) * V) * (C u⁻¹ * A) =
      A * (1 - C ((p : ℚ_[p]) * u⁻¹) * (-V)) := by
    rw [← mul_assoc, hD]
    ring
  rw [he, coe_mul, coe_sub, coe_one, mul_assoc]
  change (A : PowerSeries ℚ_[p]) * ((1 - B) * ∑' j : ℕ, B ^ j) = A
  rw [hBs.one_sub_mul_tsum_pow, mul_one]

noncomputable def farPolePowerSeries (s : ℚ_[p]) : PowerSeries ℚ_[p] :=
  PowerSeries.mk (fun n => -(s⁻¹ ^ (n + 1)))

@[simp] lemma farPolePowerSeries_coeff (s : ℚ_[p]) (n : ℕ) :
    PowerSeries.coeff n (farPolePowerSeries s) = -(s⁻¹ ^ (n + 1)) := by
  simp [farPolePowerSeries]

lemma tauPowerSeries_farPole (s : ℚ_[p]) :
    tauPowerSeries (farPolePowerSeries s) = analyticPoleValue s := by
  simp only [tauPowerSeries, farPolePowerSeries_coeff, analyticPoleValue]

lemma farPolePowerSeries_identity (s : ℚ_[p]) (hs : s ≠ 0) :
    (PowerSeries.X - PowerSeries.C s) * farPolePowerSeries s = 1 := by
  ext n
  cases n with
  | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff, farPolePowerSeries, hs]
  | succ n =>
    simp only [sub_mul, map_sub, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_C_mul, farPolePowerSeries_coeff, PowerSeries.coeff_one,
      Nat.add_eq_zero_iff, Nat.succ_ne_zero, false_and, if_false]
    simp only [pow_succ]
    linear_combination (s⁻¹ ^ n * s⁻¹) * (mul_inv_cancel₀ hs)

#print axioms farUnitExpansion_powerSeries_identity
#print axioms farPolePowerSeries_identity
end Zeta5Local
