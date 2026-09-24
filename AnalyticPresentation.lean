import FarUnitPowerSeries

namespace Zeta5Local
open Polynomial
open scoped PowerSeries.WithPiTopology
variable {p : ℕ} [Fact p.Prime]

def TauSummable (F : PowerSeries ℚ_[p]) : Prop :=
  Summable (fun n : ℕ => PowerSeries.coeff n F * (rationalTauMoment n : ℚ_[p]))

lemma tauSummable_polynomial (P : Polynomial ℚ_[p]) : TauSummable (P : PowerSeries ℚ_[p]) := by
  apply summable_of_ne_finset_zero (s := P.support)
  intro n hn
  simp [notMem_support_iff.mp hn]

lemma tauPowerSeries_polynomial (P : Polynomial ℚ_[p]) :
    tauPowerSeries (P : PowerSeries ℚ_[p]) = tauPolynomial P := by
  unfold tauPowerSeries tauPolynomial
  rw [tsum_eq_sum (s := P.support) (fun n hn => by simp [notMem_support_iff.mp hn])]
  simp only [coeff_coe]

lemma tauSummable_add {F G : PowerSeries ℚ_[p]} (hF : TauSummable F) (hG : TauSummable G) :
    TauSummable (F + G) := by
  simpa only [TauSummable, map_add, add_mul] using hF.add hG

lemma tauPowerSeries_add {F G : PowerSeries ℚ_[p]} (hF : TauSummable F) (hG : TauSummable G) :
    tauPowerSeries (F + G) = tauPowerSeries F + tauPowerSeries G := by
  simp only [tauPowerSeries, map_add, add_mul]
  exact hF.tsum_add hG

lemma tauSummable_C_mul {F : PowerSeries ℚ_[p]} (hF : TauSummable F) (c : ℚ_[p]) :
    TauSummable (PowerSeries.C c * F) := by
  simpa only [TauSummable, PowerSeries.coeff_C_mul, mul_assoc] using hF.mul_left c

lemma tauPowerSeries_C_mul (F : PowerSeries ℚ_[p]) (c : ℚ_[p]) :
    tauPowerSeries (PowerSeries.C c * F) = c * tauPowerSeries F := by
  simp only [tauPowerSeries, PowerSeries.coeff_C_mul, mul_assoc, tsum_mul_left]

lemma tauSummable_finset_sum {ι : Type*} (s : Finset ι) (F : ι → PowerSeries ℚ_[p])
    (hF : ∀ i ∈ s, TauSummable (F i)) : TauSummable (∑ i ∈ s, F i) := by
  unfold TauSummable
  simp only [map_sum, Finset.sum_mul]
  exact summable_sum hF

lemma tauPowerSeries_finset_sum {ι : Type*} (s : Finset ι) (F : ι → PowerSeries ℚ_[p])
    (hF : ∀ i ∈ s, TauSummable (F i)) :
    tauPowerSeries (∑ i ∈ s, F i) = ∑ i ∈ s, tauPowerSeries (F i) := by
  simp only [tauPowerSeries, map_sum, Finset.sum_mul]
  exact Summable.tsum_finsetSum hF

/-- The completed Bernoulli functional agrees with every finite analytic
partial-fraction presentation of the polynomial-plus-far-pole part. -/
theorem tauPowerSeries_analytic_presentation {ι : Type*} (hp7 : 7 ≤ p)
    (P : Polynomial ℚ_[p]) (s : Finset ι) (r c : ι → ℚ_[p])
    (hr : ∀ i ∈ s, ‖(r i)⁻¹‖ < 1) :
    TauSummable ((P : PowerSeries ℚ_[p]) +
      ∑ i ∈ s, PowerSeries.C (c i) * farPolePowerSeries (r i)) ∧
    tauPowerSeries ((P : PowerSeries ℚ_[p]) +
      ∑ i ∈ s, PowerSeries.C (c i) * farPolePowerSeries (r i)) =
      tauPolynomial P + ∑ i ∈ s, c i * analyticPoleValue (r i) := by
  have hf (i : ι) (hi : i ∈ s) : TauSummable (farPolePowerSeries (r i)) := by
    simpa only [TauSummable, farPolePowerSeries_coeff] using
      analyticPole_summable hp7 (r i) (hr i hi)
  have hs := tauSummable_finset_sum s _ (fun i hi => tauSummable_C_mul (hf i hi) (c i))
  constructor
  · exact tauSummable_add (tauSummable_polynomial P) hs
  · rw [tauPowerSeries_add (tauSummable_polynomial P) hs, tauPowerSeries_polynomial,
      tauPowerSeries_finset_sum s _ (fun i hi => tauSummable_C_mul (hf i hi) (c i))]
    simp only [tauPowerSeries_C_mul, tauPowerSeries_farPole]

#print axioms tauPowerSeries_analytic_presentation
end Zeta5Local
