import NearPoleCompletion
import AnalyticPresentation

namespace Zeta5Local
open Polynomial
open scoped PowerSeries.WithPiTopology
variable {p : ℕ} [Fact p.Prime]
variable {ι κ : Type*} [DecidableEq ι]

/-- Exact finite partial fractions transfer to the coefficient completion;
far poles are inverted by their convergent geometric coefficient series. -/
theorem canonical_powerSeries_identity
    (A D T P R : Polynomial ℚ_[p]) (t : Finset κ)
    (v c : κ → ℚ_[p]) (Dk : κ → Polynomial ℚ_[p])
    (hv : ∀ k ∈ t, v k ≠ 0)
    (hDk : ∀ k ∈ t, D = (X - C (v k)) * Dk k)
    (hidentity : A = D * T * P + D * R + ∑ k ∈ t, C (c k) * T * Dk k) :
    (D : PowerSeries ℚ_[p]) *
      ((T : PowerSeries ℚ_[p]) * ((P : PowerSeries ℚ_[p]) +
        ∑ k ∈ t, PowerSeries.C (c k) * farPolePowerSeries (v k)) + R) = A := by
  have hcancel (k : κ) (hk : k ∈ t) :
      (D : PowerSeries ℚ_[p]) * farPolePowerSeries (v k) = Dk k := by
    rw [hDk k hk, coe_mul, coe_sub, coe_X, coe_C]
    calc
      _ = (Dk k : PowerSeries ℚ_[p]) *
        ((PowerSeries.X - PowerSeries.C (v k)) * farPolePowerSeries (v k)) := by ring
      _ = (Dk k : PowerSeries ℚ_[p]) := by rw [farPolePowerSeries_identity _ (hv k hk), mul_one]
  have hsum := map_sum (Polynomial.coeToPowerSeries.ringHom (R := ℚ_[p]))
    (fun k => C (c k) * T * Dk k) t
  simp only [coeToPowerSeries.ringHom_apply, coe_mul, coe_C] at hsum
  rw [hidentity]
  simp only [mul_add, Finset.mul_sum, coe_add, coe_mul]
  rw [hsum]
  have hs : (∑ k ∈ t, (D : PowerSeries ℚ_[p]) *
      ((T : PowerSeries ℚ_[p]) * (PowerSeries.C (c k) * farPolePowerSeries (v k)))) =
      ∑ k ∈ t, PowerSeries.C (c k) * (T : PowerSeries ℚ_[p]) * (Dk k : PowerSeries ℚ_[p]) := by
    apply Finset.sum_congr rfl
    intro k hk
    calc
      _ = PowerSeries.C (c k) * (T : PowerSeries ℚ_[p]) *
        ((D : PowerSeries ℚ_[p]) * farPolePowerSeries (v k)) := by ring
      _ = _ := by rw [hcancel k hk]
  rw [hs]
  ring

/-- Canonical quotient and residue data agree with the complete near-pole
series whenever the same numerator and denominator identity holds. The
sequence can retain an arbitrary p-divisible high-degree numerator tail. -/
theorem canonical_eq_nearPoleSeries (hp7 : 7 ≤ p)
    (U : ℕ → Polynomial ℚ_[p]) (A D P : Polynomial ℚ_[p])
    (s : Finset ι) (r : ι → ℚ_[p]) (d : ι → ℕ) (b : ι → ℚ_[p])
    (t : Finset κ) (v c : κ → ℚ_[p]) (Y : Polynomial ℚ_[p])
    (hU : ∀ j n, ‖(U j).coeff n‖ ≤ 1) (hr : ∀ i, ‖r i‖ ≤ 1)
    (hinj : Set.InjOn r s) (hD : D ≠ 0)
    (hv : ∀ k ∈ t, ‖(v k)⁻¹‖ < 1)
    (hb : ∀ i ∈ s, b i = (∑' j : ℕ, (p : ℚ_[p]) ^ j * (U j).eval (r i)) /
      ∏ k ∈ s.erase i, (r i - r k))
    (hseries : (D : PowerSeries ℚ_[p]) * weightedPolynomialSeries U = A)
    (hcanonical : (D : PowerSeries ℚ_[p]) *
      ((poleDenominator s r : PowerSeries ℚ_[p]) * ((P : PowerSeries ℚ_[p]) +
        ∑ k ∈ t, PowerSeries.C (c k) * farPolePowerSeries (v k)) +
        ∑ i ∈ s, PowerSeries.C (b i) * (poleDenominator (s.erase i) r : PowerSeries ℚ_[p])) = A) :
    C (tauPolynomial P + ∑ k ∈ t, c k * analyticPoleValue (v k)) +
      ∑ i ∈ s, C (b i) * (C (localHarmonic (d i)) - Y) =
        nearPolePolynomialSeries U s r d Y := by
  have hdivision := weightedPolynomialSeries_division U (poleDenominator s r)
    (poleDenominator_monic s r) hU (poleDenominator_integral s r hr)
  rw [weighted_remainder_identity U s r hinj hU hr] at hdivision
  have hrem : (∑ i ∈ s, PowerSeries.C
      ((∑' j : ℕ, (p : ℚ_[p]) ^ j * (U j).eval (r i)) /
        ∏ k ∈ s.erase i, (r i - r k)) *
      (poleDenominator (s.erase i) r : PowerSeries ℚ_[p])) =
      ∑ i ∈ s, PowerSeries.C (b i) * (poleDenominator (s.erase i) r : PowerSeries ℚ_[p]) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hb i hi]
  rw [hrem] at hdivision
  have hT0 : (poleDenominator s r : PowerSeries ℚ_[p]) ≠ 0 := by
    exact_mod_cast (poleDenominator_monic s r).ne_zero
  have hD0 : (D : PowerSeries ℚ_[p]) ≠ 0 := by exact_mod_cast hD
  have hQ : weightedPolynomialSeries (fun j => U j /ₘ poleDenominator s r) =
      (P : PowerSeries ℚ_[p]) + ∑ k ∈ t, PowerSeries.C (c k) * farPolePowerSeries (v k) := by
    apply mul_left_cancel₀ (mul_ne_zero hD0 hT0)
    have hL := congrArg (fun F : PowerSeries ℚ_[p] => (D : PowerSeries ℚ_[p]) * F) hdivision
    rw [hseries] at hL
    linear_combination hL - hcanonical
  rw [nearPolePolynomialSeries_as_powerSeries hp7 U s r d Y hU hr, hQ,
    (tauPowerSeries_analytic_presentation hp7 P t v c hv).2]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [hb i hi]

/-- The full canonical rational functional satisfies the coefficient bound
from Lemma 3.1, with its original numerator approximation intact. -/
theorem canonical_local_coefficient_bound (hp7 : 7 ≤ p)
    (U : ℕ → Polynomial ℚ_[p]) (A D P : Polynomial ℚ_[p])
    (s : Finset ι) (r : ι → ℚ_[p]) (d : ι → ℕ) (b : ι → ℚ_[p])
    (t : Finset κ) (v c : κ → ℚ_[p]) (Y : Polynomial ℚ_[p])
    (hU : ∀ j n, ‖(U j).coeff n‖ ≤ 1) (hr : ∀ i, ‖r i‖ ≤ 1)
    (hinj : Set.InjOn r s) (hD : D ≠ 0)
    (hv : ∀ k ∈ t, ‖(v k)⁻¹‖ < 1)
    (hb : ∀ i ∈ s, b i = (∑' j : ℕ, (p : ℚ_[p]) ^ j * (U j).eval (r i)) /
      ∏ k ∈ s.erase i, (r i - r k))
    (hseries : (D : PowerSeries ℚ_[p]) * weightedPolynomialSeries U = A)
    (hcanonical : (D : PowerSeries ℚ_[p]) *
      ((poleDenominator s r : PowerSeries ℚ_[p]) * ((P : PowerSeries ℚ_[p]) +
        ∑ k ∈ t, PowerSeries.C (c k) * farPolePowerSeries (v k)) +
        ∑ i ∈ s, PowerSeries.C (b i) * (poleDenominator (s.erase i) r : PowerSeries ℚ_[p])) = A)
    (hsep : ∀ i ∈ s, ∀ j ∈ s.erase i, ‖r i - r j‖ = 1)
    (hd : ∀ i ∈ s, d i < p) (hY : ∀ n, ‖Y.coeff n‖ ≤ 1)
    (hdeg : (U 0).natDegree ≤ p + 1) (n : ℕ) :
    ‖(C (tauPolynomial P + ∑ k ∈ t, c k * analyticPoleValue (v k)) +
      ∑ i ∈ s, C (b i) * (C (localHarmonic (d i)) - Y)).coeff n‖ ≤ 1 := by
  rw [canonical_eq_nearPoleSeries hp7 U A D P s r d b t v c Y hU hr hinj hD hv hb hseries hcanonical]
  exact nearPolePolynomialSeries_integral hp7 U s r d Y hU hr hsep hd hY hdeg n

#print axioms canonical_local_coefficient_bound
end Zeta5Local
