import CanonicalLocalBound
import SplitExpansion

namespace Zeta5Local
open Polynomial
open scoped PowerSeries.WithPiTopology
variable {p : ℕ} [Fact p.Prime]
variable {ι κ : Type*} [DecidableEq ι]

lemma farUnitDenominator_ne_zero (V : Polynomial ℚ_[p]) (u : ℚ_[p])
    (hV : ∀ n, ‖V.coeff n‖ ≤ 1) (hu : ‖u‖ = 1) :
    C u + C (p : ℚ_[p])*V ≠ 0 := by
  have h1 : ∀ n, ‖(1 : Polynomial ℚ_[p]).coeff n‖ ≤ 1 := by
    simpa using integralCoeffs_C (p := p) (a := 1) (by norm_num)
  have he := farUnitExpansion_powerSeries_identity 1 V u h1 hV hu
  intro hz
  simp only [hz, coe_zero, zero_mul, coe_one] at he
  exact zero_ne_one he

/-- Concrete generic local bound for an original numerator A₀+pA₁ and a
far-unit denominator. Only A₀ is subject to the initial degree condition;
all canonical quotient and residue terms are included. -/
theorem canonical_split_coefficient_bound (hp7 : 7 ≤ p)
    (A₀ A₁ V A D P : Polynomial ℚ_[p]) (u : ℚ_[p])
    (s : Finset ι) (r : ι → ℚ_[p]) (d : ι → ℕ) (b : ι → ℚ_[p])
    (t : Finset κ) (v c : κ → ℚ_[p]) (Dk : κ → Polynomial ℚ_[p])
    (Y : Polynomial ℚ_[p])
    (hA : A = A₀+C (p : ℚ_[p])*A₁) (hD : D = C u+C (p : ℚ_[p])*V)
    (hA₀ : ∀ n, ‖A₀.coeff n‖ ≤ 1) (hA₁ : ∀ n, ‖A₁.coeff n‖ ≤ 1)
    (hV : ∀ n, ‖V.coeff n‖ ≤ 1) (hu : ‖u‖ = 1)
    (hr : ∀ i, ‖r i‖ ≤ 1) (hinj : Set.InjOn r s)
    (hv : ∀ k ∈ t, ‖(v k)⁻¹‖ < 1) (hv0 : ∀ k ∈ t, v k ≠ 0)
    (hb : ∀ i ∈ s, b i = A.eval (r i) /
      (D.eval (r i)*(∏ k ∈ s.erase i, (r i-r k))))
    (hDk : ∀ k ∈ t, D = (X-C (v k))*Dk k)
    (hidentity : A = D*poleDenominator s r*P +
      D*(∑ i ∈ s, C (b i)*poleDenominator (s.erase i) r) +
      ∑ k ∈ t, C (c k)*poleDenominator s r*Dk k)
    (hsep : ∀ i ∈ s, ∀ j ∈ s.erase i, ‖r i-r j‖ = 1)
    (hd : ∀ i ∈ s, d i < p) (hY : ∀ n, ‖Y.coeff n‖ ≤ 1)
    (hdeg : A₀.natDegree ≤ p+1) (n : ℕ) :
    ‖(C (tauPolynomial P + ∑ k ∈ t, c k*analyticPoleValue (v k)) +
      ∑ i ∈ s, C (b i)*(C (localHarmonic (d i))-Y)).coeff n‖ ≤ 1 := by
  apply canonical_local_coefficient_bound hp7 (splitFarExpansion A₀ A₁ V u)
    A D P s r d b t v c Y
    (splitFarExpansion_integral A₀ A₁ V u hA₀ hA₁ hV hu) hr hinj
    (by rw [hD]; exact farUnitDenominator_ne_zero V u hV hu) hv
  · intro i hi
    rw [hb i hi, (splitFarExpansion_hasSum A₀ A₁ V u (r i) hV hu (hr i)).tsum_eq]
    simp only [hA, hD, eval_add, eval_mul, eval_C, div_div]
  · rw [hA, hD]
    exact splitFarExpansion_identity A₀ A₁ V u hA₀ hA₁ hV hu
  · have hc := canonical_powerSeries_identity A D (poleDenominator s r) P
      (∑ i ∈ s, C (b i)*poleDenominator (s.erase i) r) t v c Dk hv0 hDk hidentity
    have he := map_sum (Polynomial.coeToPowerSeries.ringHom (R := ℚ_[p]))
      (fun i => C (b i)*poleDenominator (s.erase i) r) s
    simp only [coeToPowerSeries.ringHom_apply, coe_mul, coe_C] at he
    rwa [he] at hc
  · exact hsep
  · exact hd
  · exact hY
  · exact (splitFarExpansion_zero_degree A₀ A₁ V u).trans hdeg

#print axioms canonical_split_coefficient_bound
end Zeta5Local
