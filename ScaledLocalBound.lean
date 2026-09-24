import PartitionCertificate

namespace Zeta5Local
open Polynomial IsUltrametricDist
variable {p : ℕ} [Fact p.Prime]
variable {ι : Type*} [DecidableEq ι]

lemma farUnitDenominator_eval_ne_zero (V : Polynomial ℚ_[p]) (u x : ℚ_[p])
    (hV : ∀ n, ‖V.coeff n‖ ≤ 1) (hu : ‖u‖ = 1) (hx : ‖x‖ ≤ 1) :
    (C u+C (p : ℚ_[p])*V).eval x ≠ 0 := by
  simp only [eval_add, eval_mul, eval_C]
  intro hz
  have he : u = -((p : ℚ_[p])*V.eval x) := by linear_combination hz
  have hn : ‖(p : ℚ_[p])*V.eval x‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (integral_polynomial_eval V x hV hx)).trans_lt
      Padic.norm_p_lt_one
  rw [← norm_neg, ← he, hu] at hn
  exact (lt_irrefl 1) hn

lemma tauPolynomial_C_mul (P : Polynomial ℚ_[p]) (c : ℚ_[p]) :
    tauPolynomial (C c*P) = c*tauPolynomial P := by
  rw [← tauPowerSeries_polynomial, coe_mul, coe_C, tauPowerSeries_C_mul,
    tauPowerSeries_polynomial]

/-- The actual scaled rational presentation is locally integral after
normalization by β/α. All near/far partition and residue obligations follow
from its finite polynomial certificate and the disk factorizations. -/
theorem scaled_presentation_local_bound (hp7 : 7 ≤ p)
    (N E P A₀ A₁ V : Polynomial ℚ_[p]) (u α β : ℚ_[p])
    (s near : Finset ι) (hne : near ⊆ s) (r c : ι → ℚ_[p])
    (Ei : ι → Polynomial ℚ_[p]) (d : ι → ℕ) (Y : Polynomial ℚ_[p])
    (hα : α ≠ 0) (hβ : β ≠ 0)
    (hN : N = C α*(A₀+C (p : ℚ_[p])*A₁))
    (hE : E = C β*poleDenominator near r*(C u+C (p : ℚ_[p])*V))
    (hEi : ∀ i ∈ s, E = (X-C (r i))*Ei i)
    (hidentity : N = E*P + ∑ i ∈ s, C (c i)*Ei i)
    (hA₀ : ∀ n, ‖A₀.coeff n‖ ≤ 1) (hA₁ : ∀ n, ‖A₁.coeff n‖ ≤ 1)
    (hV : ∀ n, ‖V.coeff n‖ ≤ 1) (hu : ‖u‖ = 1)
    (hr : ∀ i ∈ near, ‖r i‖ ≤ 1) (hinj : Set.InjOn r near)
    (hsep : ∀ i ∈ near, ∀ j ∈ near.erase i, ‖r i-r j‖ = 1)
    (hfar : ∀ i ∈ s\near, 1 < ‖r i‖)
    (hd : ∀ i ∈ near, d i < p) (hY : ∀ n, ‖Y.coeff n‖ ≤ 1)
    (hdeg : A₀.natDegree ≤ p+1) (n : ℕ) :
    ‖(C (β/α) * (C (tauPolynomial P + ∑ i ∈ s\near, c i*analyticPoleValue (r i)) +
      ∑ i ∈ near, C (c i)*(C (localHarmonic (d i))-Y))).coeff n‖ ≤ 1 := by
  let A := A₀+C (p : ℚ_[p])*A₁
  let D := C u+C (p : ℚ_[p])*V
  let Di (i : ι) := D/(X-C (r i))
  have hTi (i : ι) (hi : i ∈ near) : poleDenominator near r =
      (X-C (r i))*poleDenominator (near.erase i) r :=
    Lagrange.nodal_eq_mul_nodal_erase hi
  have hDi (i : ι) (hi : i ∈ s\near) : D = (X-C (r i))*Di i := by
    apply far_factor_of_scaled_denominator E (poleDenominator near r) D (Ei i) β (r i)
      hβ _ hE (hEi i (Finset.mem_sdiff.mp hi).1)
    apply Lagrange.eval_nodal_not_at_node
    intro j hj heq
    have hh := hfar i hi
    rw [heq] at hh
    exact (not_lt_of_ge (hr j hj)) hh
  have hc := presentation_normalize_partition N E A D (poleDenominator near r) P s near hne
    r c Ei (fun i => poleDenominator (near.erase i) r) Di α β hα hN hE hEi hTi hDi hidentity
  have hb (i : ι) (hi : i ∈ near) : (β/α)*c i =
      A.eval (r i)/(D.eval (r i)*(∏ j ∈ near.erase i, (r i-r j))) :=
    near_residue_from_certificate A D (C (β/α)*P) near r (fun i => (β/α)*c i) hinj
      (s\near) (fun i => (β/α)*c i) Di hc i hi
      (farUnitDenominator_eval_ne_zero V u (r i) hV hu (hr i hi))
  let rn (i : ι) := if i ∈ near then r i else 0
  have hrn (i : ι) (hi : i ∈ near) : rn i = r i := if_pos hi
  have hTr : poleDenominator near rn = poleDenominator near r := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [hrn i hi]
  have hTer (i : ι) : poleDenominator (near.erase i) rn = poleDenominator (near.erase i) r := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [hrn j (Finset.mem_of_mem_erase hj)]
  have hb' (i : ι) (hi : i ∈ near) : (β/α)*c i =
      A.eval (rn i)/(D.eval (rn i)*(∏ j ∈ near.erase i, (rn i-rn j))) := by
    rw [hrn i hi, hb i hi]
    have hprod : (∏ j ∈ near.erase i, (r i-r j)) = ∏ j ∈ near.erase i, (r i-rn j) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [hrn j (Finset.mem_of_mem_erase hj)]
    rw [hprod]
  have hnorm := canonical_split_coefficient_bound hp7 A₀ A₁ V A D (C (β/α)*P) u
    near rn d (fun i => (β/α)*c i) (s\near) r (fun i => (β/α)*c i) Di Y
    rfl rfl hA₀ hA₁ hV hu
    (fun i => by dsimp [rn]; split_ifs with hi; exact hr i hi; norm_num)
    (by intro i hi j hj heq; apply hinj hi hj; simpa only [hrn i hi, hrn j hj] using heq)
    (fun i hi => by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ (hfar i hi))
    (fun i hi => by intro hz; have hh := hfar i hi; norm_num [hz] at hh)
    hb' hDi
    (by simpa only [hTr, hTer] using hc)
    (by intro i hi j hj; simpa only [hrn i hi, hrn j (Finset.mem_of_mem_erase hj)] using hsep i hi j hj)
    hd hY hdeg n
  convert! hnorm using 1
  congr 2
  simp only [tauPolynomial_C_mul, map_add, map_mul, map_sum,
    mul_add, Finset.mul_sum, mul_sub, Finset.sum_sub_distrib, mul_assoc]

#print axioms scaled_presentation_local_bound
end Zeta5Local
