import SmallPrimeProducts

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5Local
open IsUltrametricDist

/-- The polynomial-part estimate behind Lemma 3.3, proved by selecting a nearest pole. -/
theorem partialFraction_polynomial_norm (p : ℕ) [Fact p.Prime]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (r : ι → ℚ_[p]) (c : ℚ_[p])
    (A : ℚ_[p] → ℚ_[p]) (x P : ℚ_[p]) (C D L : ℝ)
    (hne : s.Nonempty) (hC : 0 ≤ C) (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hx : ∀ i ∈ s, x ≠ r i)
    (hsep : ∀ j ∈ s, ∀ i ∈ s, j ≠ i → r j ≠ r i ∧ ‖r j-r i‖⁻¹ ≤ D)
    (hcenter : ∀ j ∈ s, ‖reducedInverseProduct p s r c j (r j)‖ ≤ C)
    (hA : ∀ j ∈ s, ‖A (r j)‖ ≤ 1)
    (hLip : ∀ j ∈ s, ‖A x-A (r j)‖ ≤ L * ‖x-r j‖)
    (hpart : P = c*A x/(∏ i ∈ s, (x-r i)) -
      ∑ i ∈ s, A (r i)*reducedInverseProduct p s r c i (r i)/(x-r i)) :
    ‖P‖ ≤ C * max L D := by
  obtain ⟨j, hj, hnear⟩ := s.exists_min_image (fun i => ‖x-r i‖) hne
  have hsep' (i) (hi : i ∈ s.erase j) :=
    hsep j hj i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi).symm
  have hF := reducedInverseProduct_bounds p s r c j x C D hC hD hx hsep' hnear (hcenter j hj)
  let F := reducedInverseProduct p s r c j
  let v : ι → ℚ_[p] := fun i => A (r i)*reducedInverseProduct p s r c i (r i)/(x-r i)
  have hreg : ‖(A x*F x - A (r j)*F (r j))/(x-r j)‖ ≤ C * max L D := by
    have hex : A x*F x - A (r j)*F (r j) =
        (A x-A (r j))*F x + A (r j)*(F x-F (r j)) := by ring
    have hnum : ‖A x*F x-A (r j)*F (r j)‖ ≤ ‖x-r j‖*(C*max L D) := by
      rw [hex]
      apply (norm_add_le_max _ _).trans
      apply max_le
      · rw [norm_mul]
        have hb := mul_le_mul (hLip j hj) hF.1 (norm_nonneg _) (by positivity)
        have hLD := mul_le_mul_of_nonneg_left (le_max_left L D) (mul_nonneg (norm_nonneg (x-r j)) hC)
        nlinarith
      · rw [norm_mul]
        have hb := mul_le_mul (hA j hj) hF.2 (norm_nonneg _) (by norm_num : (0:ℝ)≤1)
        have hLD := mul_le_mul_of_nonneg_left (le_max_right L D) (mul_nonneg (norm_nonneg (x-r j)) hC)
        nlinarith
    rw [norm_div]
    apply (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr (hx j hj)))).mpr
    simpa only [mul_comm] using hnum
  have hv : ‖∑ i ∈ s.erase j, v i‖ ≤ C*max L D := by
    apply norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    dsimp [v]
    rw [norm_div, norm_mul, div_eq_mul_inv]
    have hs := hsep' i hi
    have hdist := nearest_pole_distance p x (r j) (r i) (hnear i (Finset.mem_of_mem_erase hi))
    have hxi : x-r i ≠ 0 := sub_ne_zero.mpr (hx i (Finset.mem_of_mem_erase hi))
    have hiD : ‖x-r i‖⁻¹ ≤ D :=
      ((inv_le_inv₀ (norm_pos_iff.mpr hxi)
        (norm_pos_iff.mpr (sub_ne_zero.mpr hs.1))).mpr hdist).trans hs.2
    have hb := mul_le_mul
      (mul_le_mul (hA i (Finset.mem_of_mem_erase hi))
        (hcenter i (Finset.mem_of_mem_erase hi)) (norm_nonneg _) (by norm_num : (0:ℝ)≤1))
      hiD (by positivity) (by positivity)
    simp only [one_mul] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left (le_max_right L D) hC)
  have hprod0 : (∏ i ∈ s.erase j, (x-r i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i hi => sub_ne_zero.mpr (hx i (Finset.mem_of_mem_erase hi)))
  have hxj0 := sub_ne_zero.mpr (hx j hj)
  have he : P = (A x*F x-A (r j)*F (r j))/(x-r j) - ∑ i ∈ s.erase j, v i := by
    rw [hpart, ← Finset.sum_erase_add s v hj]
    change _ = _
    rw [← Finset.prod_erase_mul s (fun i => x-r i) hj]
    dsimp [F, reducedInverseProduct, v]
    field_simp
    ring
  rw [he]
  rw [sub_eq_add_neg]
  exact (norm_add_le_max _ _).trans (max_le hreg (by simpa only [norm_neg] using hv))

#print axioms partialFraction_polynomial_norm
end Zeta5Local
