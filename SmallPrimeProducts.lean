import SmallPrimeLipschitz

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5Local
open IsUltrametricDist

lemma norm_prod_sub_one_le (p : ℕ) [Fact p.Prime] {ι : Type*}
    (s : Finset ι) (u : ι → ℚ_[p]) (B : ℝ) (hB : 0 ≤ B)
    (hu : ∀ i ∈ s, ‖u i‖ ≤ 1) (hd : ∀ i ∈ s, ‖u i-1‖ ≤ B) :
    ‖(∏ i ∈ s, u i)-1‖ ≤ B := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hB
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have he : u a * (∏ i ∈ s, u i) - 1 =
        u a * ((∏ i ∈ s, u i)-1) + (u a-1) := by ring
    rw [he]
    apply (norm_add_le_max _ _).trans
    apply max_le
    · rw [norm_mul]
      exact (mul_le_mul (hu a (Finset.mem_insert_self _ _))
        (ih (fun i hi => hu i (Finset.mem_insert_of_mem hi))
          (fun i hi => hd i (Finset.mem_insert_of_mem hi)))
        (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
    · exact hd a (Finset.mem_insert_self _ _)

/-- Choosing a nearest pole controls every remaining denominator factor. -/
lemma nearest_pole_distance (p : ℕ) [Fact p.Prime] (x r s : ℚ_[p])
    (h : ‖x-r‖ ≤ ‖x-s‖) : ‖r-s‖ ≤ ‖x-s‖ := by
  have he : r-s = -(x-r)+(x-s) := by ring
  rw [he]
  apply (norm_add_le_max _ _).trans
  rw [norm_neg]
  exact max_le h le_rfl

/-- The inverse product away from the chosen pole. -/
noncomputable def reducedInverseProduct {ι : Type*} [DecidableEq ι]
    (p : ℕ) [Fact p.Prime] (s : Finset ι) (r : ι → ℚ_[p]) (c : ℚ_[p]) (j : ι)
    (x : ℚ_[p]) : ℚ_[p] := c / ∏ i ∈ s.erase j, (x-r i)

/-- Both estimates for F_r follow from a nearest pole, without splitting into balls. -/
theorem reducedInverseProduct_bounds (p : ℕ) [Fact p.Prime] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (r : ι → ℚ_[p]) (c : ℚ_[p]) (j : ι) (x : ℚ_[p])
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hx : ∀ i ∈ s, x ≠ r i)
    (hsep : ∀ i ∈ s.erase j, r j ≠ r i ∧ ‖r j-r i‖⁻¹ ≤ D)
    (hnear : ∀ i ∈ s, ‖x-r j‖ ≤ ‖x-r i‖)
    (hcenter : ‖reducedInverseProduct p s r c j (r j)‖ ≤ C) :
    ‖reducedInverseProduct p s r c j x‖ ≤ C ∧
      ‖reducedInverseProduct p s r c j x - reducedInverseProduct p s r c j (r j)‖ ≤
        C * ‖x-r j‖ * D := by
  let u : ι → ℚ_[p] := fun i => (r j-r i)/(x-r i)
  have hx0 (i) (hi : i ∈ s.erase j) : x-r i ≠ 0 :=
    sub_ne_zero.mpr (hx i (Finset.mem_of_mem_erase hi))
  have hd (i) (hi : i ∈ s.erase j) : ‖r j-r i‖ ≤ ‖x-r i‖ :=
    nearest_pole_distance p x (r j) (r i) (hnear i (Finset.mem_of_mem_erase hi))
  have hu (i) (hi : i ∈ s.erase j) : ‖u i‖ ≤ 1 := by
    dsimp [u]
    rw [norm_div]
    exact (div_le_one (norm_pos_iff.mpr (hx0 i hi))).mpr (hd i hi)
  have hdelta (i) (hi : i ∈ s.erase j) : ‖u i-1‖ ≤ ‖x-r j‖ * D := by
    have he : u i-1 = -(x-r j)/(x-r i) := by
      dsimp [u]
      field_simp [hx0 i hi]
      ring
    rw [he, norm_div, norm_neg, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (inv_le_inv₀ (norm_pos_iff.mpr (hx0 i hi))
      (norm_pos_iff.mpr (sub_ne_zero.mpr (hsep i hi).1))).mpr (hd i hi) |>.trans (hsep i hi).2
  have hprod : ‖∏ i ∈ s.erase j, u i‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one (fun i _ => norm_nonneg _) hu
  have he : reducedInverseProduct p s r c j x =
      reducedInverseProduct p s r c j (r j) * ∏ i ∈ s.erase j, u i := by
    unfold reducedInverseProduct
    simp only [u, Finset.prod_div_distrib]
    have hr0 : (∏ i ∈ s.erase j, (r j-r i)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i hi => sub_ne_zero.mpr (hsep i hi).1)
    field_simp
  constructor
  · rw [he, norm_mul]
    exact (mul_le_mul hcenter hprod (norm_nonneg _) hC).trans_eq (mul_one _)
  · rw [he, ← mul_sub_one, norm_mul]
    have hb := norm_prod_sub_one_le p (s.erase j) u (‖x-r j‖*D)
      (by positivity) hu hdelta
    exact (mul_le_mul hcenter hb (norm_nonneg _) hC).trans_eq (by ring)

#print axioms reducedInverseProduct_bounds
end Zeta5Local
