import OuterLow

/-! The outer zero class: one or two poles and the exceptional row weights. -/
noncomputable section
open scoped BigOperators
open Polynomial Finset
namespace Zeta5OuterZero
open Zeta5Construction Zeta5OuterMoments Zeta5OuterBasis Zeta5OuterNear Zeta5OuterArithmetic
open Zeta5Outer Zeta5OuterEntries Zeta5NumeratorFunctional Zeta5FunctionalCancellation Zeta5OuterLow

lemma zero_class_dvd (p m N h : ℕ) (hp : p = 2*m+1) (a : Fin (m+1))
    (ha : a.val = 0) (k : Fin h) (hk : k ∈ classMembers p m N h hp a) :
    p ∣ poleIndex N k := by
  have hc := congrArg Fin.val ((mem_filter.mp hk).2)
  simp only [poleClass, ha] at hc
  have hr := Nat.mod_lt (poleIndex N k) (by omega : 0 < p)
  apply Nat.dvd_of_mod_eq_zero
  omega

lemma zero_pole_values (p m N h : ℕ) (hp : p = 2*m+1) (hK : N+h < 3*p)
    (a : Fin (m+1)) (ha : a.val = 0) (k : Fin h)
    (hk : k ∈ classMembers p m N h hp a) :
    poleIndex N k = p ∨ poleIndex N k = 2*p := by
  obtain ⟨t, ht⟩ := zero_class_dvd p m N h hp a ha k hk
  have ht0 : 0 < t := by have := poleIndex_pos N k; nlinarith
  have ht3 : t < 3 := by
    have hklt := k.isLt
    have hidx : poleIndex N k < 3*p := by unfold poleIndex; omega
    nlinarith
  interval_cases t <;> omega

lemma prime_power_integer_valuation (p n : ℕ) [Fact p.Prime] (z : ℤ)
    (hz : (p : ℤ)^n ∣ z) : ((n : ℚ) : WithTop ℚ) ≤ rationalPadicValuation p (z : ℚ) := by
  apply (rationalPadicValuation_lower_iff p _ (n : ℚ)).mpr
  rcases (padicValInt_dvd_iff n z).mp hz with hz0 | hn
  · left
    exact_mod_cast hz0
  · right
    rw [padicValRat.of_int]
    exact_mod_cast hn

lemma zero_linear_factor_valuation (p m N h : ℕ) [Fact p.Prime]
    (hp : p = 2*m+1) (a : Fin (m+1)) (ha : a.val = 0) (k : Fin h)
    (hk : k ∈ classMembers p m N h hp a) :
    (2 : WithTop ℚ) ≤ rationalPadicValuation p (node N k+(p : ℚ)^2) := by
  obtain ⟨t, ht⟩ := zero_class_dvd p m N h hp a ha k hk
  have hz : (p : ℤ)^2 ∣ -((poleIndex N k : ℤ)^2)+(p : ℤ)^2 := by
    refine ⟨1-(t : ℤ)^2, ?_⟩
    rw [ht]
    push_cast
    ring
  have hh := prime_power_integer_valuation p 2 _ hz
  simpa only [Int.cast_add, Int.cast_neg, Int.cast_pow, Int.cast_natCast, Nat.cast_ofNat, node,
    WithTop.coe_ofNat] using hh

lemma zero_row_eval_lower (p m N h : ℕ) [Fact p.Prime]
    (hp : p = 2*m+1) (a : Fin (m+1)) (ha : a.val = 0)
    (i : Fin (classDimension p m N h hp a)) (k : Fin h)
    (hk : k ∈ classMembers p m N h hp a) :
    (((2*(i.val : ℚ)) : ℚ) : WithTop ℚ) ≤ rationalPadicValuation p
      (((localRow p m N h hp a i).map (Int.castRingHom ℚ)).eval (node N k)) := by
  have hr : (localRow p m N h hp a i).map (Int.castRingHom ℚ) =
      (X+C ((p : ℚ)^2))^i.val := by simp [localRow, ha]
  rw [hr, eval_pow, eval_add, eval_X, eval_C]
  have hh := valuation_pow_lower (rationalPadicValuation p) _ 2
    (by simpa only [WithTop.coe_ofNat] using zero_linear_factor_valuation p m N h hp a ha k hk) i.val
  simpa only [mul_comm] using hh

lemma prime_square_difference_value (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    padicValRat p ((p : ℚ)^2-((2*p : ℕ) : ℚ)^2) = 2 := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have h3 : padicValRat p (-3 : ℚ) = 0 := by
    rw [padicValRat.neg]
    change padicValRat p ((3 : ℕ) : ℚ) = 0
    rw [padicValRat.of_nat]
    rw [padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))]
    rfl
  rw [show (p : ℚ)^2-((2*p : ℕ) : ℚ)^2 = -3*(p : ℚ)^2 by push_cast; ring,
    padicValRat.mul (by norm_num) (pow_ne_zero _ hp0), h3, padicValRat.pow,
    padicValRat.self (Fact.out : p.Prime).one_lt]
  norm_num

lemma zero_difference_padicVal_le_two (p m N h : ℕ) [Fact p.Prime]
    (hp : p = 2*m+1) (hp5 : 5 ≤ p) (hK : N+h < 3*p)
    (a : Fin (m+1)) (ha : a.val = 0) (k l : Fin h)
    (hk : k ∈ classMembers p m N h hp a) (hl : l ∈ classMembers p m N h hp a) (hkl : k ≠ l) :
    padicValRat p (node N k-node N l) ≤ 2 := by
  have hneq : poleIndex N k ≠ poleIndex N l := fun hh => hkl (poleIndex_injective N h hh)
  rcases zero_pole_values p m N h hp hK a ha k hk with hk' | hk' <;>
    rcases zero_pole_values p m N h hp hK a ha l hl with hl' | hl'
  · exact False.elim (hneq (hk'.trans hl'.symm))
  · have he : node N k-node N l = -((p : ℚ)^2-((2*p : ℕ) : ℚ)^2) := by
      simp only [node, hk', hl']; ring
    rw [he, padicValRat.neg, prime_square_difference_value p hp5]
  · have he : node N k-node N l = (p : ℚ)^2-((2*p : ℕ) : ℚ)^2 := by
      simp only [node, hk', hl']; ring
    rw [he, prime_square_difference_value p hp5]
  · exact False.elim (hneq (hk'.trans hl'.symm))

#print axioms zero_difference_padicVal_le_two
lemma zero_classDimension_le_two (p m N h : ℕ) (hp : p = 2*m+1) (hK : N+h < 3*p)
    (a : Fin (m+1)) (ha : a.val = 0) : classDimension p m N h hp a ≤ 2 := by
  have hs : (classMembers p m N h hp a).image (poleIndex N) ⊆ ({p,2*p} : Finset ℕ) := by
    intro j hj
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
    simpa only [mem_insert, mem_singleton] using zero_pole_values p m N h hp hK a ha k hk
  have hh := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ (poleIndex_injective N h)] at hh
  have hpp : p ≠ 2*p := by omega
  simpa only [Finset.card_pair hpp, classDimension] using hh

lemma zero_derivative_inverse_lower (p m N h : ℕ) [Fact p.Prime]
    (hp : p = 2*m+1) (hp5 : 5 ≤ p) (hK : N+h < 3*p)
    (a : Fin (m+1)) (ha : a.val = 0) (k : Fin h)
    (hk : k ∈ classMembers p m N h hp a) :
    (((-2*((classDimension p m N h hp a-1 : ℕ) : ℚ)) : ℚ) : WithTop ℚ) ≤
      rationalPadicValuation p (((selectedTail N (classMembers p m N h hp a)).derivative.eval
        (node N k))⁻¹) := by
  rw [selected_derivative_at_node N _ k hk, ← Finset.prod_inv_distrib]
  have hh := valuation_prod_lower (rationalPadicValuation p)
    ((classMembers p m N h hp a).erase k) (fun l => (node N k-node N l)⁻¹) (fun _ => (-2 : ℚ))
    (by
      intro l hl
      apply (rationalPadicValuation_lower_iff p _ (-2)).mpr
      right
      rw [padicValRat.inv]
      have hv := zero_difference_padicVal_le_two p m N h hp hp5 hK a ha k l hk
        (mem_of_mem_erase hl) (by exact Ne.symm (mem_erase.mp hl).1)
      exact_mod_cast (show (-2 : ℤ) ≤ -padicValRat p (node N k-node N l) by omega))
  simpa only [Finset.sum_const, Finset.card_erase_of_mem hk, nsmul_eq_mul,
    mul_comm, classDimension] using hh

lemma zero_classEntryNumerator_eval_lower (p m N h : ℕ) [Fact p.Prime]
    (hp : p = 2*m+1) (a : Fin (m+1)) (ha : a.val = 0)
    (i j : Fin (classDimension p m N h hp a)) (k : Fin h)
    (hk : k ∈ classMembers p m N h hp a) :
    (((2*(i.val : ℚ)+2*j.val) : ℚ) : WithTop ℚ) ≤ rationalPadicValuation p
      (((classEntryNumerator p m N h hp a i j).map (Int.castRingHom ℚ)).eval (node N k)) := by
  have hD := integer_eval_at_node_integral p N (integerDenominator N ^ 5) k
  have hC := integer_eval_at_node_integral p N (classComplement p m N h hp a) k
  have hI := zero_row_eval_lower p m N h hp a ha i k hk
  have hJ := zero_row_eval_lower p m N h hp a ha j k hk
  unfold classEntryNumerator
  rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_mul,
    eval_mul, eval_mul, eval_mul, AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_mul]
  have hh := add_le_add (add_le_add (add_le_add hD hC) hI) hJ
  simpa only [zero_add, ← WithTop.coe_add] using hh

/-- The source zero-class residue bounds: at least -1 for the single row;
at least 2i+2j-3 in the two-pole case. -/
theorem zero_residue_lower (p m N h : ℕ) [Fact p.Prime]
    (hp : p = 2*m+1) (hp5 : 5 ≤ p) (hK : N+h < 3*p) (hK2 : 2*(N+h) < p^2)
    (a : Fin (m+1)) (ha : a.val = 0)
    (i j : Fin (classDimension p m N h hp a))
    (k : Fin h) (hk : k ∈ classMembers p m N h hp a) :
    CoeffLower (rationalPadicValuation p)
      (C (((classEntryNumerator p m N h hp a i j).map (Int.castRingHom ℚ)).eval (node N k) /
        (selectedTail N (classMembers p m N h hp a)).derivative.eval (node N k)) *
          poleFunctional (poleIndex N k))
      (2*(i.val : ℚ)+2*j.val-2*((classDimension p m N h hp a-1 : ℕ) : ℚ)-1) := by
  have hI := zero_derivative_inverse_lower p m N h hp hp5 hK a ha k hk
  have hP := zero_classEntryNumerator_eval_lower p m N h hp a ha i j k hk
  have hres : (((2*(i.val : ℚ)+2*j.val)-
      2*((classDimension p m N h hp a-1 : ℕ) : ℚ) : ℚ) : WithTop ℚ) ≤
      rationalPadicValuation p
        (((classEntryNumerator p m N h hp a i j).map (Int.castRingHom ℚ)).eval (node N k) /
          (selectedTail N (classMembers p m N h hp a)).derivative.eval (node N k)) := by
    rw [div_eq_mul_inv, AddValuation.map_mul]
    have hh := add_le_add hP hI
    simpa only [← WithTop.coe_add, sub_eq_add_neg, neg_mul] using hh
  have hkp : poleIndex N k < p^2 := by have := k.isLt; unfold poleIndex; omega
  have hh := coeffLower_mul (rationalPadicValuation p) (coeffLower_C _ _ _ hres)
    (poleFunctional_lower_one p (poleIndex N k) hp5 (poleIndex_pos N k) hkp
      (zero_class_dvd p m N h hp a ha k hk))
  simpa only [sub_eq_add_neg] using hh

def zeroWeight (p m N h : ℕ) (hp : p = 2*m+1) (a : Fin (m+1))
    (i : Fin (classDimension p m N h hp a)) : ℚ :=
  if classDimension p m N h hp a = 1 then -1/2 else 2*(i.val : ℚ)-2

lemma zeroWeight_nonpos (p m N h : ℕ) (hp : p = 2*m+1) (hK : N+h < 3*p)
    (a : Fin (m+1)) (ha : a.val = 0) (i : Fin (classDimension p m N h hp a)) :
    zeroWeight p m N h hp a i ≤ 0 := by
  have hd := zero_classDimension_le_two p m N h hp hK a ha
  have hi := i.isLt
  unfold zeroWeight
  split_ifs
  · norm_num
  · have hi' : (i.val : ℚ) ≤ 1 := by exact_mod_cast (show i.val ≤ 1 by omega)
    linarith

/-- All actual zero-class entry bounds, with the exceptional half-integer weight. -/
theorem zero_entry_weighted_bound (p m N h : ℕ) [Fact p.Prime]
    (hp : p = 2*m+1) (hp7 : 7 ≤ p) (hK : N+h < 3*p) (hK2 : 2*(N+h) < p^2)
    (a : Fin (m+1)) (ha : a.val = 0)
    (i j : Fin (classDimension p m N h hp a)) :
    CoeffLower (rationalPadicValuation p)
      (numeratorFunctional N h (correctedMomentLinearMap p)
        (denominator N ^ 5 *
          ((globalRow p m N h hp a i).map (Int.castRingHom ℚ) *
           (globalRow p m N h hp a j).map (Int.castRingHom ℚ))))
      (zeroWeight p m N h hp a i + zeroWeight p m N h hp a j) := by
  rw [classEntryNumerator_identity, numeratorFunctional_cancel_subset]
  have hnonpos := add_nonpos (zeroWeight_nonpos p m N h hp hK a ha i)
    (zeroWeight_nonpos p m N h hp hK a ha j)
  apply coeffLower_add_same
  · exact coeffLower_mono _ (coeffLower_C _ _ 0
      (corrected_selected_quotient_integral p N hp7 _ (classEntryNumerator p m N h hp a i j))) hnonpos
  · apply coeffLower_mono _ ?_
      (show zeroWeight p m N h hp a i + zeroWeight p m N h hp a j ≤
        2*(i.val : ℚ)+2*j.val-2*((classDimension p m N h hp a-1 : ℕ) : ℚ)-1 by
        have hd := zero_classDimension_le_two p m N h hp hK a ha
        have hi := i.isLt
        have hj := j.isLt
        unfold zeroWeight
        split_ifs with hd1
        · have hi0 : i.val = 0 := by omega
          have hj0 : j.val = 0 := by omega
          simp [hd1, hi0, hj0]
        · have hd2 : classDimension p m N h hp a = 2 := by omega
          simp only [hd2]
          norm_num
          linarith)
    apply coeffLower_sum
    intro k hk
    exact zero_residue_lower p m N h hp (by omega) hK hK2 a ha i j k hk

#print axioms zero_entry_weighted_bound
end Zeta5OuterZero
