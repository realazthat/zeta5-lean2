import OuterPoleArithmetic

/-! Ordinary low-row residue bounds in the actual class basis. -/
noncomputable section
open scoped BigOperators
open Polynomial Finset
namespace Zeta5OuterLow
open Zeta5Construction Zeta5OuterMoments Zeta5OuterBasis Zeta5OuterNear Zeta5OuterArithmetic
open Zeta5Outer Zeta5OuterEntries Zeta5NumeratorFunctional Zeta5FunctionalCancellation

lemma selected_derivative_at_node (N : ℕ) {h : ℕ} (s : Finset (Fin h))
    (k : Fin h) (hk : k ∈ s) :
    (selectedTail N s).derivative.eval (node N k) =
      ∏ l ∈ s.erase k, (node N k-node N l) := by
  unfold selectedTail
  rw [← Finset.mul_prod_erase _ _ hk]
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero,
    eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, eval_one,
    one_mul, add_zero, eval_prod]

lemma ordinary_derivative_inverse_lower (p m N h : ℕ) [Fact p.Prime]
    (hp : p = 2*m+1) (hp3 : 3 ≤ p) (hK : 2*(N+h) < p^2)
    (a : Fin (m+1)) (ha : 0 < a.val) (k : Fin h)
    (hk : k ∈ classMembers p m N h hp a) :
    (((-((classDimension p m N h hp a - 1 : ℕ) : ℚ)) : ℚ) : WithTop ℚ) ≤
      rationalPadicValuation p (((selectedTail N (classMembers p m N h hp a)).derivative.eval
        (node N k))⁻¹) := by
  rw [selected_derivative_at_node N _ k hk, ← Finset.prod_inv_distrib]
  have hh := valuation_prod_lower (rationalPadicValuation p)
    ((classMembers p m N h hp a).erase k) (fun l => (node N k-node N l)⁻¹) (fun _ => (-1 : ℚ))
    (by
      intro l hl
      apply (rationalPadicValuation_lower_iff p _ (-1)).mpr
      right
      rw [padicValRat.inv]
      have hv := ordinary_difference_padicVal_le_one p m N h hp hp3 hK a ha k l hk
        (by exact Ne.symm (mem_erase.mp hl).1)
      exact_mod_cast (show (-1 : ℤ) ≤ -padicValRat p (node N k-node N l) by omega))
  simpa only [Finset.sum_const, Finset.card_erase_of_mem hk, nsmul_eq_mul, mul_neg,
    mul_one, classDimension] using hh

lemma node_integral (p N : ℕ) {h : ℕ} [Fact p.Prime] (k : Fin h) :
    (0 : WithTop ℚ) ≤ rationalPadicValuation p (node N k) := by
  have hh := rationalPadicValuation_int_nonneg p (-((poleIndex N k : ℤ)^2))
  simpa only [Int.cast_neg, Int.cast_pow, Int.cast_natCast, node] using hh

lemma integer_eval_at_node_integral (p N : ℕ) {h : ℕ} [Fact p.Prime]
    (P : ℤ[X]) (k : Fin h) :
    (0 : WithTop ℚ) ≤ rationalPadicValuation p ((P.map (Int.castRingHom ℚ)).eval (node N k)) :=
  polynomial_eval_integral (rationalPadicValuation p) _ (coeffLower_integer_map p P) _ (node_integral p N k)

lemma valuation_pow_lower {F : Type*} [Field F] (v : AddValuation F (WithTop ℚ))
    (x : F) (e : ℚ) (hx : (e : WithTop ℚ) ≤ v x) (n : ℕ) :
    (((n : ℚ)*e : ℚ) : WithTop ℚ) ≤ v (x^n) := by
  rw [AddValuation.map_pow]
  have hh := nsmul_le_nsmul_right hx n
  rw [← WithTop.coe_nsmul] at hh
  simpa only [nsmul_eq_mul] using hh

/-- The small class representative contributes a factor to D_N exactly when removed. -/
lemma integerDenominator_factor (N a : ℕ) (ha : 0 < a) (hNa : a ≤ N) :
    (X+C ((a : ℤ)^2) : ℤ[X]) ∣ integerDenominator N := by
  have hm : a-1 ∈ range N := by simp only [mem_range]; omega
  have hh := Finset.dvd_prod_of_mem (fun k => (X+C (((k+1 : ℕ) : ℤ)^2) : ℤ[X])) hm
  simpa only [show a-1+1=a by omega, integerDenominator] using hh

def removedIndicator (N a : ℕ) : ℕ := if a ≤ N then 1 else 0

lemma removed_denominator_eval_lower (p m N h : ℕ) [Fact p.Prime]
    (hp : p = 2*m+1) (a : Fin (m+1)) (ha : 0 < a.val) (k : Fin h)
    (hk : k ∈ classMembers p m N h hp a) :
    ((removedIndicator N a.val : ℕ) : WithTop ℚ) ≤
      rationalPadicValuation p ((denominator N).eval (node N k)) := by
  unfold removedIndicator
  split_ifs with hNa
  · obtain ⟨q, hq⟩ := integerDenominator_factor N a.val ha hNa
    rw [← map_integerDenominator, hq, Polynomial.map_mul, eval_mul]
    have hlinear := class_linear_factor_valuation p m N h hp a k hk
    have hqv := integer_eval_at_node_integral p N q k
    rw [AddValuation.map_mul]
    have hh := add_le_add hlinear hqv
    simpa using hh
  · simpa only [Nat.cast_zero, map_integerDenominator] using integer_eval_at_node_integral p N (integerDenominator N) k

lemma low_row_eval_lower (p m N h : ℕ) [Fact p.Prime]
    (hp : p = 2*m+1) (a : Fin (m+1)) (ha : 0 < a.val)
    (i : Fin (classDimension p m N h hp a))
    (hi : i.val < (farFactor p m N h hp a).natDegree)
    (k : Fin h) (hk : k ∈ classMembers p m N h hp a) :
    (i.val : WithTop ℚ) ≤ rationalPadicValuation p
      (((localRow p m N h hp a i).map (Int.castRingHom ℚ)).eval (node N k)) := by
  have hr : (localRow p m N h hp a i).map (Int.castRingHom ℚ) =
      (X+C ((a.val : ℚ)^2))^i.val := by
    simp [localRow, show ¬a.val = 0 by omega, hi]
  rw [hr, eval_pow, eval_add, eval_X, eval_C]
  have hh := valuation_pow_lower (rationalPadicValuation p) _ 1
    (class_linear_factor_valuation p m N h hp a k hk) i.val
  simpa only [mul_one, WithTop.coe_natCast] using hh

#print axioms ordinary_derivative_inverse_lower
#print axioms removed_denominator_eval_lower
#print axioms low_row_eval_lower
def classComplement (p m N h : ℕ) (hp : p = 2*m+1) (a : Fin (m+1)) : ℤ[X] :=
  ∏ c ∈ univ.erase a, classFactor p m N h hp c

lemma classComplement_map (p m N h : ℕ) (hp : p = 2*m+1) (a : Fin (m+1)) :
    (classComplement p m N h hp a).map (Int.castRingHom ℚ) =
      omittedTail N (classMembers p m N h hp a) := by
  apply mul_right_cancel₀ (selectedTail_monic N (classMembers p m N h hp a)).ne_zero
  rw [← tail_split_selected]
  have hh : classComplement p m N h hp a * integerSelectedTail N (classMembers p m N h hp a) =
      integerTailDenominator N h := by
    change (∏ c ∈ univ.erase a, classFactor p m N h hp c) * classFactor p m N h hp a = _
    rw [Finset.prod_erase_mul _ _ (mem_univ a), classFactors_product]
  have hh' := congrArg (Polynomial.map (Int.castRingHom ℚ)) hh
  simpa only [Polynomial.map_mul, integerSelectedTail_map, map_integerTailDenominator] using hh'

def classEntryNumerator (p m N h : ℕ) (hp : p = 2*m+1) (a : Fin (m+1))
    (i j : Fin (classDimension p m N h hp a)) : ℤ[X] :=
  integerDenominator N^5 * classComplement p m N h hp a *
    localRow p m N h hp a i * localRow p m N h hp a j

/-- The actual same-class product, after its complementary denominator cancels. -/
lemma classEntryNumerator_identity (p m N h : ℕ) (hp : p = 2*m+1) (a : Fin (m+1))
    (i j : Fin (classDimension p m N h hp a)) :
    denominator N ^ 5 * ((globalRow p m N h hp a i).map (Int.castRingHom ℚ) *
      (globalRow p m N h hp a j).map (Int.castRingHom ℚ)) =
      omittedTail N (classMembers p m N h hp a) *
        (classEntryNumerator p m N h hp a i j).map (Int.castRingHom ℚ) := by
  rw [← classComplement_map]
  have hh : integerDenominator N ^ 5 *
      (globalRow p m N h hp a i * globalRow p m N h hp a j) =
      classComplement p m N h hp a * classEntryNumerator p m N h hp a i j := by
    unfold globalRow classEntryNumerator classComplement
    ring
  have hh' := congrArg (Polynomial.map (Int.castRingHom ℚ)) hh
  simpa only [Polynomial.map_mul, Polynomial.map_pow, map_integerDenominator] using hh'

lemma classEntryNumerator_eval_lower (p m N h : ℕ) [Fact p.Prime]
    (hp : p = 2*m+1) (a : Fin (m+1)) (ha : 0 < a.val)
    (i j : Fin (classDimension p m N h hp a))
    (hi : i.val < (farFactor p m N h hp a).natDegree)
    (hj : j.val < (farFactor p m N h hp a).natDegree)
    (k : Fin h) (hk : k ∈ classMembers p m N h hp a) :
    (((5*(removedIndicator N a.val : ℚ)+(i.val : ℚ)+j.val) : ℚ) : WithTop ℚ) ≤
      rationalPadicValuation p
        (((classEntryNumerator p m N h hp a i j).map (Int.castRingHom ℚ)).eval (node N k)) := by
  have hD := valuation_pow_lower (rationalPadicValuation p) _ (removedIndicator N a.val)
    (by simpa only [WithTop.coe_natCast] using removed_denominator_eval_lower p m N h hp a ha k hk) 5
  have hC := integer_eval_at_node_integral p N (classComplement p m N h hp a) k
  have hI := low_row_eval_lower p m N h hp a ha i hi k hk
  have hJ := low_row_eval_lower p m N h hp a ha j hj k hk
  unfold classEntryNumerator
  rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_pow,
    map_integerDenominator, eval_mul, eval_mul, eval_mul, eval_pow,
    AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_mul]
  have hh := add_le_add (add_le_add (add_le_add hD hC) hI) hJ
  simpa only [Nat.cast_ofNat, add_zero, ← WithTop.coe_natCast, ← WithTop.coe_add] using hh

/-- Each low/low ordinary residue has the bound advertised before (4.12). -/
theorem ordinary_low_residue_lower (p m N h : ℕ) [Fact p.Prime]
    (hp : p = 2*m+1) (hp5 : 5 ≤ p) (hK : 2*(N+h) < p^2)
    (a : Fin (m+1)) (ha : 0 < a.val)
    (i j : Fin (classDimension p m N h hp a))
    (hi : i.val < (farFactor p m N h hp a).natDegree)
    (hj : j.val < (farFactor p m N h hp a).natDegree)
    (k : Fin h) (hk : k ∈ classMembers p m N h hp a) :
    CoeffLower (rationalPadicValuation p)
      (C (((classEntryNumerator p m N h hp a i j).map (Int.castRingHom ℚ)).eval (node N k) /
        (selectedTail N (classMembers p m N h hp a)).derivative.eval (node N k)) *
          poleFunctional (poleIndex N k))
      ((i.val : ℚ)+j.val+5*(removedIndicator N a.val : ℚ)-classDimension p m N h hp a-4) := by
  have hdim : 0 < classDimension p m N h hp a := Finset.card_pos.mpr ⟨k,hk⟩
  have hI := ordinary_derivative_inverse_lower p m N h hp (by omega) hK a ha k hk
  have hP := classEntryNumerator_eval_lower p m N h hp a ha i j hi hj k hk
  have hres : (((5*(removedIndicator N a.val : ℚ)+(i.val : ℚ)+j.val)-
      ((classDimension p m N h hp a-1 : ℕ) : ℚ) : ℚ) : WithTop ℚ) ≤
      rationalPadicValuation p
        (((classEntryNumerator p m N h hp a i j).map (Int.castRingHom ℚ)).eval (node N k) /
          (selectedTail N (classMembers p m N h hp a)).derivative.eval (node N k)) := by
    rw [div_eq_mul_inv, AddValuation.map_mul]
    have hh := add_le_add hP hI
    simpa only [← WithTop.coe_add, sub_eq_add_neg] using hh
  have hkp : poleIndex N k < p^2 := by have := k.isLt; unfold poleIndex; omega
  have hh := coeffLower_mul (rationalPadicValuation p) (coeffLower_C _ _ _ hres)
    (poleFunctional_lower_five p (poleIndex N k) hp5 (poleIndex_pos N k) hkp)
  have heq : (5*(removedIndicator N a.val : ℚ)+(i.val : ℚ)+j.val)-
      ((classDimension p m N h hp a-1 : ℕ) : ℚ)+(-5) =
      (i.val : ℚ)+j.val+5*(removedIndicator N a.val : ℚ)-classDimension p m N h hp a-4 := by
    rw [Nat.cast_sub (by omega : 1 ≤ classDimension p m N h hp a), Nat.cast_one]
    ring
  rwa [heq] at hh

#print axioms ordinary_low_residue_lower
/-- The complete corrected low/low entry, including its integral polynomial part. -/
theorem ordinary_low_entry_lower (p m N h : ℕ) [Fact p.Prime]
    (hp : p = 2*m+1) (hp7 : 7 ≤ p) (hK : 2*(N+h) < p^2)
    (a : Fin (m+1)) (ha : 0 < a.val)
    (i j : Fin (classDimension p m N h hp a))
    (hi : i.val < (farFactor p m N h hp a).natDegree)
    (hj : j.val < (farFactor p m N h hp a).natDegree) :
    CoeffLower (rationalPadicValuation p)
      (numeratorFunctional N h (correctedMomentLinearMap p)
        (denominator N ^ 5 *
          ((globalRow p m N h hp a i).map (Int.castRingHom ℚ) *
           (globalRow p m N h hp a j).map (Int.castRingHom ℚ))))
      (min 0 ((i.val : ℚ)+j.val+5*(removedIndicator N a.val : ℚ)-classDimension p m N h hp a-4)) := by
  rw [classEntryNumerator_identity, numeratorFunctional_cancel_subset]
  apply coeffLower_add_same
  · apply coeffLower_mono _ (coeffLower_C _ _ 0
      (corrected_selected_quotient_integral p N hp7 _ (classEntryNumerator p m N h hp a i j)))
    exact min_le_left _ _
  · apply coeffLower_mono _ ?_ (min_le_right _ _)
    apply coeffLower_sum
    intro k hk
    exact ordinary_low_residue_lower p m N h hp (by omega) hK a ha i j hi hj k hk

/-- Equation (4.12) expressed with the actual surviving class dimension and
actual far-factor degree; the removed class count is a Boolean. -/
def ordinaryWeight (p m N h : ℕ) (hp : p = 2*m+1) (a : Fin (m+1))
    (i : Fin (classDimension p m N h hp a)) : ℚ :=
  if i.val < (farFactor p m N h hp a).natDegree then
    min 0 ((2*(i.val : ℚ)+5*(removedIndicator N a.val : ℚ)-classDimension p m N h hp a-4)/2)
  else 0

lemma ordinaryWeight_nonpos (p m N h : ℕ) (hp : p = 2*m+1) (a : Fin (m+1))
    (i : Fin (classDimension p m N h hp a)) : ordinaryWeight p m N h hp a i ≤ 0 := by
  unfold ordinaryWeight
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

/-- All actual ordinary same-class entry bounds are now discharged. -/
theorem ordinary_entry_weighted_bound (p m N h : ℕ) [Fact p.Prime]
    (hp : p = 2*m+1) (hp7 : 7 ≤ p) (hK : 2*(N+h) < p^2)
    (hNp : 2*N < p) (hKp : p ≤ N+h)
    (a : Fin (m+1)) (ha : 0 < a.val)
    (i j : Fin (classDimension p m N h hp a)) :
    CoeffLower (rationalPadicValuation p)
      (numeratorFunctional N h (correctedMomentLinearMap p)
        (denominator N ^ 5 *
          ((globalRow p m N h hp a i).map (Int.castRingHom ℚ) *
           (globalRow p m N h hp a j).map (Int.castRingHom ℚ))))
      (ordinaryWeight p m N h hp a i + ordinaryWeight p m N h hp a j) := by
  have hnonpos : ordinaryWeight p m N h hp a i + ordinaryWeight p m N h hp a j ≤ 0 :=
    add_nonpos (ordinaryWeight_nonpos _ _ _ _ _ _ _) (ordinaryWeight_nonpos _ _ _ _ _ _ _)
  by_cases hi : i.val < (farFactor p m N h hp a).natDegree
  · by_cases hj : j.val < (farFactor p m N h hp a).natDegree
    · apply coeffLower_mono _ (ordinary_low_entry_lower p m N h hp hp7 hK a ha i j hi hj)
      apply le_min hnonpos
      simp only [ordinaryWeight, if_pos hi, if_pos hj]
      have hI := min_le_right (0 : ℚ)
        ((2*(i.val : ℚ)+5*(removedIndicator N a.val : ℚ)-classDimension p m N h hp a-4)/2)
      have hJ := min_le_right (0 : ℚ)
        ((2*(j.val : ℚ)+5*(removedIndicator N a.val : ℚ)-classDimension p m N h hp a-4)/2)
      linarith
    · have hh := ordinary_high_row_entry_integral p m N h hp7 hp hNp hKp a ha j i (by omega)
      rw [mul_comm ((globalRow p m N h hp a j).map _) ((globalRow p m N h hp a i).map _)] at hh
      exact coeffLower_mono _ hh hnonpos
  · exact coeffLower_mono _
      (ordinary_high_row_entry_integral p m N h hp7 hp hNp hKp a ha i j (by omega)) hnonpos

#print axioms ordinary_entry_weighted_bound
end Zeta5OuterLow
