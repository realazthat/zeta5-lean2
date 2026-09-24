import OuterDeterminant

/-! Integrality at primes beyond the largest pole. -/
noncomputable section
open scoped BigOperators
open Polynomial Finset Matrix
namespace Zeta5OuterLargePrimes
open Zeta5Construction Zeta5OuterMoments Zeta5OuterBasis Zeta5OuterNear Zeta5OuterArithmetic
open Zeta5Outer Zeta5OuterEntries Zeta5NumeratorFunctional Zeta5FunctionalCancellation
open Zeta5OuterLow Zeta5OuterZero Zeta5BasisTransfer Zeta5OuterDeterminant

lemma ordinary_near_card_le_two (p m N h : ℕ) (hp : p = 2*m+1) (a : Fin (m+1)) :
    (nearMembers p m N h hp a).card ≤ 2 := by
  have hs : (nearMembers p m N h hp a).image (poleIndex N) ⊆ ({a.val,p-a.val} : Finset ℕ) := by
    intro j hj
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
    simpa only [mem_insert, mem_singleton] using (nearMembers_iff p m N h hp a k).mp hk |>.2
  have hh := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ (poleIndex_injective N h)] at hh
  exact hh.trans Finset.card_le_two

lemma ordinary_near_pole_lt (p m N h : ℕ) (hp : p = 2*m+1) (a : Fin (m+1))
    (ha : 0 < a.val) (k : Fin h) (hk : k ∈ nearMembers p m N h hp a) : poleIndex N k < p := by
  have hh := (nearMembers_iff p m N h hp a k).mp hk
  have ham := a.isLt
  omega

/-- Near-pole integrality holds for every surviving subset of a reflected pair,
including when p is greater than the largest source pole. -/
theorem ordinary_near_sum_integral_general (p m N h : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)
    (hp : p = 2*m+1) (a : Fin (m+1)) (ha : 0 < a.val) (P : ℤ[X]) :
    CoeffLower (rationalPadicValuation p)
      (∑ k ∈ nearMembers p m N h hp a,
        C ((P.map (Int.castRingHom ℚ)).eval (node N k) /
          (selectedTail N (nearMembers p m N h hp a)).derivative.eval (node N k)) *
            poleFunctional (poleIndex N k)) 0 := by
  have hd := ordinary_near_card_le_two p m N h hp a
  have ham := a.isLt
  rcases (show (nearMembers p m N h hp a).card = 0 ∨
      (nearMembers p m N h hp a).card = 1 ∨ (nearMembers p m N h hp a).card = 2 by omega) with hz | ho | ht
  · have hs := Finset.card_eq_zero.mp hz
    rw [hs, Finset.sum_empty]
    exact coeffLower_zero _ _
  · obtain ⟨k,hs⟩ := Finset.card_eq_one.mp ho
    have hk : k ∈ nearMembers p m N h hp a := by rw [hs]; simp
    have hkp := ordinary_near_pole_lt p m N h hp a ha k hk
    rw [hs]
    simp only [Finset.sum_singleton, selectedTail, Finset.prod_singleton,
      derivative_sub, derivative_X, derivative_C, sub_zero, eval_one, div_one, node]
    exact single_pole_integral p (poleIndex N k) (by omega) (poleIndex_pos N k) hkp P
  · obtain ⟨k,l,hkl,hs⟩ := Finset.card_eq_two.mp ht
    have hk : k ∈ nearMembers p m N h hp a := by rw [hs]; simp
    have hl : l ∈ nearMembers p m N h hp a := by rw [hs]; simp
    have hkval := (nearMembers_iff p m N h hp a k).mp hk |>.2
    have hlval := (nearMembers_iff p m N h hp a l).mp hl |>.2
    have hneq : poleIndex N k ≠ poleIndex N l := fun hh => hkl (poleIndex_injective N h hh)
    rw [hs, Finset.sum_pair hkl, selected_pair_derivative_left N k l hkl,
      selected_pair_derivative_right N k l hkl]
    rcases hkval with hk' | hk' <;> rcases hlval with hl' | hl'
    · exact False.elim (hneq (hk'.trans hl'.symm))
    · simp only [node, hk', hl']
      exact paired_poles_integral p a.val (by omega) ha (by omega) P
    · simp only [node, hk', hl']
      rw [add_comm]
      exact paired_poles_integral p a.val (by omega) ha (by omega) P
    · exact False.elim (hneq (hk'.trans hl'.symm))

lemma ordinary_near_functional_integral_general (p m N h : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)
    (hp : p = 2*m+1) (a : Fin (m+1)) (ha : 0 < a.val) (P : ℤ[X]) :
    CoeffLower (rationalPadicValuation p)
      (numeratorFunctional N h (correctedMomentLinearMap p)
        (omittedTail N (nearMembers p m N h hp a) * P.map (Int.castRingHom ℚ))) 0 := by
  rw [numeratorFunctional_cancel_subset]
  apply coeffLower_add_same
  · exact coeffLower_C _ _ 0 (corrected_selected_quotient_integral p N hp7 _ P)
  · exact ordinary_near_sum_integral_general p m N h hp7 hp a ha P

lemma ordinary_high_row_integral_general (p m N h : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)
    (hp : p = 2*m+1) (a : Fin (m+1)) (ha : 0 < a.val)
    (i j : Fin (classDimension p m N h hp a))
    (hi : (farFactor p m N h hp a).natDegree ≤ i.val) :
    CoeffLower (rationalPadicValuation p)
      (numeratorFunctional N h (correctedMomentLinearMap p)
        (denominator N ^ 5 *
          ((globalRow p m N h hp a i).map (Int.castRingHom ℚ) *
           (globalRow p m N h hp a j).map (Int.castRingHom ℚ)))) 0 := by
  obtain ⟨q, hq⟩ := farFactor_dvd_high_localRow p m N h hp a i (by omega) hi
  let P : ℤ[X] := integerDenominator N ^ 5 * q * globalRow p m N h hp a j
  have hf : integerDenominator N ^ 5 *
      (globalRow p m N h hp a i * globalRow p m N h hp a j) =
      ((∏ c ∈ univ.erase a, classFactor p m N h hp c) * farFactor p m N h hp a) * P := by
    dsimp [P]
    rw [globalRow, hq]
    ring
  have hf' := congrArg (Polynomial.map (Int.castRingHom ℚ)) hf
  simp only [Polynomial.map_mul, Polynomial.map_pow, map_integerDenominator] at hf'
  have hco := class_complement_far_map p m N h hp a
  simp only [Polynomial.map_mul] at hco
  rw [hco] at hf'
  rw [hf']
  exact ordinary_near_functional_integral_general p m N h hp7 hp a ha P

#print axioms ordinary_high_row_integral_general
lemma farFactor_eq_one_of_large (p m N h : ℕ) (hp : p = 2*m+1) (hK : N+h < p)
    (a : Fin (m+1)) : farFactor p m N h hp a = 1 := by
  have hs : (classMembers p m N h hp a).filter (fun k => p < poleIndex N k) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro k hk
    have hkp := (Finset.mem_filter.mp hk).2
    have hklt := k.isLt
    unfold poleIndex at hkp
    omega
  simp only [farFactor, hs, Finset.prod_empty]

lemma row_class_ne_zero_of_large (p m N h : ℕ) (hp : p = 2*m+1) (hK : N+h < p)
    (i : RowIndex p m N h hp) : i.1.val ≠ 0 := by
  intro ha
  have hd : 0 < classDimension p m N h hp i.1 := Nat.zero_lt_of_lt i.2.isLt
  obtain ⟨k,hk⟩ := Finset.card_pos.mp hd
  have hdiv := zero_class_dvd p m N h hp i.1 ha k hk
  apply Nat.not_dvd_of_pos_of_lt (poleIndex_pos N k) _ hdiv
  have hkl := k.isLt
  unfold poleIndex
  omega

lemma correctedClassMatrix_integral_of_large (p m N h : ℕ) [Fact p.Prime]
    (hp : p = 2*m+1) (hp7 : 7 ≤ p) (hK : N+h < p) (i j : RowIndex p m N h hp) :
    CoeffLower (rationalPadicValuation p) (correctedClassMatrix p m N h hp i j) 0 := by
  have hai := row_class_ne_zero_of_large p m N h hp hK i
  rcases i with ⟨a,i⟩
  rcases j with ⟨b,j⟩
  by_cases hab : a = b
  · subst b
    apply ordinary_high_row_integral_general p m N h hp7 hp a (Nat.pos_of_ne_zero hai) i j
    rw [farFactor_eq_one_of_large p m N h hp hK a, Polynomial.natDegree_one]
    omega
  · exact corrected_cross_class_entry_integral p m N h hp hp7 a b hab i j

/-- The entire source determinant is p-integral above its largest pole, once
its polynomial quotient degrees lie below the correction threshold. -/
theorem actual_large_prime_determinant_coeffLower (p m N h : ℕ) [Fact p.Prime]
    (hp : p = 2*m+1) (hp7 : 7 ≤ p) (hK : N+h < p)
    (hthreshold : (N+h)+4*N+2 ≤ 2*p) :
    CoeffLower (rationalPadicValuation p) (determinant N h) 0 := by
  have hpv : (-1 : WithTop ℚ) ≤ rationalPadicValuation p (p : ℚ)⁻¹ := by
    apply (rationalPadicValuation_lower_iff p _ (-1)).mpr
    right
    rw [padicValRat.inv, padicValRat.self (Fact.out : p.Prime).one_lt]
    norm_num
  have hB : ∀ i j : RowIndex p m N h hp,
      (-1 : WithTop ℚ) ≤ rationalPadicValuation p
        (((p : ℚ)⁻¹ • classCorrectionMatrix p m N h hp) i j) := by
    intro i j
    rw [Matrix.smul_apply, smul_eq_mul, AddValuation.map_mul]
    simpa only [add_zero] using add_le_add hpv (classCorrectionMatrix_integral p m N h hp hp7 i j)
  have hr : (((p : ℚ)⁻¹ • classCorrectionMatrix p m N h hp)).rank ≤ 0 := by
    have he : (p : ℚ)⁻¹ • classCorrectionMatrix p m N h hp =
        Matrix.diagonal (fun _ : RowIndex p m N h hp => (p : ℚ)⁻¹) * classCorrectionMatrix p m N h hp := by
      ext i j
      simp [Matrix.diagonal_mul]
    rw [he]
    have hh := (Matrix.rank_mul_le_right
      (Matrix.diagonal (fun _ : RowIndex p m N h hp => (p : ℚ)⁻¹)) _).trans
      (classCorrectionMatrix_rank p m N h hp hp7)
    simpa only [Nat.sub_eq_zero_of_le hthreshold] using hh
  have hd : CoeffLower (rationalPadicValuation p)
      (correctedClassMatrix p m N h hp + ((p : ℚ)⁻¹ • classCorrectionMatrix p m N h hp).map C).det 0 := by
    have hh := polynomial_det_coarse_rank_correction (rationalPadicValuation p)
      (correctedClassMatrix p m N h hp) ((p : ℚ)⁻¹ • classCorrectionMatrix p m N h hp)
      (fun _ => (0 : ℚ)) 0 (fun _ => le_rfl)
      (by simpa only [zero_add] using correctedClassMatrix_integral_of_large p m N h hp hp7 hK) hB hr
    simpa only [Finset.sum_const_zero, mul_zero, Nat.cast_zero, sub_zero] using hh
  rw [← actual_class_correction_decomposition] at hd
  have hu : rationalPadicValuation p (rationalBasis p m N h hp).det = 0 :=
    integer_det_valuation_zero p (basisMatrix p m N h hp) (basisMatrix_det_not_dvd p m N h hp)
  have hh := (congruence_preserves_coeffLower (rationalPadicValuation p)
    ((hankelMatrix N h).submatrix (rowEquiv p m N h hp) (rowEquiv p m N h hp))
    (rationalBasis p m N h hp) hu _).mp hd
  rw [Matrix.det_submatrix_equiv_self] at hh
  exact hh

/-- Guarded form for the normalizer's p>K branch. -/
theorem actual_large_prime_determinant_bound (p m N h : ℕ) [Fact p.Prime]
    (hp : p = 2*m+1) (hp7 : 7 ≤ p) (hK : N+h < p)
    (hthreshold : (N+h)+4*N+2 ≤ 2*p) (k : ℕ) (hk : (determinant N h).coeff k ≠ 0) :
    0 ≤ padicValRat p ((determinant N h).coeff k) := by
  have hh := ((rationalPadicValuation_lower_iff p _ 0).mp
    (actual_large_prime_determinant_coeffLower p m N h hp hp7 hK hthreshold k)).resolve_left hk
  exact_mod_cast hh

#print axioms actual_large_prime_determinant_bound
end Zeta5OuterLargePrimes
