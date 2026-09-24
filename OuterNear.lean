import OuterEntries
import FunctionalCancellation

/-! The surviving ordinary near poles and their integral contributions. -/
noncomputable section
open scoped BigOperators
open Polynomial Finset
namespace Zeta5OuterNear
open Zeta5Construction Zeta5OuterMoments Zeta5OuterBasis Zeta5NumeratorFunctional
open Zeta5FunctionalCancellation Zeta5OuterEntries Zeta5Outer

lemma poleClass_small_iff (p m j : ℕ) (hp : p = 2*m+1) (hj : j ≤ p)
    (a : Fin (m+1)) : poleClass p m j hp = a ↔ j = a.val ∨ j = p-a.val := by
  have ha := a.isLt
  have hp0 : 0 < p := by omega
  rw [Fin.ext_iff]
  change min (j%p) (p-j%p) = a.val ↔ _
  by_cases heq : j = p
  · subst j
    simp only [Nat.mod_self, Nat.sub_zero, min_eq_left (Nat.zero_le _)]
    omega
  · have hjp : j < p := by omega
    rw [Nat.mod_eq_of_lt hjp]
    by_cases hhalf : j ≤ p-j
    · rw [min_eq_left hhalf]
      omega
    · rw [min_eq_right (le_of_not_ge hhalf)]
      omega

def poleAt (N h j : ℕ) (hlo : N < j) (hhi : j ≤ N+h) : Fin h :=
  ⟨j-(N+1), by omega⟩

lemma poleIndex_poleAt (N h j : ℕ) (hlo : N < j) (hhi : j ≤ N+h) :
    poleIndex N (poleAt N h j hlo hhi) = j := by
  unfold poleAt poleIndex
  simp only
  omega

lemma poleIndex_injective (N h : ℕ) : Function.Injective (poleIndex N : Fin h → ℕ) := by
  intro i j hij
  apply Fin.ext
  unfold poleIndex at hij
  omega

def nearMembers (p m N h : ℕ) (hp : p = 2*m+1) (a : Fin (m+1)) : Finset (Fin h) :=
  (classMembers p m N h hp a).filter fun k => poleIndex N k ≤ p

lemma nearMembers_iff (p m N h : ℕ) (hp : p = 2*m+1) (a : Fin (m+1)) (k : Fin h) :
    k ∈ nearMembers p m N h hp a ↔
      poleIndex N k ≤ p ∧ (poleIndex N k = a.val ∨ poleIndex N k = p-a.val) := by
  simp only [nearMembers, classMembers, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨hclass, hkp⟩
    exact ⟨hkp, (poleClass_small_iff p m _ hp hkp a).mp hclass⟩
  · rintro ⟨hkp, hclass⟩
    exact ⟨(poleClass_small_iff p m _ hp hkp a).mpr hclass, hkp⟩

lemma reflectedPole_survives (p m N h : ℕ) (hp : p = 2*m+1) (hNp : 2*N < p)
    (hKp : p ≤ N+h) (a : Fin (m+1)) (ha : 0 < a.val) :
    N < p-a.val ∧ p-a.val ≤ N+h := by
  have ham := a.isLt
  omega

/-- An ordinary class retains exactly its two near poles if neither was removed. -/
theorem nearMembers_unremoved (p m N h : ℕ) (hp : p = 2*m+1)
    (hNp : 2*N < p) (hKp : p ≤ N+h) (a : Fin (m+1)) (ha : 0 < a.val) (hNa : N < a.val) :
    nearMembers p m N h hp a =
      {poleAt N h a.val hNa (by have := a.isLt; omega),
       poleAt N h (p-a.val) (reflectedPole_survives p m N h hp hNp hKp a ha).1
         (reflectedPole_survives p m N h hp hNp hKp a ha).2} := by
  ext k
  rw [nearMembers_iff]
  simp only [mem_insert, mem_singleton]
  constructor
  · rintro ⟨hk, hk' | hk'⟩
    · left
      apply poleIndex_injective N h
      rw [poleIndex_poleAt, hk']
    · right
      apply poleIndex_injective N h
      rw [poleIndex_poleAt, hk']
  · rintro (rfl | rfl) <;> rw [poleIndex_poleAt] <;>
      have := a.isLt <;> omega

/-- Removing the small representative leaves just the reflected near pole. -/
theorem nearMembers_removed (p m N h : ℕ) (hp : p = 2*m+1)
    (hNp : 2*N < p) (hKp : p ≤ N+h) (a : Fin (m+1)) (ha : 0 < a.val) (hNa : a.val ≤ N) :
    nearMembers p m N h hp a =
      {poleAt N h (p-a.val) (reflectedPole_survives p m N h hp hNp hKp a ha).1
         (reflectedPole_survives p m N h hp hNp hKp a ha).2} := by
  ext k
  rw [nearMembers_iff]
  simp only [mem_singleton]
  constructor
  · rintro ⟨hk, hk'⟩
    have hidx : N < poleIndex N k := by unfold poleIndex; omega
    apply poleIndex_injective N h
    rw [poleIndex_poleAt]
    omega
  · rintro rfl
    rw [poleIndex_poleAt]
    have := a.isLt
    omega

lemma coeffLower_add_same {F : Type*} [Field F] (v : AddValuation F (WithTop ℚ))
    {P Q : F[X]} {e : ℚ} (hP : CoeffLower v P e) (hQ : CoeffLower v Q e) :
    CoeffLower v (P+Q) e := by
  intro n
  rw [coeff_add]
  exact v.map_le_add (hP n) (hQ n)

lemma coeffLower_X_zero (p : ℕ) [Fact p.Prime] :
    CoeffLower (rationalPadicValuation p) (X : ℚ[X]) 0 := by
  intro n
  by_cases hn : n = 1
  · simp [coeff_X, hn]
  · simp [coeff_X, hn, Ne.symm hn]

lemma coeffLower_integer_map (p : ℕ) [Fact p.Prime] (P : ℤ[X]) :
    CoeffLower (rationalPadicValuation p) (P.map (Int.castRingHom ℚ)) 0 := by
  intro n
  rw [coeff_map]
  exact rationalPadicValuation_int_nonneg p (P.coeff n)

lemma coeffLower_affine (p : ℕ) [Fact p.Prime] (c d : ℚ)
    (hc : (0 : WithTop ℚ) ≤ rationalPadicValuation p c)
    (hd : (0 : WithTop ℚ) ≤ rationalPadicValuation p d) :
    CoeffLower (rationalPadicValuation p) (X*C c+C d) 0 := by
  apply coeffLower_add_same
  · simpa using coeffLower_mul (rationalPadicValuation p)
      (coeffLower_X_zero p) (coeffLower_C _ c 0 hc)
  · exact coeffLower_C _ d 0 hd

lemma pair_pole_affine (a b : ℕ) (A B : ℚ) :
    C (A / (-(a : ℚ)^2 - (-(b : ℚ)^2))) * poleFunctional a +
      C (B / (-(b : ℚ)^2 - (-(a : ℚ)^2))) * poleFunctional b =
      X*C ((A*(a : ℚ)^4-B*(b : ℚ)^4) / (-(a : ℚ)^2 - (-(b : ℚ)^2))) +
        C ((A*poleConstant a-B*poleConstant b) / (-(a : ℚ)^2 - (-(b : ℚ)^2))) := by
  have hd : (-(b : ℚ)^2 - (-(a : ℚ)^2))⁻¹ =
      -((-(a : ℚ)^2 - (-(b : ℚ)^2))⁻¹) := by
    rw [show -(b : ℚ)^2 - (-(a : ℚ)^2) = - (-(a : ℚ)^2 - (-(b : ℚ)^2)) by ring, inv_neg]
  simp only [poleFunctional_affine, div_eq_mul_inv, hd, map_neg, map_sub, map_mul]
  ring

/-- Complete affine integrality of the reflected pair, with any integer numerator. -/
theorem paired_poles_integral (p a : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ha : 0 < a) (hap : 2*a < p) (P : ℤ[X]) :
    CoeffLower (rationalPadicValuation p)
      (C ((P.map (Int.castRingHom ℚ)).eval (-(a : ℚ)^2) /
          (-(a : ℚ)^2 - (-((p-a : ℕ) : ℚ)^2))) * poleFunctional a +
        C ((P.map (Int.castRingHom ℚ)).eval (-((p-a : ℕ) : ℚ)^2) /
          (-((p-a : ℕ) : ℚ)^2 - (-(a : ℚ)^2))) * poleFunctional (p-a)) 0 := by
  rw [pair_pole_affine]
  apply coeffLower_affine
  · exact ordinary_pair_numerator_linear_integral p a _ (coeffLower_integer_map p P) ha hap
  · exact ordinary_pair_numerator_constant_integral p a _ (coeffLower_integer_map p P) hp ha hap

lemma single_pole_integral (p j : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (hj : 0 < j) (hjp : j < p) (P : ℤ[X]) :
    CoeffLower (rationalPadicValuation p)
      (C ((P.map (Int.castRingHom ℚ)).eval (-(j : ℚ)^2)) * poleFunctional j) 0 := by
  have hv : (0 : WithTop ℚ) ≤ rationalPadicValuation p (-(j : ℚ)^2) := by
    rw [AddValuation.map_neg, AddValuation.map_pow,
      rationalPadicValuation_unit_below p j hj hjp]
    simp
  have he := polynomial_eval_integral (rationalPadicValuation p) _ (coeffLower_integer_map p P) _ hv
  have hfun : CoeffLower (rationalPadicValuation p) (poleFunctional j) 0 := by
    rw [poleFunctional_affine]
    apply coeffLower_affine
    · rw [AddValuation.map_pow, rationalPadicValuation_unit_below p j hj hjp]
      simp
    · exact localPoleConstant_integral_below p j hp hj hjp
  simpa using coeffLower_mul (rationalPadicValuation p) (coeffLower_C _ _ 0 he) hfun

def integerSelectedTail (N : ℕ) {h : ℕ} (s : Finset (Fin h)) : ℤ[X] :=
  ∏ k ∈ s, (X+C ((poleIndex N k : ℤ)^2))

lemma integerSelectedTail_monic (N : ℕ) {h : ℕ} (s : Finset (Fin h)) :
    (integerSelectedTail N s).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_add_C _)

lemma integerSelectedTail_map (N : ℕ) {h : ℕ} (s : Finset (Fin h)) :
    (integerSelectedTail N s).map (Int.castRingHom ℚ) = selectedTail N s := by
  simp [integerSelectedTail, selectedTail, node, Polynomial.map_prod]

lemma corrected_selected_quotient_integral (p N : ℕ) {h : ℕ} [Fact p.Prime]
    (hp : 7 ≤ p) (s : Finset (Fin h)) (P : ℤ[X]) :
    (0 : WithTop ℚ) ≤ rationalPadicValuation p
      (correctedMomentLinearMap p ((P.map (Int.castRingHom ℚ)) / selectedTail N s)) := by
  have hm : (P /ₘ integerSelectedTail N s).map (Int.castRingHom ℚ) =
      (P.map (Int.castRingHom ℚ)) / selectedTail N s := by
    rw [Polynomial.map_divByMonic _ (integerSelectedTail_monic N s),
      integerSelectedTail_map, Polynomial.divByMonic_eq_div _ (selectedTail_monic N s)]
  rw [← hm]
  exact corrected_integer_moment_integral p hp _

lemma selected_pair_derivative_left (N : ℕ) {h : ℕ} (k l : Fin h) (hkl : k ≠ l) :
    (selectedTail N {k,l}).derivative.eval (node N k) = node N k-node N l := by
  simp [selectedTail, hkl, derivative_mul]

lemma selected_pair_derivative_right (N : ℕ) {h : ℕ} (k l : Fin h) (hkl : k ≠ l) :
    (selectedTail N {k,l}).derivative.eval (node N l) = node N l-node N k := by
  simp [selectedTail, hkl, derivative_mul]

/-- The near-pole remainder of every ordinary class is integral, regardless
of whether its small representative was removed by D_N. -/
theorem ordinary_near_sum_integral (p m N h : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)
    (hp : p = 2*m+1) (hNp : 2*N < p) (hKp : p ≤ N+h)
    (a : Fin (m+1)) (ha : 0 < a.val) (P : ℤ[X]) :
    CoeffLower (rationalPadicValuation p)
      (∑ k ∈ nearMembers p m N h hp a,
        C ((P.map (Int.castRingHom ℚ)).eval (node N k) /
          (selectedTail N (nearMembers p m N h hp a)).derivative.eval (node N k)) *
            poleFunctional (poleIndex N k)) 0 := by
  have ham := a.isLt
  by_cases hNa : N < a.val
  · let k := poleAt N h a.val hNa (by omega)
    let l := poleAt N h (p-a.val)
      (reflectedPole_survives p m N h hp hNp hKp a ha).1
      (reflectedPole_survives p m N h hp hNp hKp a ha).2
    have hk : poleIndex N k = a.val := poleIndex_poleAt _ _ _ _ _
    have hl : poleIndex N l = p-a.val := poleIndex_poleAt _ _ _ _ _
    have hkl : k ≠ l := by
      intro hkl
      have := congrArg (poleIndex N) hkl
      rw [hk, hl] at this
      omega
    have hs : nearMembers p m N h hp a = {k,l} :=
      nearMembers_unremoved p m N h hp hNp hKp a ha hNa
    rw [hs, Finset.sum_pair hkl]
    rw [selected_pair_derivative_left N k l hkl, selected_pair_derivative_right N k l hkl]
    simp only [node, hk, hl]
    exact paired_poles_integral p a.val (by omega) ha (by omega) P
  · let l := poleAt N h (p-a.val)
      (reflectedPole_survives p m N h hp hNp hKp a ha).1
      (reflectedPole_survives p m N h hp hNp hKp a ha).2
    have hl : poleIndex N l = p-a.val := poleIndex_poleAt _ _ _ _ _
    have hs : nearMembers p m N h hp a = {l} :=
      nearMembers_removed p m N h hp hNp hKp a ha (by omega)
    rw [hs]
    simp only [Finset.sum_singleton, selectedTail, Finset.prod_singleton,
      derivative_sub, derivative_X, derivative_C, sub_zero, eval_one, div_one]
    simp only [node, hl]
    exact single_pole_integral p (p-a.val) (by omega) (by omega) (by omega) P

/-- The complete functional after all ordinary far poles cancel is integral. -/
theorem ordinary_near_functional_integral (p m N h : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)
    (hp : p = 2*m+1) (hNp : 2*N < p) (hKp : p ≤ N+h)
    (a : Fin (m+1)) (ha : 0 < a.val) (P : ℤ[X]) :
    CoeffLower (rationalPadicValuation p)
      (numeratorFunctional N h (correctedMomentLinearMap p)
        (omittedTail N (nearMembers p m N h hp a) * P.map (Int.castRingHom ℚ))) 0 := by
  rw [numeratorFunctional_cancel_subset]
  apply coeffLower_add_same
  · exact coeffLower_C _ _ 0 (corrected_selected_quotient_integral p N hp7 _ P)
  · exact ordinary_near_sum_integral p m N h hp7 hp hNp hKp a ha P

#print axioms ordinary_near_functional_integral
lemma classFactor_split_near (p m N h : ℕ) (hp : p = 2*m+1) (a : Fin (m+1)) :
    classFactor p m N h hp a =
      farFactor p m N h hp a * integerSelectedTail N (nearMembers p m N h hp a) := by
  unfold classFactor farFactor integerSelectedTail nearMembers
  simpa only [not_lt] using (Finset.prod_filter_mul_prod_filter_not
    (classMembers p m N h hp a) (fun k => p < poleIndex N k)
    (fun k => (X+C ((poleIndex N k : ℤ)^2) : ℤ[X]))).symm

lemma class_complement_far_map (p m N h : ℕ) (hp : p = 2*m+1) (a : Fin (m+1)) :
    (((∏ c ∈ univ.erase a, classFactor p m N h hp c) * farFactor p m N h hp a).map
      (Int.castRingHom ℚ)) = omittedTail N (nearMembers p m N h hp a) := by
  apply mul_right_cancel₀ (selectedTail_monic N (nearMembers p m N h hp a)).ne_zero
  rw [← tail_split_selected]
  have hh : ((∏ c ∈ univ.erase a, classFactor p m N h hp c) * farFactor p m N h hp a) *
      integerSelectedTail N (nearMembers p m N h hp a) = integerTailDenominator N h := by
    have ht := Finset.mul_prod_erase univ (classFactor p m N h hp) (mem_univ a)
    rw [classFactors_product, classFactor_split_near] at ht
    calc
      _ = (farFactor p m N h hp a * integerSelectedTail N (nearMembers p m N h hp a)) *
        ∏ c ∈ univ.erase a, classFactor p m N h hp c := by ring
      _ = _ := ht
  have hh' := congrArg (Polynomial.map (Int.castRingHom ℚ)) hh
  simpa only [Polynomial.map_mul, integerSelectedTail_map, map_integerTailDenominator] using hh'

/-- All ordinary same-class entries with a high row are integral. This proves
the cancellation branch of the actual row-weight estimate (4.12). -/
theorem ordinary_high_row_entry_integral (p m N h : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)
    (hp : p = 2*m+1) (hNp : 2*N < p) (hKp : p ≤ N+h)
    (a : Fin (m+1)) (ha : 0 < a.val)
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
  exact ordinary_near_functional_integral p m N h hp7 hp hNp hKp a ha P

#print axioms ordinary_high_row_entry_integral
end Zeta5OuterNear
