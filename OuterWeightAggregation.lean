import OuterLargePrimes
import OuterWeightSums
import OuterCountSums

/-! Exact finite aggregation of the actual outer row weights. -/
noncomputable section
open scoped BigOperators
open Polynomial Finset Matrix
namespace Zeta5OuterWeightAggregation
open Zeta5Construction Zeta5OuterMoments Zeta5OuterBasis Zeta5OuterNear Zeta5OuterArithmetic
open Zeta5Outer Zeta5OuterEntries Zeta5NumeratorFunctional Zeta5FunctionalCancellation
open Zeta5OuterLow Zeta5OuterZero Zeta5BasisTransfer Zeta5OuterDeterminant
open Zeta5OuterClassCounts Zeta5OuterWeightSums Zeta5OuterCountSums

lemma zeroWeight_sum (p m N h : ℕ) (hp : p=2*m+1) (hNp : 2*N<p)
    (hKp : p≤N+h) (hK3 : N+h<3*p) (a : Fin (m+1)) (ha : a.val=0) :
    2*(∑ i, zeroWeight p m N h hp a i) = if N+h<2*p then (-1 : ℚ) else -4 := by
  have hd := zero_classDimension p m N h hp (by omega) a ha
  change 2*(∑ i : Fin (classDimension p m N h hp a),
    if classDimension p m N h hp a = 1 then (-1/2 : ℚ) else 2*(i.val : ℚ)-2) = _
  rw [hd]
  by_cases hK2 : N+h<2*p
  · rw [if_pos hK2, quotient_eq_one p (N+h) (by omega) hKp hK2]
    norm_num [Fin.sum_univ_succ]
  · rw [if_neg hK2, quotient_eq_two p (N+h) (by omega) (by omega) hK3]
    norm_num [Fin.sum_univ_succ]

lemma removed_class_count (p m N : ℕ) (hp : p=2*m+1) (hNp : 2*N<p) :
    (∑ a : Fin (m+1), if 0<a.val ∧ a.val≤N then (1 : ℚ) else 0) = N := by
  rw [sum_positive_below_eq m N (by omega) (fun _ => (1 : ℚ))]
  simp

lemma zero_indicator_sum (m : ℕ) (f : Fin (m+1) → ℚ) :
    (∑ a : Fin (m+1), if a.val=0 then f a else 0) = f 0 := by
  have he (a : Fin (m+1)) : a.val=0 ↔ a=0 := by
    constructor
    · intro h
      apply Fin.ext
      simpa using h
    · rintro rfl
      rfl
  simp_rw [he]
  simp

/-- Twice the exact sum of all source row weights, before the rank loss. -/
theorem rowWeight_sum (p m N h : ℕ) (hp : p=2*m+1) (hNp : 2*N<p)
    (hKp : p≤N+h) (hK3 : N+h<3*p) :
    2*(∑ i : RowIndex p m N h hp, rowWeight p m N h hp i) =
      if N+h<2*p then
        -7*((N+h : ℕ) : ℚ)+7*p+6*((min N ((N+h)%p)+(N+(N+h)%p+1-p) : ℕ) : ℚ)-1
      else
        -7*((N+h : ℕ) : ℚ)+7*p+3+12*N+5*((min N ((N+h)%p)+(N+(N+h)%p+1-p) : ℕ) : ℚ) := by
  let F : Fin (m+1) → ℕ := fun a => (farFactor p m N h hp a).natDegree
  let R : Fin (m+1) → Prop := fun a => 0<a.val ∧ a.val≤N
  letI : DecidablePred R := fun a => inferInstance
  have hf : (∑ a : Fin (m+1), (F a : ℚ)) = ((N+h : ℕ) : ℚ)-p := by
    have hh : (∑ a : Fin (m+1), (F a : ℚ)) = ((N+h-p : ℕ) : ℚ) := by
      exact_mod_cast farDegree_sum p m N h hp (by omega) hKp
    rw [Nat.cast_sub hKp] at hh
    exact hh
  have hr := removed_farDegree_sum p m N h hp hNp hKp
  have hz := zero_farDegree p m N h hp (by omega) hKp (0 : Fin (m+1)) rfl
  have hcount : (∑ a : Fin (m+1), if R a then (1 : ℚ) else 0) = N :=
    removed_class_count p m N hp hNp
  rw [Fintype.sum_sigma, Finset.mul_sum]
  by_cases hK2 : N+h<2*p
  · rw [if_pos hK2]
    rw [quotient_eq_one p (N+h) (by omega) hKp hK2] at hr hz
    have hz0 : F 0=0 := by dsimp [F]; omega
    have hrq : (∑ a : Fin (m+1), if R a then (F a : ℚ) else 0) =
        ((min N ((N+h)%p)+(N+(N+h)%p+1-p) : ℕ) : ℚ) := by
      norm_num only [Nat.sub_self, mul_zero, zero_mul, zero_add] at hr
      exact_mod_cast hr
    have he (a : Fin (m+1)) :
        2*(∑ i : Fin (classDimension p m N h hp a), rowWeight p m N h hp ⟨a,i⟩) =
          -7*(F a : ℚ)+6*(if R a then (F a : ℚ) else 0)+
            (if a.val=0 then -1+7*(F a : ℚ) else 0) := by
      by_cases ha : a.val=0
      · simp only [rowWeight, if_pos ha]
        rw [zeroWeight_sum p m N h hp hNp hKp hK3 a ha, if_pos hK2]
        simp only [R, ha, lt_self_iff_false, false_and, if_false, if_true]
        ring
      · simp only [rowWeight, if_neg ha]
        rw [ordinaryWeight_sum p m N h hp hNp hKp hK3 a (by omega)]
        simp only [if_pos hK2, if_neg ha, R]
        by_cases haN : a.val≤N <;> simp [haN, show 0<a.val by omega, F] <;> ring
    simp_rw [he]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hf, hrq, zero_indicator_sum, hz0]
    norm_num
    ring
  · rw [if_neg hK2]
    rw [quotient_eq_two p (N+h) (by omega) (by omega) hK3] at hr hz
    have hz1 : F 0=1 := by dsimp [F]; omega
    have hrq : (∑ a : Fin (m+1), if R a then (F a : ℚ) else 0) =
        2*N+((min N ((N+h)%p)+(N+(N+h)%p+1-p) : ℕ) : ℚ) := by
      norm_num only [Nat.add_one_sub_one, mul_one] at hr
      exact_mod_cast (by simpa only [Nat.add_assoc] using hr)
    have he (a : Fin (m+1)) :
        2*(∑ i : Fin (classDimension p m N h hp a), rowWeight p m N h hp ⟨a,i⟩) =
          -7*(F a : ℚ)+5*(if R a then (F a : ℚ) else 0)+
            2*(if R a then (1 : ℚ) else 0)+(if a.val=0 then -4+7*(F a : ℚ) else 0) := by
      by_cases ha : a.val=0
      · simp only [rowWeight, if_pos ha]
        rw [zeroWeight_sum p m N h hp hNp hKp hK3 a ha, if_neg hK2]
        simp only [R, ha, lt_self_iff_false, false_and, if_false, if_true]
        ring
      · simp only [rowWeight, if_neg ha]
        rw [ordinaryWeight_sum p m N h hp hNp hKp hK3 a (by omega)]
        simp only [if_neg hK2, if_neg ha, R]
        by_cases haN : a.val≤N <;> simp [haN, show 0<a.val by omega, F] <;> ring
    simp_rw [he]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      hf, hrq, hcount, zero_indicator_sum, hz1]
    norm_num
    ring

#print axioms rowWeight_sum
end Zeta5OuterWeightAggregation
