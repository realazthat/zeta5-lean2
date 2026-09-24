import OuterClassCounts
import OuterLow

noncomputable section
open scoped BigOperators
namespace Zeta5OuterWeightSums
open Finset Zeta5OuterBasis Zeta5OuterLow Zeta5OuterClassCounts

def localWeightSum (d f δ : ℕ) : ℚ :=
  2*∑ i : Fin d, if i.val<f then min 0 ((2*(i.val : ℚ)+5*δ-d-4)/2) else 0

lemma localWeightSum_unremoved (f : ℕ) (hf : f≤4) :
    localWeightSum (f+2) f 0 = -7*(f : ℚ) := by
  interval_cases f <;> norm_num [localWeightSum,Fin.sum_univ_succ]

lemma localWeightSum_removed_low (f : ℕ) (hf : f≤2) :
    localWeightSum (f+1) f 1 = -(f : ℚ) := by
  interval_cases f <;> norm_num [localWeightSum,Fin.sum_univ_succ]

lemma localWeightSum_removed_high (f : ℕ) (hf : 2≤f) (hf4 : f≤4) :
    localWeightSum (f+1) f 1 = 2-2*(f : ℚ) := by
  interval_cases f <;> norm_num [localWeightSum,Fin.sum_univ_succ]

lemma quotient_eq_one (p K : ℕ) (hp : 0<p) (hKp : p≤K) (hK2 : K<2*p) : K/p=1 := by
  apply Nat.div_eq_of_lt_le
  · omega
  · omega

lemma quotient_eq_two (p K : ℕ) (hp : 0<p) (hK2 : 2*p≤K) (hK3 : K<3*p) : K/p=2 := by
  apply Nat.div_eq_of_lt_le
  · omega
  · omega

lemma ordinaryWeight_sum (p m N h : ℕ) (hp : p=2*m+1)
    (hNp : 2*N<p) (hKp : p≤N+h) (hK3 : N+h<3*p)
    (a : Fin (m+1)) (ha : 0<a.val) :
    2*(∑ i, ordinaryWeight p m N h hp a i) =
      if a.val≤N then
        if N+h<2*p then -((farFactor p m N h hp a).natDegree : ℚ)
        else 2-2*((farFactor p m N h hp a).natDegree : ℚ)
      else -7*((farFactor p m N h hp a).natDegree : ℚ) := by
  have hpos : 0<p := by omega
  have hdim := classDimension_eq_far_add p m N h hp hNp hKp a ha
  have hfar := farDegree_eq_indicators p m N h hp hNp hKp a ha
  have hbounds : (farFactor p m N h hp a).natDegree≤4 := by
    by_cases hK2 : N+h<2*p
    · rw [quotient_eq_one p (N+h) hpos hKp hK2] at hfar
      split_ifs at hfar <;> omega
    · rw [quotient_eq_two p (N+h) hpos (by omega) hK3] at hfar
      split_ifs at hfar <;> omega
  change localWeightSum (classDimension p m N h hp a)
    (farFactor p m N h hp a).natDegree (removedIndicator N a.val) = _
  by_cases haN : a.val≤N
  · simp only [removedIndicator,if_pos haN] at hdim ⊢
    have hdim' : classDimension p m N h hp a = (farFactor p m N h hp a).natDegree+1 := by omega
    rw [hdim']
    by_cases hK2 : N+h<2*p
    · rw [if_pos hK2]
      apply localWeightSum_removed_low
      rw [quotient_eq_one p (N+h) hpos hKp hK2] at hfar
      split_ifs at hfar <;> omega
    · rw [if_neg hK2]
      apply localWeightSum_removed_high _ _ hbounds
      rw [quotient_eq_two p (N+h) hpos (by omega) hK3] at hfar
      split_ifs at hfar <;> omega
  · rw [if_neg haN,removedIndicator,if_neg haN]
    rw [if_neg haN,Nat.sub_zero] at hdim
    rw [hdim]
    exact localWeightSum_unremoved _ hbounds

end Zeta5OuterWeightSums
