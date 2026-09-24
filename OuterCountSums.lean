import OuterClassCounts

noncomputable section
open scoped BigOperators
namespace Zeta5OuterCountSums
open Finset Zeta5OuterBasis Zeta5OuterClassCounts

lemma sum_positive_below_eq {M : Type*} [AddCommMonoid M] (m N : ℕ) (hNm : N≤m)
    (f : ℕ → M) :
    (∑ a : Fin (m+1), if 0<a.val ∧ a.val≤N then f a.val else 0)=∑ a ∈ Icc 1 N, f a := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun a _ => a.val)
  · intro a ha
    have h := (mem_filter.1 ha).2
    exact mem_Icc.2 (by omega)
  · intro a ha b hb hab
    exact Fin.ext hab
  · intro a ha
    obtain ⟨ha1,haN⟩ := mem_Icc.1 ha
    refine ⟨⟨a,by omega⟩,?_,rfl⟩
    simp only [mem_filter,mem_univ,true_and,Fin.val_mk]
    exact ⟨by omega,haN⟩
  · intro a ha
    rfl

lemma removed_indicator_sum (N p r : ℕ) (hNp : N<p) (hrp : r<p) :
    (∑ a ∈ Icc 1 N, ((if a≤r then 1 else 0)+(if p-a≤r then 1 else 0))) =
      min N r+(N+r+1-p) := by
  rw [sum_add_distrib]
  have hlo : (∑ a ∈ Icc 1 N, if a≤r then 1 else 0)=min N r := by
    rw [← card_filter]
    have he : (Icc 1 N).filter (fun a => a≤r)=Icc 1 (min N r) := by
      ext a
      simp only [mem_filter,mem_Icc,le_min_iff]
      omega
    rw [he,Nat.card_Icc]
    omega
  have hhi : (∑ a ∈ Icc 1 N, if p-a≤r then 1 else 0)=N+r+1-p := by
    rw [← card_filter]
    have he : (Icc 1 N).filter (fun a => p-a≤r)=Icc (p-r) N := by
      ext a
      simp only [mem_filter,mem_Icc]
      omega
    rw [he,Nat.card_Icc]
    omega
  rw [hlo,hhi]

lemma removed_farDegree_sum (p m N h : ℕ) (hp : p=2*m+1)
    (hNp : 2*N<p) (hKp : p≤N+h) :
    (∑ a : Fin (m+1), if 0<a.val ∧ a.val≤N then (farFactor p m N h hp a).natDegree else 0) =
      2*((N+h)/p-1)*N+min N ((N+h)%p)+(N+(N+h)%p+1-p) := by
  have hpos : 0<p := by omega
  have hNm : N≤m := by omega
  have he (a : Fin (m+1)) :
      (if 0<a.val ∧ a.val≤N then (farFactor p m N h hp a).natDegree else 0) =
      if 0<a.val ∧ a.val≤N then
        2*((N+h)/p-1)+(if a.val≤(N+h)%p then 1 else 0)+(if p-a.val≤(N+h)%p then 1 else 0)
      else 0 := by
    by_cases ha : 0<a.val ∧ a.val≤N
    · rw [if_pos ha,if_pos ha]
      exact farDegree_eq_indicators p m N h hp hNp hKp a ha.1
    · rw [if_neg ha,if_neg ha]
  simp_rw [he]
  rw [sum_positive_below_eq m N hNm (fun a : ℕ =>
    2*((N+h)/p-1)+(if a≤(N+h)%p then 1 else 0)+(if p-a≤(N+h)%p then 1 else 0))]
  have hs := removed_indicator_sum N p ((N+h)%p) (by omega) (Nat.mod_lt _ hpos)
  simp only [sum_add_distrib,sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul]
  rw [sum_add_distrib] at hs
  nlinarith only [hs]

#print axioms removed_farDegree_sum
end Zeta5OuterCountSums
