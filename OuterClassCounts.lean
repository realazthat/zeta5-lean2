import OuterZero
import OuterBasis
import InnerAsymptotics

noncomputable section
open scoped BigOperators
namespace Zeta5OuterClassCounts
open Finset Zeta5OuterBasis Zeta5Construction

lemma poleClass_eq_iff (p m j : ℕ) (hp : p=2*m+1) (a : Fin (m+1)) :
    poleClass p m j hp = a ↔ j%p=a.val ∨ j%p=p-a.val := by
  have hj : j%p < p := Nat.mod_lt _ (by omega)
  have ha := a.isLt
  rw [Fin.ext_iff]
  change min (j%p) (p-j%p)=a.val ↔ _
  by_cases hc : j%p ≤ p-j%p
  · rw [min_eq_left hc]
    omega
  · rw [min_eq_right (by omega)]
    omega

lemma poleClass_zero_iff (p m j : ℕ) (hp : p=2*m+1) :
    (poleClass p m j hp).val=0 ↔ j%p=0 := by
  have hj : j%p < p := Nat.mod_lt _ (by omega)
  change min (j%p) (p-j%p)=0 ↔ _
  omega

lemma poleIndex_filter_card (N h : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ((univ : Finset (Fin h)).filter fun i => P (poleIndex N i)).card =
      ((Ioc N (N+h)).filter P).card := by
  apply card_bij (fun i _ => poleIndex N i)
  · intro i hi
    have hp := (mem_filter.1 hi).2
    simp only [mem_filter,mem_Ioc]
    exact ⟨⟨by unfold poleIndex; omega,by unfold poleIndex; have := i.isLt; omega⟩,hp⟩
  · intro i hi j hj he
    apply Fin.ext
    unfold poleIndex at he
    omega
  · intro j hj
    obtain ⟨hjI,hjP⟩ := mem_filter.1 hj
    obtain ⟨hjN,hjK⟩ := mem_Ioc.1 hjI
    let i : Fin h := ⟨j-(N+1),by omega⟩
    have hi : poleIndex N i=j := by dsimp [poleIndex,i]; omega
    exact ⟨i,by simpa only [mem_filter,mem_univ,hi,true_and] using hjP,hi⟩

lemma interval_count_split (N h : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ((Icc 1 (N+h)).filter P).card =
      ((Icc 1 N).filter P).card+((Ioc N (N+h)).filter P).card := by
  have he : (Icc 1 (N+h)).filter P =
      ((Icc 1 N).filter P) ∪ ((Ioc N (N+h)).filter P) := by
    ext j
    by_cases hj : P j <;> simp [mem_filter,mem_union,mem_Icc,mem_Ioc,hj] <;> omega
  rw [he,card_union_of_disjoint]
  apply disjoint_left.2
  intro j hj1 hj2
  have h1 := (mem_filter.1 hj1).1
  have h2 := (mem_filter.1 hj2).1
  simp only [mem_Icc,mem_Ioc] at h1 h2
  omega

lemma classDimension_add_removed (p m N h : ℕ) (hp : p=2*m+1)
    (a : Fin (m+1)) (ha : 0<a.val) :
    classDimension p m N h hp a + Zeta5Parameters.poleCount N p a.val =
      Zeta5Parameters.poleCount (N+h) p a.val := by
  have hap : a.val<p := by have := a.isLt; omega
  have hpa : p-a.val<p := by omega
  have he : classDimension p m N h hp a =
      ((Ioc N (N+h)).filter fun j => j%p=a.val ∨ j%p=p-a.val).card := by
    unfold classDimension classMembers
    simp_rw [poleClass_eq_iff]
    exact poleIndex_filter_card N h (fun j => j%p=a.val ∨ j%p=p-a.val)
  rw [he]
  unfold Zeta5Parameters.poleCount
  simp only [Nat.mod_eq_of_lt hap,Nat.mod_eq_of_lt hpa]
  rw [interval_count_split N h]
  omega

lemma poleCount_eq_quotient_indicators (A p a : ℕ) (hp : 0<p)
    (ha : 0<a) (hhalf : 2*a<p) :
    Zeta5Parameters.poleCount A p a = 2*(A/p)+
      (if a≤A%p then 1 else 0)+(if p-a≤A%p then 1 else 0) := by
  have hf := Zeta5InnerAsymptotics.poleCount_eq_floor A p a hp ha hhalf
  have hd := Nat.mod_add_div A p
  have hr := Nat.mod_lt A hp
  generalize hqdef : A/p=q at *
  generalize hrdef : A%p=r at *
  have hpa : a<p := by omega
  have hq : (0 : ℚ)<p := by exact_mod_cast hp
  have hA : (A : ℚ) = (q : ℚ)*p+r := by
    have hn : A=q*p+r := by simpa only [Nat.mul_comm,Nat.add_comm] using hd.symm
    exact_mod_cast hn
  have hrq : (r : ℚ)<p := by exact_mod_cast hr
  have hapq : (a : ℚ)<p := by exact_mod_cast hpa
  have haq : (0 : ℚ)<a := by exact_mod_cast ha
  have hr0 : (0 : ℚ)≤r := Nat.cast_nonneg r
  have hl : ⌊((A : ℚ)-a)/p⌋ = (q : ℤ)+(if a≤r then 0 else -1 : ℤ) := by
    apply Int.floor_eq_iff.mpr
    rw [hA]
    split_ifs with haR
    · have har : (a : ℚ)≤r := by exact_mod_cast haR
      constructor <;> push_cast <;> first | rw [le_div_iff₀ hq] | rw [div_lt_iff₀ hq]
      all_goals nlinarith
    · have hra : (r : ℚ)<a := by exact_mod_cast (show r<a by omega)
      constructor <;> push_cast <;> first | rw [le_div_iff₀ hq] | rw [div_lt_iff₀ hq]
      all_goals nlinarith
  have hu : ⌊((A : ℚ)+a)/p⌋ = (q : ℤ)+(if p-a≤r then 1 else 0 : ℤ) := by
    apply Int.floor_eq_iff.mpr
    rw [hA]
    split_ifs with hbR
    · have hsum : (p : ℚ)≤r+a := by exact_mod_cast (show p≤r+a by omega)
      constructor <;> push_cast <;> first | rw [le_div_iff₀ hq] | rw [div_lt_iff₀ hq]
      all_goals nlinarith
    · have hsum : (r : ℚ)+a<p := by exact_mod_cast (show r+a<p by omega)
      constructor <;> push_cast <;> first | rw [le_div_iff₀ hq] | rw [div_lt_iff₀ hq]
      all_goals nlinarith
  rw [hl,hu] at hf
  split_ifs at * <;> omega

lemma poleCount_removed (N p a : ℕ) (hNp : 2*N<p) (ha : 0<a) (hhalf : 2*a<p) :
    Zeta5Parameters.poleCount N p a = if a≤N then 1 else 0 := by
  have hp : 0<p := by omega
  have hN : N<p := by omega
  rw [poleCount_eq_quotient_indicators N p a hp ha hhalf,
    Nat.div_eq_of_lt hN,Nat.mod_eq_of_lt hN]
  have hpa : ¬p-a≤N := by omega
  simp [hpa]

lemma farFactor_natDegree_card (p m N h : ℕ) (hp : p=2*m+1) (a : Fin (m+1)) :
    (farFactor p m N h hp a).natDegree =
      ((classMembers p m N h hp a).filter fun i => p<poleIndex N i).card := by
  unfold farFactor
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_add_C _)]
  simp only [Polynomial.natDegree_X_add_C,Finset.sum_const,nsmul_eq_mul,mul_one]
  norm_cast

lemma farDegree_add_two (p m N h : ℕ) (hp : p=2*m+1)
    (hNp : 2*N<p) (hKp : p≤N+h) (a : Fin (m+1)) (ha : 0<a.val) :
    (farFactor p m N h hp a).natDegree+2=Zeta5Parameters.poleCount (N+h) p a.val := by
  have hpos : 0<p := by omega
  have hhalf : 2*a.val<p := by have := a.isLt; omega
  have hap : a.val<p := by omega
  have hpa : p-a.val<p := by omega
  let P : ℕ → Prop := fun j => j%p=a.val ∨ j%p=p-a.val
  have he : (farFactor p m N h hp a).natDegree = ((Ioc p (N+h)).filter P).card := by
    rw [farFactor_natDegree_card]
    unfold classMembers
    rw [filter_filter]
    simp_rw [poleClass_eq_iff]
    rw [poleIndex_filter_card N h (fun j => (j%p=a.val ∨ j%p=p-a.val) ∧ p<j)]
    congr 1
    ext j
    simp only [mem_filter,mem_Ioc,P]
    have hN : N<p := by omega
    omega
  have hc := interval_count_split p (N+h-p) P
  have heK : p+(N+h-p)=N+h := by omega
  rw [heK] at hc
  have hpoles0 : Zeta5Parameters.poleCount p p a.val=2 := by
    rw [poleCount_eq_quotient_indicators p p a.val hpos ha hhalf]
    simp [Nat.div_self hpos,show ¬a.val≤0 by omega,show ¬p-a.val≤0 by omega]
  have hpoles : ((Icc 1 p).filter P).card=2 := by
    simpa only [Zeta5Parameters.poleCount,Nat.mod_eq_of_lt hap,Nat.mod_eq_of_lt hpa,P] using hpoles0
  rw [hpoles,← he] at hc
  unfold Zeta5Parameters.poleCount
  simp only [Nat.mod_eq_of_lt hap,Nat.mod_eq_of_lt hpa]
  simpa only [P,Nat.add_comm] using hc.symm

lemma classDimension_eq_far_add (p m N h : ℕ) (hp : p=2*m+1)
    (hNp : 2*N<p) (hKp : p≤N+h) (a : Fin (m+1)) (ha : 0<a.val) :
    classDimension p m N h hp a = (farFactor p m N h hp a).natDegree+2-
      (if a.val≤N then 1 else 0) := by
  have hhalf : 2*a.val<p := by have := a.isLt; omega
  have hc := classDimension_add_removed p m N h hp a ha
  rw [poleCount_removed N p a.val hNp ha hhalf] at hc
  have hf := farDegree_add_two p m N h hp hNp hKp a ha
  omega

lemma farDegree_eq_indicators (p m N h : ℕ) (hp : p=2*m+1)
    (hNp : 2*N<p) (hKp : p≤N+h) (a : Fin (m+1)) (ha : 0<a.val) :
    (farFactor p m N h hp a).natDegree = 2*((N+h)/p-1)+
      (if a.val≤(N+h)%p then 1 else 0)+(if p-a.val≤(N+h)%p then 1 else 0) := by
  have hpos : 0<p := by omega
  have hhalf : 2*a.val<p := by have := a.isLt; omega
  have hf := farDegree_add_two p m N h hp hNp hKp a ha
  rw [poleCount_eq_quotient_indicators (N+h) p a.val hpos ha hhalf] at hf
  have hq : 0<(N+h)/p := Nat.div_pos hKp hpos
  omega

lemma zero_interval_count (A p : ℕ) :
    ((Icc 1 A).filter fun j => j%p=0).card=A/p := by
  have he : Icc 1 A=Ioc 0 A := by ext j; simp only [mem_Icc,mem_Ioc]; omega
  rw [he]
  simp only [← Nat.dvd_iff_mod_eq_zero]
  exact Nat.Ioc_filter_dvd_card_eq_div A p

lemma zero_classDimension (p m N h : ℕ) (hp : p=2*m+1) (hNp : N<p)
    (a : Fin (m+1)) (ha : a.val=0) : classDimension p m N h hp a=(N+h)/p := by
  have he (j : ℕ) : poleClass p m j hp=a ↔ j%p=0 := by
    rw [Fin.ext_iff,ha,poleClass_zero_iff]
  have hdim : classDimension p m N h hp a =
      ((Ioc N (N+h)).filter fun j => j%p=0).card := by
    unfold classDimension classMembers
    simp_rw [he]
    exact poleIndex_filter_card N h (fun j => j%p=0)
  have hs := interval_count_split N h (fun j => j%p=0)
  rw [zero_interval_count,zero_interval_count,Nat.div_eq_of_lt hNp,zero_add,← hdim] at hs
  exact hs.symm

lemma zero_farDegree (p m N h : ℕ) (hp : p=2*m+1) (hNp : N<p)
    (hKp : p≤N+h) (a : Fin (m+1)) (ha : a.val=0) :
    (farFactor p m N h hp a).natDegree+1=(N+h)/p := by
  have he (j : ℕ) : poleClass p m j hp=a ↔ j%p=0 := by
    rw [Fin.ext_iff,ha,poleClass_zero_iff]
  have hfar : (farFactor p m N h hp a).natDegree =
      ((Ioc p (N+h)).filter fun j => j%p=0).card := by
    rw [farFactor_natDegree_card]
    unfold classMembers
    rw [filter_filter]
    simp_rw [he]
    rw [poleIndex_filter_card N h (fun j => j%p=0 ∧ p<j)]
    congr 1
    ext j
    simp only [mem_filter,mem_Ioc]
    omega
  have hs := interval_count_split p (N+h-p) (fun j => j%p=0)
  have hK : p+(N+h-p)=N+h := by omega
  rw [hK,zero_interval_count,zero_interval_count,Nat.div_self (by omega : 0<p),← hfar] at hs
  omega

lemma farDegree_sum (p m N h : ℕ) (hp : p=2*m+1) (hNp : N<p) (hKp : p≤N+h) :
    (∑ a : Fin (m+1), (farFactor p m N h hp a).natDegree)=N+h-p := by
  let S : Finset (Fin h) := univ.filter (fun i => p<poleIndex N i)
  have hf := Finset.card_eq_sum_card_fiberwise
    (s := S) (t := (univ : Finset (Fin (m+1))))
    (f := fun i => poleClass p m (poleIndex N i) hp) (by simp)
  have he (a : Fin (m+1)) : (S.filter fun i => poleClass p m (poleIndex N i) hp=a).card =
      (farFactor p m N h hp a).natDegree := by
    rw [farFactor_natDegree_card]
    unfold S classMembers
    congr 1
    ext i
    simp only [mem_filter,mem_univ,true_and]
    tauto
  simp_rw [he] at hf
  rw [← hf]
  unfold S
  rw [poleIndex_filter_card N h (fun j => p<j)]
  have heI : (Ioc N (N+h)).filter (fun j => p<j)=Ioc p (N+h) := by
    ext j
    simp only [mem_filter,mem_Ioc]
    omega
  rw [heI,Nat.card_Ioc]

#print axioms zero_classDimension
#print axioms zero_farDegree
#print axioms farDegree_sum
#print axioms classDimension_add_removed
#print axioms poleCount_eq_quotient_indicators
#print axioms farDegree_add_two
#print axioms farDegree_eq_indicators
end Zeta5OuterClassCounts
