import PresentationCertificates

noncomputable section
open Polynomial
namespace Zeta5Local

/-- A cleared simple-pole presentation has uniquely determined residues and polynomial part. -/
theorem canonical_presentation_unique {F ι : Type*} [Field F] [DecidableEq ι]
    (A P : F[X]) (s : Finset ι) (r c : ι → F) (E : ι → F[X])
    (hinj : Set.InjOn r s)
    (hfac : ∀ i ∈ s,  Lagrange.nodal s r=(X-C (r i))*E i)
    (hcert : A=Lagrange.nodal s r*P+∑ i ∈ s, C (c i)*E i) :
    P=A/Lagrange.nodal s r ∧
      ∀ i ∈ s, c i=A.eval (r i)/(∏ j ∈ s.erase i, (r i-r j)) := by
  have hE : ∀ i ∈ s, E i=Lagrange.nodal (s.erase i) r := by
    intro i hi
    apply mul_left_cancel₀ (monic_X_sub_C (r i)).ne_zero
    exact (hfac i hi).symm.trans (Lagrange.nodal_eq_mul_nodal_erase hi)
  have hc : ∀ i ∈ s, c i=A.eval (r i)/(∏ j ∈ s.erase i, (r i-r j)) := by
    intro i hi
    have he := congrArg (Polynomial.eval (r i)) hcert
    simp only [eval_add,eval_mul,eval_C,eval_finsetSum,Lagrange.eval_nodal_at_node hi,
      zero_mul,zero_add] at he
    have hs : (∑ j ∈ s, c j*(E j).eval (r i)) = c i*(E i).eval (r i) := by
      apply Finset.sum_eq_single i
      · intro j hj hji
        rw [hE j hj,Lagrange.eval_nodal_at_node (Finset.mem_erase.mpr ⟨hji.symm,hi⟩),mul_zero]
      · exact fun hn => False.elim (hn hi)
    rw [hs,hE i hi,Lagrange.eval_nodal] at he
    have hn : (∏ j ∈ s.erase i, (r i-r j))≠0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro j hj
      apply sub_ne_zero.mpr
      intro hij
      exact (Finset.mem_erase.mp hj).1 (hinj (Finset.mem_of_mem_erase hj) hi hij.symm)
    exact (eq_div_iff hn).mpr he.symm
  refine ⟨?_,hc⟩
  have hcan := partial_fraction_polynomial_identity A s r hinj
  have hs : (∑ i ∈ s, C (c i)*E i) =
      ∑ i ∈ s, C (A.eval (r i)/(∏ j ∈ s.erase i, (r i-r j)))*Lagrange.nodal (s.erase i) r := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hc i hi,hE i hi]
  rw [hs] at hcert
  exact mul_left_cancel₀ (Lagrange.nodal_monic (s:=s) (v:=r)).ne_zero
    (add_right_cancel (hcert.symm.trans hcan))

theorem presentations_unique {F ι : Type*} [Field F] [DecidableEq ι]
    (A P Q : F[X]) (s : Finset ι) (r c d : ι → F) (E H : ι → F[X])
    (hinj : Set.InjOn r s)
    (hE : ∀ i ∈ s, Lagrange.nodal s r=(X-C (r i))*E i)
    (hH : ∀ i ∈ s, Lagrange.nodal s r=(X-C (r i))*H i)
    (hc : A=Lagrange.nodal s r*P+∑ i ∈ s, C (c i)*E i)
    (hd : A=Lagrange.nodal s r*Q+∑ i ∈ s, C (d i)*H i) :
    P=Q ∧ ∀ i ∈ s, c i=d i := by
  have hp := canonical_presentation_unique A P s r c E hinj hE hc
  have hq := canonical_presentation_unique A Q s r d H hinj hH hd
  exact ⟨hp.1.trans hq.1.symm,fun i hi => (hp.2 i hi).trans (hq.2 i hi).symm⟩

#print axioms canonical_presentation_unique
#print axioms presentations_unique
end Zeta5Local
