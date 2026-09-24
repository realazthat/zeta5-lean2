import CanonicalSplitBound
import PresentationCertificates

namespace Zeta5Local
open Polynomial
variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]

lemma presentation_near_cofactor (E D T Ti Ei : F[X]) (β v : F)
    (hE : E = C β*T*D) (hEi : E = (X-C v)*Ei) (hTi : T = (X-C v)*Ti) :
    Ei = C β*D*Ti := by
  apply mul_left_cancel₀ (monic_X_sub_C v).ne_zero
  rw [← hEi, hE, hTi]
  ring

lemma presentation_far_cofactor (E D T Di Ei : F[X]) (β v : F)
    (hE : E = C β*T*D) (hEi : E = (X-C v)*Ei) (hDi : D = (X-C v)*Di) :
    Ei = C β*T*Di := by
  apply mul_left_cancel₀ (monic_X_sub_C v).ne_zero
  rw [← hEi, hE, hDi]
  ring

/-- Normalize a finite partial-fraction certificate and partition every pole
into its near and far terms. All numerator powers are retained in α. -/
theorem presentation_normalize_partition
    (N E A D T P : F[X]) (s near : Finset ι) (hne : near ⊆ s)
    (r c : ι → F) (Ei Ti Di : ι → F[X]) (α β : F) (hα : α ≠ 0)
    (hN : N = C α*A) (hE : E = C β*T*D)
    (hEi : ∀ i ∈ s, E = (X-C (r i))*Ei i)
    (hTi : ∀ i ∈ near, T = (X-C (r i))*Ti i)
    (hDi : ∀ i ∈ s\near, D = (X-C (r i))*Di i)
    (hidentity : N = E*P + ∑ i ∈ s, C (c i)*Ei i) :
    A = D*T*(C (β/α)*P) + D*(∑ i ∈ near, C ((β/α)*c i)*Ti i) +
      ∑ i ∈ s\near, C ((β/α)*c i)*T*Di i := by
  have hs : (∑ i ∈ s, C (c i)*Ei i) =
      (∑ i ∈ near, C (c i)*Ei i) + ∑ i ∈ s\near, C (c i)*Ei i := by
    have hh := Finset.sum_sdiff hne (f := fun i => C (c i)*Ei i)
    linear_combination -hh
  have hn : (∑ i ∈ near, C (c i)*Ei i) = C β*D*(∑ i ∈ near, C (c i)*Ti i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [presentation_near_cofactor E D T (Ti i) (Ei i) β (r i) hE (hEi i (hne hi)) (hTi i hi)]
    ring
  have hf : (∑ i ∈ s\near, C (c i)*Ei i) = C β*(∑ i ∈ s\near, C (c i)*T*Di i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [presentation_far_cofactor E D T (Di i) (Ei i) β (r i) hE
      (hEi i (Finset.mem_sdiff.mp hi).1) (hDi i hi)]
    ring
  rw [hN, hE, hs, hn, hf] at hidentity
  have hc : (C α : F[X])*C (β/α) = C β := by
    rw [← map_mul]
    congr 1
    field_simp
  have hb : A = C (β/α)*(D*T*P + D*(∑ i ∈ near, C (c i)*Ti i) +
      ∑ i ∈ s\near, C (c i)*T*Di i) := by
    apply mul_left_cancel₀ (C_ne_zero.mpr hα)
    rw [← mul_assoc, hc]
    linear_combination hidentity
  rw [hb]
  simp only [mul_add, Finset.mul_sum, map_mul]
  have hn' : (∑ i ∈ near, C (β/α)*(D*(C (c i)*Ti i))) =
      ∑ i ∈ near, D*(C (β/α)*C (c i)*Ti i) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hf' : (∑ i ∈ s\near, C (β/α)*(C (c i)*T*Di i)) =
      ∑ i ∈ s\near, C (β/α)*C (c i)*T*Di i := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hn', hf']
  ring

lemma polynomial_factor_of_eval_zero (D : F[X]) (v : F) (hv : D.eval v = 0) :
    D = (X-C v)*(D/(X-C v)) := by
  obtain ⟨Q, hQ⟩ := (dvd_iff_isRoot (p := D) (a := v)).mpr hv
  rw [hQ, mul_div_cancel_left₀ _ (monic_X_sub_C v).ne_zero]

lemma far_factor_of_scaled_denominator (E T D Ei : F[X]) (β v : F)
    (hβ : β ≠ 0) (hT : T.eval v ≠ 0)
    (hE : E = C β*T*D) (hEi : E = (X-C v)*Ei) :
    D = (X-C v)*(D/(X-C v)) := by
  apply polynomial_factor_of_eval_zero
  have he : E.eval v = 0 := by rw [hEi]; simp
  rw [hE, eval_mul, eval_mul, eval_C] at he
  exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero hβ hT)

/-- Each near coefficient is forced by the original numerator evaluation;
this derives the residue formula rather than taking it as an extra analytic
assumption. -/
theorem near_residue_from_certificate (A D P : F[X]) (s : Finset ι)
    (r b : ι → F) (hinj : Set.InjOn r s)
    {κ : Type*} (t : Finset κ) (c : κ → F) (Dk : κ → F[X])
    (he : A = D*Lagrange.nodal s r*P +
      D*(∑ j ∈ s, C (b j)*Lagrange.nodal (s.erase j) r) +
      ∑ k ∈ t, C (c k)*Lagrange.nodal s r*Dk k)
    (i : ι) (hi : i ∈ s) (hD : D.eval (r i) ≠ 0) :
    b i = A.eval (r i)/(D.eval (r i)*(∏ j ∈ s.erase i, (r i-r j))) := by
  have hT : (Lagrange.nodal s r).eval (r i) = 0 := Lagrange.eval_nodal_at_node hi
  have hprod : (∏ j ∈ s.erase i, (r i-r j)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    apply sub_ne_zero.mpr
    intro hh
    have hij := hinj hi (Finset.mem_of_mem_erase hj) hh
    exact (Finset.ne_of_mem_erase hj) hij.symm
  have hsum : (∑ j ∈ s, C (b j)*Lagrange.nodal (s.erase j) r).eval (r i) =
      b i*(∏ j ∈ s.erase i, (r i-r j)) := by
    rw [eval_finsetSum, Finset.sum_eq_single i]
    · simp [Lagrange.nodal, eval_prod]
    · intro j hj hji
      have hroot : i ∈ s.erase j := Finset.mem_erase.mpr ⟨hji.symm, hi⟩
      simp only [eval_mul, eval_C, Lagrange.eval_nodal_at_node hroot, mul_zero]
    · exact fun hh => False.elim (hh hi)
  have hh := congrArg (Polynomial.eval (r i)) he
  simp only [eval_add, eval_mul, eval_C, hT, mul_zero, zero_mul, zero_add,
    hsum, eval_finsetSum] at hh
  simp only [eval_mul, eval_C, hT, mul_zero, zero_mul, Finset.sum_const_zero, add_zero] at hh
  apply (eq_div_iff (mul_ne_zero hD hprod)).mpr
  linear_combination -hh

#print axioms presentation_normalize_partition
end Zeta5Local
