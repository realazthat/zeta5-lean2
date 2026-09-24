import FullPullbackCertificate
import SmallPrimeFactorials

namespace Zeta5Local
open Polynomial Zeta5Construction

/-- Centered indexing of the two signed roots ±(i+1). -/
def smallPrimeRootIndex (K : ℕ) (ib : Fin K × Bool) : ℕ :=
  if ib.2 = true then K-(ib.1.val+1) else K+(ib.1.val+1)

lemma smallPrimeRootIndex_mem (K : ℕ) (ib : Fin K × Bool) :
    smallPrimeRootIndex K ib ∈ smallPrimeRoots K := by
  rcases ib with ⟨i,b⟩
  simp only [smallPrimeRoots, Finset.mem_erase, Finset.mem_range]
  have hi := i.isLt
  cases b <;> simp only [smallPrimeRootIndex, Bool.false_eq_true, if_false, if_true] <;> omega

lemma smallPrimeRootIndex_injective (K : ℕ) : Function.Injective (smallPrimeRootIndex K) := by
  rintro ⟨i,b⟩ ⟨j,c⟩ he
  have hi := i.isLt
  have hj := j.isLt
  cases b <;> cases c <;>
    simp only [smallPrimeRootIndex, Bool.false_eq_true, if_false, if_true] at he
  · have heij : i=j := Fin.ext (by omega)
    subst j
    rfl
  · omega
  · omega
  · have heij : i=j := Fin.ext (by omega)
    subst j
    rfl

noncomputable def smallPrimeRootEquiv (K : ℕ) :
    (Fin K × Bool) ≃ {j // j∈smallPrimeRoots K} :=
  Equiv.ofBijective (fun ib => ⟨smallPrimeRootIndex K ib, smallPrimeRootIndex_mem K ib⟩) (by
    constructor
    · intro i j he
      exact smallPrimeRootIndex_injective K (congrArg Subtype.val he)
    · intro j
      have hj := j.property
      simp only [smallPrimeRoots, Finset.mem_erase, Finset.mem_range] at hj
      by_cases hjK : j.val<K
      · refine ⟨(⟨K-j.val-1, by omega⟩,true), ?_⟩
        apply Subtype.ext
        simp only [smallPrimeRootIndex, if_true]
        omega
      · refine ⟨(⟨j.val-K-1, by omega⟩,false), ?_⟩
        apply Subtype.ext
        simp only [smallPrimeRootIndex, Bool.false_eq_true, if_false]
        omega)

lemma smallPrimeRootEquiv_apply (K : ℕ) (ib : Fin K × Bool) :
    (smallPrimeRootEquiv K ib).val = smallPrimeRootIndex K ib := rfl

lemma smallPrimeRootEquiv_integer (K : ℕ) (ib : Fin K × Bool) :
    ((smallPrimeRootEquiv K ib).val : ℤ)-K = actualSignedIntegerRoot 0 ib := by
  rcases ib with ⟨i,b⟩
  have hi := i.isLt
  rw [smallPrimeRootEquiv_apply]
  cases b <;>
    simp only [smallPrimeRootIndex, actualSignedIntegerRoot, Zeta5Construction.poleIndex,
      Bool.false_eq_true, if_false, if_true, Nat.zero_add] <;> omega

lemma smallPrimeRootEquiv_root (K : ℕ) (ib : Fin K × Bool) :
    smallPrimeRoot K (smallPrimeRootEquiv K ib).val = actualSignedRoot 0 ib := by
  rw [←actualSignedIntegerRoot_cast, ←smallPrimeRootEquiv_integer K ib]
  simp [smallPrimeRoot]

lemma smallPrimeRootEquiv_sum {R : Type*} [AddCommMonoid R] (K : ℕ) (f : ℕ → R) :
    (∑ j∈smallPrimeRoots K, f j) = ∑ ib : Fin K × Bool, f (smallPrimeRootEquiv K ib).val := by
  rw [←Finset.sum_coe_sort]
  exact (Equiv.sum_comp (smallPrimeRootEquiv K) (fun j => f j.val)).symm


lemma smallPrimeRootEquiv_prod {R : Type*} [CommMonoid R] (K : ℕ) (f : ℕ → R) :
    (∏ j∈smallPrimeRoots K, f j) = ∏ ib : Fin K × Bool, f (smallPrimeRootEquiv K ib).val := by
  rw [←Finset.prod_coe_sort]
  exact (Equiv.prod_comp (smallPrimeRootEquiv K) (fun j => f j.val)).symm

lemma actualSignedRoot_nodal (K : ℕ) :
    Lagrange.nodal Finset.univ (actualSignedRoot 0 (h := K)) =
      C ((-1:ℚ)^K)*(denominator K).comp (-(X^2)) := by
  rw [Lagrange.nodal, Fintype.prod_prod_type]
  simp only [Fintype.prod_bool, actualSignedRoot, Bool.false_eq_true, if_false, if_true,
    map_neg, sub_neg_eq_add]
  have hd : (denominator K).comp (-(X^2)) =
      ∏ i : Fin K, (-(X^2)+C ((Zeta5Construction.poleIndex 0 i : ℚ)^2)) := by
    rw [←tailDenominator_zero, tailDenominator, Polynomial.prod_comp]
    simp only [sub_comp, add_comp, X_comp, C_comp, node, map_neg, sub_neg_eq_add]
  rw [hd]
  calc
    _ = ∏ i : Fin K, (C (-1:ℚ)*(-(X^2)+C ((Zeta5Construction.poleIndex 0 i : ℚ)^2))) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [map_neg, map_one, map_pow]
      ring
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, map_pow]

lemma smallPrimeRoot_nodal (K : ℕ) :
    Lagrange.nodal (smallPrimeRoots K) (smallPrimeRoot K) =
      C ((-1:ℚ)^K)*(denominator K).comp (-(X^2)) := by
  rw [Lagrange.nodal, smallPrimeRootEquiv_prod]
  simp only [smallPrimeRootEquiv_root]
  exact actualSignedRoot_nodal K

lemma actualSignedRoot_nodal_cofactor (K : ℕ) (ib : Fin K × Bool) :
    Lagrange.nodal (Finset.univ.erase ib) (actualSignedRoot 0) =
      C ((-1:ℚ)^K)*actualSignedCofactor 0 K ib := by
  apply mul_left_cancel₀ (monic_X_sub_C (actualSignedRoot 0 ib)).ne_zero
  rw [←Lagrange.nodal_eq_mul_nodal_erase (Finset.mem_univ ib), actualSignedRoot_nodal]
  rw [←tailDenominator_zero, actualSigned_factor]
  ring

lemma actualSignedRoot_injective (K : ℕ) :
    Function.Injective (actualSignedRoot 0 (h := K)) := by
  intro i j he
  apply (smallPrimeRootEquiv K).injective
  apply Subtype.ext
  apply smallPrimeRoot_inj K
  simpa only [smallPrimeRootEquiv_root] using he

lemma smallPrimeRoot_nodal_cofactor (K : ℕ) (ib : Fin K × Bool) :
    Lagrange.nodal ((smallPrimeRoots K).erase (smallPrimeRootEquiv K ib).val) (smallPrimeRoot K) =
      C ((-1:ℚ)^K)*actualSignedCofactor 0 K ib := by
  apply mul_left_cancel₀ (monic_X_sub_C (smallPrimeRoot K (smallPrimeRootEquiv K ib).val)).ne_zero
  rw [←Lagrange.nodal_eq_mul_nodal_erase (smallPrimeRootEquiv K ib).property,
    smallPrimeRoot_nodal, smallPrimeRootEquiv_root]
  rw [←tailDenominator_zero, actualSigned_factor]
  ring

#print axioms smallPrimeRootEquiv
#print axioms smallPrimeRootEquiv_root
#print axioms smallPrimeRoot_nodal
#print axioms actualSignedRoot_nodal_cofactor
end Zeta5Local
