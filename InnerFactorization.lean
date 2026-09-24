import InnerFactorCounts
import InnerRoots
import Construction

noncomputable section
open scoped BigOperators
namespace Zeta5InnerFactorization
open Polynomial Zeta5ResidueFactorization Zeta5InnerFactorCounts

def signedRoot (j : ℕ×Bool) : ℤ := if j.2 then j.1 else -(j.1:ℤ)
def signedIndices (A : ℕ) : Finset (ℕ×Bool) := (Finset.Icc 1 A) ×ˢ Finset.univ

lemma near_card (A p : ℕ) (c : ℤ) :
    (nearIndices (signedIndices A) signedRoot p c).card = linearNearCount A p c := by
  simp only [nearIndices, Finset.card_filter, signedIndices, Finset.sum_product,
    Fintype.sum_bool, signedRoot, Bool.false_eq_true, if_false, if_true, sub_neg_eq_add]
  unfold linearNearCount
  apply Finset.sum_congr rfl
  intro j hj
  omega

lemma signedRoot_inj (A : ℕ) : Set.InjOn signedRoot (signedIndices A : Set (ℕ×Bool)) := by
  intro j hj k hk he
  have hj' := Finset.mem_product.mp hj
  have hk' := Finset.mem_product.mp hk
  have hjp := (Finset.mem_Icc.mp hj'.1).1
  have hkp := (Finset.mem_Icc.mp hk'.1).1
  rcases j with ⟨j,b⟩
  rcases k with ⟨k,d⟩
  cases b <;> cases d <;> simp [signedRoot] at he ⊢ <;> omega

lemma signedRoot_bound (A : ℕ) (j : ℕ×Bool) (hj : j∈signedIndices A) :
    -(A:ℤ)≤signedRoot j ∧ signedRoot j≤A := by
  have h := Finset.mem_Icc.mp (Finset.mem_product.mp hj).1
  unfold signedRoot
  split_ifs <;> omega

def signedProduct (A : ℕ) : ℤ[X] := ∏ j ∈ signedIndices A, (X-C (signedRoot j))

def integerDenominator (A : ℕ) : ℤ[X] :=
  ∏ j ∈ Finset.Icc 1 A, (X+C ((j:ℤ)^2))

lemma signedProduct_pullback (A : ℕ) :
    signedProduct A = C ((-1:ℤ)^A) * (integerDenominator A).comp (-(X^2)) := by
  simp only [signedProduct, signedIndices, Finset.prod_product, Fintype.prod_bool,
    signedRoot, Bool.false_eq_true, if_false, if_true, map_neg, sub_neg_eq_add,
    integerDenominator, Polynomial.prod_comp, Polynomial.add_comp,
    Polynomial.X_comp, Polynomial.C_comp]
  calc
    _ = ∏ j ∈ Finset.Icc 1 A, C (-1:ℤ) * (-(X^2)+C ((j:ℤ)^2)) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [map_pow, map_neg, map_one]
      ring
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel, ←map_pow]

lemma integerDenominator_map (A : ℕ) :
    (integerDenominator A).map (Int.castRingHom ℚ) = Zeta5Construction.denominator A := by
  unfold integerDenominator Zeta5Construction.denominator
  rw [Polynomial.map_prod]
  have he : (∏ j ∈ Finset.Icc 1 A, (X+C ((j:ℚ)^2))) =
      ∏ k ∈ Finset.range A, (X+C (((k+1:ℕ):ℚ)^2)) := by
    apply Finset.prod_bij (fun j _ => j-1)
    · intro j hj
      have h := Finset.mem_Icc.mp hj
      simp only [Finset.mem_range]
      omega
    · intro i hi j hj he
      have hi' := Finset.mem_Icc.mp hi
      have hj' := Finset.mem_Icc.mp hj
      omega
    · intro k hk
      refine ⟨k+1, ?_, by omega⟩
      simp only [Finset.mem_Icc, Finset.mem_range] at *
      omega
    · intro j hj
      have hj' := Finset.mem_Icc.mp hj
      rw [Nat.sub_add_cancel hj'.1]
  simpa using he

/-- Denominator degree at an ordinary source is exactly the paper count. -/
theorem ordinary_near_degree (A p a : ℕ) (ha : 1≤a) (hap : 2*a<p) :
    (nearPolynomial (signedIndices A) signedRoot p a).natDegree =
      Zeta5Parameters.poleCount A p a := by
  rw [nearPolynomial_degree, near_card, linearNearCount_ordinary A p a ha hap]

/-- The zero residue has two near linear factors per multiple of p. -/
theorem zero_near_degree (A p : ℕ) (hp : 0<p) :
    (nearPolynomial (signedIndices A) signedRoot p 0).natDegree = 2*(A/p) := by
  rw [nearPolynomial_degree, near_card, linearNearCount_zero A p hp]

#print axioms signedProduct_pullback
#print axioms ordinary_near_degree
end Zeta5InnerFactorization
