import InnerBasis
import InnerFactorization

noncomputable section
open scoped BigOperators
namespace Zeta5InnerRowFactors
open Polynomial Zeta5ResidueFactorization

variable (m : ℕ)
def root (i : Fin (m+1)×Bool) : ℤ := if i.2 then i.1.val else -(i.1.val:ℤ)
def weight (ν : Fin (m+1)→ℕ) (i : Fin (m+1)×Bool) : ℕ := ν i.1

def rowPolynomial (ν : Fin (m+1)→ℕ) : ℤ[X] :=
  ∏ a, (X+C ((a.val:ℤ)^2))^ν a

lemma sub_divisible (p : ℕ) (hm : 2*m<p) (a b : Fin (m+1)) :
    ((p:ℤ)∣(a.val:ℤ)-b.val) ↔ a=b := by
  rw [Zeta5InnerFactorCounts.dvd_sub_iff_mod,
    Nat.mod_eq_of_lt (by omega : b.val<p), Nat.mod_eq_of_lt (by omega : a.val<p)]
  exact ⟨fun h => Fin.ext h.symm, fun h => by rw [h]⟩

lemma add_divisible (p : ℕ) (hm : 2*m<p) (a b : Fin (m+1)) :
    ((p:ℤ)∣(a.val:ℤ)+b.val) ↔ a=0 ∧ b=0 := by
  rw [←Nat.cast_add, Int.natCast_dvd_natCast]
  have hlt : a.val+b.val<p := by omega
  constructor
  · intro hd
    have hz := Nat.eq_zero_of_dvd_of_lt hd hlt
    exact ⟨Fin.ext (by simp only [Fin.val_zero]; omega), Fin.ext (by simp only [Fin.val_zero]; omega)⟩
  · rintro ⟨rfl,rfl⟩
    simp

lemma near_weight_sum (ν : Fin (m+1)→ℕ) (p : ℕ) (c : ℤ) :
    (∑ i ∈ nearIndices Finset.univ (root m) p c, weight m ν i) =
      ∑ a : Fin (m+1), ((if (p:ℤ)∣c-a.val then ν a else 0)+
        (if (p:ℤ)∣c+a.val then ν a else 0)) := by
  unfold nearIndices
  erw [Finset.sum_filter]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool,
    root, weight, Bool.false_eq_true, if_false, if_true, sub_neg_eq_add]

/-- Exact local degree of a row pullback at an ordinary square class. -/
theorem ordinary_degree (ν : Fin (m+1)→ℕ) (p : ℕ) (hm : 2*m<p)
    (a : Fin (m+1)) (ha : a≠0) :
    (nearWeightedPolynomial Finset.univ (root m) (weight m ν) p a.val).natDegree=ν a := by
  rw [nearWeightedPolynomial_degree, near_weight_sum]
  simp only [sub_divisible m p hm, add_divisible m p hm, ha, false_and, if_false, add_zero]
  simp

/-- At zero both linear factors of the zero-class quadratic are near. -/
theorem zero_degree (ν : Fin (m+1)→ℕ) (p : ℕ) (hm : 2*m<p) :
    (nearWeightedPolynomial Finset.univ (root m) (weight m ν) p 0).natDegree=2*ν 0 := by
  rw [nearWeightedPolynomial_degree, near_weight_sum]
  change (∑ a : Fin (m+1), ((if (p:ℤ)∣((0:Fin (m+1)).val:ℤ)-a.val then ν a else 0)+
    (if (p:ℤ)∣((0:Fin (m+1)).val:ℤ)+a.val then ν a else 0))) = _
  simp only [sub_divisible m p hm, add_divisible m p hm, true_and]
  rw [Finset.sum_add_distrib]
  simp [two_mul]

lemma row_pullback (ν : Fin (m+1)→ℕ) :
    (∏ i : Fin (m+1)×Bool, (X-C (root m i))^weight m ν i) =
      C ((-1:ℤ)^(∑ a,ν a))*(rowPolynomial m ν).comp (-(X^2)) := by
  simp only [Fintype.prod_prod_type, Fintype.prod_bool, root, weight,
    Bool.false_eq_true, if_false, if_true, map_neg, sub_neg_eq_add,
    rowPolynomial, Polynomial.prod_comp, Polynomial.pow_comp, Polynomial.add_comp,
    Polynomial.X_comp, Polynomial.C_comp]
  calc
    _ = ∏ a : Fin (m+1), C (-1:ℤ)^ν a * (-(X^2)+C ((a.val:ℤ)^2))^ν a := by
      apply Finset.prod_congr rfl
      intro a ha
      rw [←mul_pow, ←mul_pow]
      congr 1
      rw [map_pow, map_neg, map_one]
      ring
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_pow]

#print axioms ordinary_degree
#print axioms row_pullback
end Zeta5InnerRowFactors
