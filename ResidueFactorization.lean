import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
open Polynomial

namespace Zeta5ResidueFactorization

variable {ι : Type*} [DecidableEq ι]

def nearIndices (s : Finset ι) (r : ι → ℤ) (p : ℕ) (c : ℤ) : Finset ι :=
  s.filter fun i => (p : ℤ) ∣ c-r i

def farIndices (s : Finset ι) (r : ι → ℤ) (p : ℕ) (c : ℤ) : Finset ι :=
  s.filter fun i => ¬ (p : ℤ) ∣ c-r i

def nearPolynomial (s : Finset ι) (r : ι → ℤ) (p : ℕ) (c : ℤ) : ℤ[X] :=
  ∏ i ∈ nearIndices s r p c, (X+C ((c-r i)/(p : ℤ)))

def farPolynomial (s : Finset ι) (r : ι → ℤ) (p : ℕ) (c : ℤ) : ℤ[X] :=
  ∏ i ∈ farIndices s r p c, (X+C (c-r i))

lemma near_factor (p : ℕ) (c r : ℤ) (h : (p : ℤ) ∣ c-r) :
    (C (p : ℤ)*X+C (c-r) : ℤ[X]) = C (p : ℤ)*(X+C ((c-r)/(p : ℤ))) := by
  have he : (p : ℤ)*((c-r)/(p : ℤ)) = c-r := Int.mul_ediv_cancel' h
  rw [mul_add, ← map_mul, he]

/-- Exact residue-disk factorization. No partial-fraction subtraction is
used, so all numerator powers of p are retained. -/
theorem translated_product_factorization (s : Finset ι) (r : ι → ℤ) (p : ℕ) (c : ℤ) :
    (∏ i ∈ s, (C (p : ℤ)*X+C (c-r i) : ℤ[X])) =
      C ((p : ℤ)^(nearIndices s r p c).card) * nearPolynomial s r p c *
        (farPolynomial s r p c).comp (C (p : ℤ)*X) := by
  have hp := Finset.prod_filter_mul_prod_filter_not s
    (fun i => (p : ℤ) ∣ c-r i) (fun i => (C (p : ℤ)*X+C (c-r i) : ℤ[X]))
  rw [← hp]
  have hn : (∏ i ∈ nearIndices s r p c, (C (p : ℤ)*X+C (c-r i) : ℤ[X])) =
      C ((p : ℤ)^(nearIndices s r p c).card) * nearPolynomial s r p c := by
    rw [map_pow, nearPolynomial, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    exact near_factor p c (r i) (Finset.mem_filter.mp hi).2
  change (∏ i ∈ nearIndices s r p c, _) * (∏ i ∈ farIndices s r p c, _) = _
  rw [hn]
  congr 1
  simp [farPolynomial, Polynomial.prod_comp]

theorem nearPolynomial_monic (s : Finset ι) (r : ι → ℤ) (p : ℕ) (c : ℤ) :
    (nearPolynomial s r p c).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => monic_X_add_C _)

theorem nearPolynomial_degree (s : Finset ι) (r : ι → ℤ) (p : ℕ) (c : ℤ) :
    (nearPolynomial s r p c).natDegree = (nearIndices s r p c).card := by
  rw [nearPolynomial, natDegree_prod_of_monic _ _ (fun _ _ => monic_X_add_C _)]
  simp only [natDegree_X_add_C, Finset.sum_const, nsmul_eq_mul, Nat.cast_id, mul_one]

theorem farPolynomial_constant_unit (s : Finset ι) (r : ι → ℤ) (p : ℕ) [Fact p.Prime]
    (c : ℤ) : ¬ (p : ℤ) ∣ (farPolynomial s r p c).coeff 0 := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [farPolynomial, Polynomial.coeff_zero_prod, coeff_add, coeff_X_zero,
    coeff_C_zero, zero_add, Int.cast_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact fun hh => (Finset.mem_filter.mp hi).2
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hh)

def nearWeightedPolynomial (s : Finset ι) (r : ι → ℤ) (w : ι → ℕ)
    (p : ℕ) (c : ℤ) : ℤ[X] :=
  ∏ i ∈ nearIndices s r p c, (X+C ((c-r i)/(p:ℤ)))^w i

def farWeightedPolynomial (s : Finset ι) (r : ι → ℤ) (w : ι → ℕ)
    (p : ℕ) (c : ℤ) : ℤ[X] :=
  ∏ i ∈ farIndices s r p c, (X+C (c-r i))^w i

theorem translated_weighted_product_factorization (s : Finset ι) (r : ι → ℤ)
    (w : ι → ℕ) (p : ℕ) (c : ℤ) :
    (∏ i ∈ s, (C (p:ℤ)*X+C (c-r i) : ℤ[X])^w i) =
      C ((p:ℤ)^(∑ i ∈ nearIndices s r p c, w i)) *
        nearWeightedPolynomial s r w p c *
        (farWeightedPolynomial s r w p c).comp (C (p:ℤ)*X) := by
  have hp := Finset.prod_filter_mul_prod_filter_not s
    (fun i => (p:ℤ)∣c-r i) (fun i => (C (p:ℤ)*X+C (c-r i) : ℤ[X])^w i)
  rw [←hp]
  change (∏ i ∈ nearIndices s r p c, _) * (∏ i ∈ farIndices s r p c, _) = _
  have hn : (∏ i ∈ nearIndices s r p c, (C (p:ℤ)*X+C (c-r i) : ℤ[X])^w i) =
      C ((p:ℤ)^(∑ i ∈ nearIndices s r p c, w i)) * nearWeightedPolynomial s r w p c := by
    calc
      _ = ∏ i ∈ nearIndices s r p c,
          C (p:ℤ)^w i * (X+C ((c-r i)/(p:ℤ)))^w i := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [near_factor p c (r i) (Finset.mem_filter.mp hi).2, mul_pow]
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_pow]; rfl
  rw [hn]
  congr 1
  simp [farWeightedPolynomial, Polynomial.prod_comp]

theorem nearWeightedPolynomial_monic (s : Finset ι) (r : ι → ℤ) (w : ι → ℕ)
    (p : ℕ) (c : ℤ) : (nearWeightedPolynomial s r w p c).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => (monic_X_add_C _).pow _)

theorem nearWeightedPolynomial_degree (s : Finset ι) (r : ι → ℤ) (w : ι → ℕ)
    (p : ℕ) (c : ℤ) :
    (nearWeightedPolynomial s r w p c).natDegree = ∑ i ∈ nearIndices s r p c, w i := by
  rw [nearWeightedPolynomial, natDegree_prod_of_monic _ _ (fun _ _ => (monic_X_add_C _).pow _)]
  simp only [natDegree_pow, natDegree_X_add_C, mul_one]

#print axioms translated_weighted_product_factorization

#print axioms translated_product_factorization

end Zeta5ResidueFactorization
