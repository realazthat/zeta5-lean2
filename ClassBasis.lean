import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
open Polynomial

namespace Zeta5ClassBasis

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]

def complement (Q : ι → F[X]) (i : ι) : F[X] :=
  ∏ j ∈ Finset.univ.erase i, Q j

lemma complement_coprime (Q : ι → F[X])
    (hc : Pairwise fun i j => IsCoprime (Q i) (Q j)) (i : ι) :
    IsCoprime (Q i) (complement Q i) := by
  apply IsCoprime.prod_right
  intro j hj
  exact hc (Finset.mem_erase.mp hj).1.symm

lemma dvd_complement (Q : ι → F[X]) {i j : ι} (hij : i ≠ j) :
    Q i ∣ complement Q j := by
  exact Finset.dvd_prod_of_mem Q (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ _⟩)

/-- The algebraic CRT step: a vanishing combination of separate classes
vanishes separately in each class when local degrees are smaller. -/
theorem class_sum_injective (Q B : ι → F[X])
    (hc : Pairwise fun i j => IsCoprime (Q i) (Q j))
    (hd : ∀ i, (B i).degree < (Q i).degree)
    (hs : ∑ i, complement Q i * B i = 0) : ∀ i, B i = 0 := by
  intro i
  have hother : Q i ∣ ∑ j ∈ Finset.univ.erase i, complement Q j * B j := by
    apply Finset.dvd_sum
    intro j hj
    exact dvd_mul_of_dvd_left (dvd_complement Q (Finset.mem_erase.mp hj).1.symm) _
  have hself : Q i ∣ complement Q i * B i := by
    have hsplit := Finset.sum_erase_add Finset.univ
      (fun j => complement Q j * B j) (Finset.mem_univ i)
    rw [hs] at hsplit
    have h := dvd_sub (show Q i ∣ (0 : F[X]) from dvd_zero _) hother
    simpa only [zero_sub, ← eq_neg_of_add_eq_zero_right hsplit] using h
  exact eq_zero_of_dvd_of_degree_lt ((complement_coprime Q hc i).dvd_of_dvd_mul_left hself)
    (hd i)

/-- Successive local degrees give linearly independent local rows. -/
theorem local_polynomials_independent (d : ℕ) (q : Fin d → F[X])
    (hq : ∀ k, (q k).degree = (k.val : ℕ)) : LinearIndependent F q := by
  let S : Polynomial.Sequence F :=
    ⟨fun k => if h : k < d then q ⟨k, h⟩ else X ^ k,
      fun k => by split_ifs with hk; exact hq ⟨k, hk⟩; simp⟩
  have := S.linearIndependent.comp (fun k : Fin d => k.val) Fin.val_injective
  simpa [S, Function.comp_def] using this

/-- Local bases multiplied by the other class factors remain independent. -/
theorem class_polynomials_independent (Q : ι → F[X]) (d : ι → ℕ)
    (q : (i : ι) → Fin (d i) → F[X])
    (hc : Pairwise fun i j => IsCoprime (Q i) (Q j))
    (hQ : ∀ i, (Q i).degree = (d i : ℕ))
    (hq : ∀ i k, (q i k).degree = (k.val : ℕ)) :
    LinearIndependent F (fun x : Σ i, Fin (d i) => complement Q x.1 * q x.1 x.2) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hs x
  let B : ι → F[X] := fun i => ∑ k : Fin (d i), c ⟨i, k⟩ • q i k
  have hB : ∀ i, (B i).degree < (Q i).degree := by
    intro i
    rw [hQ i]
    apply mem_degreeLT.mp
    apply (degreeLT F (d i)).sum_mem
    intro k _
    apply (degreeLT F (d i)).smul_mem
    rw [Polynomial.mem_degreeLT, hq]
    exact_mod_cast k.is_lt
  have hsum : ∑ i, complement Q i * B i = 0 := by
    rw [Fintype.sum_sigma] at hs
    convert hs using 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [B, Finset.mul_sum, smul_eq_C_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hzero := class_sum_injective Q B hc hB hsum
  exact Fintype.linearIndependent_iff.mp
    (local_polynomials_independent (d x.1) (q x.1) (hq x.1))
    (fun k => c ⟨x.1, k⟩) (hzero x.1) x.2

lemma coefficients_independent {κ : Type*} [Fintype κ] (n : ℕ) (P : κ → F[X])
    (hP : LinearIndependent F P) (hd : ∀ k, (P k).degree < n) :
    LinearIndependent F (fun k => fun j : Fin n => (P k).coeff j.val) := by
  classical
  rw [Fintype.linearIndependent_iff] at hP ⊢
  intro c hc k
  apply hP c _ k
  ext j
  by_cases hj : j < n
  · have hh := congrFun hc ⟨j, hj⟩
    simpa only [Polynomial.finset_sum_coeff, Polynomial.coeff_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      Polynomial.coeff_zero] using hh
  · have hsum : ∑ k, c k • P k ∈ degreeLT F n := by
      apply (degreeLT F n).sum_mem
      intro k _
      exact (degreeLT F n).smul_mem _ (mem_degreeLT.mpr (hd k))
    exact (coeff_eq_zero_of_degree_lt
      ((mem_degreeLT.mp hsum).trans_le (by exact_mod_cast Nat.le_of_not_gt hj))).trans
      (Polynomial.coeff_zero j).symm

theorem class_polynomial_degree_lt (Q : ι → F[X]) (d : ι → ℕ)
    (q : (i : ι) → Fin (d i) → F[X])
    (hm : ∀ i, (Q i).Monic) (hQ : ∀ i, (Q i).degree = (d i : ℕ))
    (hq : ∀ i k, (q i k).degree = (k.val : ℕ))
    (x : Σ i, Fin (d i)) :
    (complement Q x.1 * q x.1 x.2).degree < (∑ i, d i : ℕ) := by
  have hcomp : (complement Q x.1).Monic :=
    monic_prod_of_monic _ _ (fun i _ => hm i)
  have hdeg : (complement Q x.1).natDegree = ∑ i ∈ Finset.univ.erase x.1, d i := by
    rw [complement, natDegree_prod_of_monic _ _ (fun i _ => hm i)]
    apply Finset.sum_congr rfl
    intro i _
    exact natDegree_eq_of_degree_eq_some (hQ i)
  rw [degree_mul, degree_eq_natDegree hcomp.ne_zero, hdeg, hq,
    ← Nat.cast_add, Nat.cast_lt]
  have hsum := Finset.sum_erase_add Finset.univ d (Finset.mem_univ x.1)
  omega

/-- The coefficient matrix of the paper's CRT rows is nonsingular over
any residue field in which the class factors remain pairwise coprime. -/
theorem class_coefficient_det_ne_zero (Q : ι → F[X]) (d : ι → ℕ)
    (q : (i : ι) → Fin (d i) → F[X])
    (hc : Pairwise fun i j => IsCoprime (Q i) (Q j))
    (hm : ∀ i, (Q i).Monic) (hQ : ∀ i, (Q i).degree = (d i : ℕ))
    (hq : ∀ i k, (q i k).degree = (k.val : ℕ))
    (e : (Σ i, Fin (d i)) ≃ Fin (∑ i, d i)) :
    Matrix.det (fun i j : Σ a, Fin (d a) =>
      (complement Q i.1 * q i.1 i.2).coeff (e j).val) ≠ 0 := by
  classical
  apply IsUnit.ne_zero
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.linearIndependent_rows_iff_isUnit.mp
  have hind := coefficients_independent (∑ i, d i)
    (fun x : Σ i, Fin (d i) => complement Q x.1 * q x.1 x.2)
    (class_polynomials_independent Q d q hc hQ hq)
    (class_polynomial_degree_lt Q d q hm hQ hq)
  rw [Fintype.linearIndependent_iff] at hind ⊢
  intro c hc k
  apply hind c _ k
  funext j
  have hh := congrFun hc (e.symm j)
  simpa using hh

#print axioms class_coefficient_det_ne_zero

theorem integer_class_det_unit (p : ℕ) [Fact p.Prime]
    (Q : ι → ℤ[X]) (d : ι → ℕ)
    (q : (i : ι) → Fin (d i) → ℤ[X])
    (hc : Pairwise fun i j => IsCoprime
      ((Q i).map (Int.castRingHom (ZMod p))) ((Q j).map (Int.castRingHom (ZMod p))))
    (hm : ∀ i, (Q i).Monic) (hQ : ∀ i, (Q i).degree = (d i : ℕ))
    (hqm : ∀ i k, (q i k).Monic)
    (hq : ∀ i k, (q i k).degree = (k.val : ℕ))
    (e : (Σ i, Fin (d i)) ≃ Fin (∑ i, d i)) :
    ¬ (p : ℤ) ∣ Matrix.det (fun i j : Σ a, Fin (d a) =>
      ((∏ a ∈ Finset.univ.erase i.1, Q a) * q i.1 i.2).coeff (e j).val) := by
  classical
  let f := Int.castRingHom (ZMod p)
  have hh := class_coefficient_det_ne_zero (fun i => (Q i).map f) d
    (fun i k => (q i k).map f) hc
    (fun i => (hm i).map f) (fun i => (hm i).degree_map f |>.trans (hQ i))
    (fun i k => (hqm i k).degree_map f |>.trans (hq i k)) e
  intro hdiv
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdiv
  apply hh
  rw [← hz]
  rw [Int.cast_det]
  congr 1
  ext i j
  simp [complement, Polynomial.coeff_map, ← Polynomial.map_prod, ← Polynomial.map_mul]

theorem integer_class_det_valuation (p : ℕ) [Fact p.Prime]
    (Q : ι → ℤ[X]) (d : ι → ℕ)
    (q : (i : ι) → Fin (d i) → ℤ[X])
    (hc : Pairwise fun i j => IsCoprime
      ((Q i).map (Int.castRingHom (ZMod p))) ((Q j).map (Int.castRingHom (ZMod p))))
    (hm : ∀ i, (Q i).Monic) (hQ : ∀ i, (Q i).degree = (d i : ℕ))
    (hqm : ∀ i k, (q i k).Monic)
    (hq : ∀ i k, (q i k).degree = (k.val : ℕ))
    (e : (Σ i, Fin (d i)) ≃ Fin (∑ i, d i)) :
    padicValInt p (Matrix.det (fun i j : Σ a, Fin (d a) =>
      ((∏ a ∈ Finset.univ.erase i.1, Q a) * q i.1 i.2).coeff (e j).val)) = 0 :=
  padicValInt.eq_zero_of_not_dvd (integer_class_det_unit p Q d q hc hm hQ hqm hq e)

theorem square_class_injective (p m : ℕ) [Fact p.Prime] (hm : 2 * m < p) :
    Function.Injective (fun a : Fin (m + 1) => -((a.val : ZMod p) ^ 2)) := by
  intro a b hab
  have hs : (a.val : ZMod p) ^ 2 = (b.val : ZMod p) ^ 2 := neg_injective hab
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with he | he
  · apply Fin.ext
    have hv := congrArg ZMod.val he
    simpa only [ZMod.val_natCast_of_lt (show a.val < p by omega),
      ZMod.val_natCast_of_lt (show b.val < p by omega)] using hv
  · have hab0 : ((a.val + b.val : ℕ) : ZMod p) = 0 := by
      push_cast
      rw [he, neg_add_cancel]
    have hd := (ZMod.natCast_eq_zero_iff _ p).mp hab0
    have hz := (Nat.eq_zero_of_dvd_of_lt hd (show a.val + b.val < p by omega))
    apply Fin.ext
    omega

theorem inner_class_factors_coprime (p m : ℕ) [Fact p.Prime]
    (hm : 2 * m < p) (d : Fin (m + 1) → ℕ) :
    Pairwise fun a b => IsCoprime
      (((X : ℤ[X]) + C (a.val : ℤ)^2)^d a |>.map (Int.castRingHom (ZMod p)))
      (((X : ℤ[X]) + C (b.val : ℤ)^2)^d b |>.map (Int.castRingHom (ZMod p))) := by
  intro a b hab
  have hc := pairwise_coprime_X_sub_C (square_class_injective p m hm) hab
  have hp : IsCoprime
      (((X : (ZMod p)[X]) - C (-(a.val : ZMod p)^2)) ^ d a)
      (((X : (ZMod p)[X]) - C (-(b.val : ZMod p)^2)) ^ d b) := hc.pow
  simpa [map_pow, map_add, Polynomial.map_X, map_C, sub_neg_eq_add, map_neg] using hp

#print axioms integer_class_det_valuation

/-- Unimodularity for exactly the inner-range row polynomials (4.5). -/
theorem inner_basis_unimodular (p m : ℕ) [Fact p.Prime]
    (hm : 2*m < p) (d : Fin (m+1) → ℕ)
    (e : (Σ a, Fin (d a)) ≃ Fin (∑ a, d a)) :
    padicValInt p (Matrix.det (fun i j : Σ a, Fin (d a) =>
      ((∏ a ∈ Finset.univ.erase i.1,
        ((X : ℤ[X]) + C ((a.val : ℤ)^2)) ^ d a) *
        ((X : ℤ[X]) + C ((i.1.val : ℤ)^2)) ^ i.2.val).coeff (e j).val)) = 0 := by
  apply integer_class_det_valuation p
    (fun a => ((X : ℤ[X]) + C ((a.val : ℤ)^2)) ^ d a) d
    (fun a k => ((X : ℤ[X]) + C ((a.val : ℤ)^2)) ^ k.val)
  · simpa only [map_pow] using inner_class_factors_coprime p m hm d
  · intro a
    exact (monic_X_add_C _).pow _
  · intro a
    rw [degree_pow, degree_X_add_C]
    simp
  · intro a k
    exact (monic_X_add_C _).pow _
  · intro a k
    rw [degree_pow, degree_X_add_C]
    simp

#print axioms inner_basis_unimodular

end Zeta5ClassBasis
