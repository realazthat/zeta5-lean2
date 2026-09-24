import OuterValuation
import ClassBasis
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
open Polynomial Matrix Zeta5Outer

namespace Zeta5BasisTransfer

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]

def congruence (A : Matrix ι ι F[X]) (B : Matrix ι ι F) : Matrix ι ι F[X] :=
  (B.map C) * A * (B.map C)ᵀ

theorem congruence_det (A : Matrix ι ι F[X]) (B : Matrix ι ι F) :
    (congruence A B).det = C (B.det ^ 2) * A.det := by
  have hm : (B.map C).det = C B.det := (C.map_det B).symm
  simp only [congruence, Matrix.det_mul, Matrix.det_transpose, hm]
  simp only [map_pow]
  ring

theorem congruence_det_coeff (A : Matrix ι ι F[X]) (B : Matrix ι ι F) (k : ℕ) :
    (congruence A B).det.coeff k = B.det ^ 2 * A.det.coeff k := by
  rw [congruence_det, coeff_C_mul]

theorem congruence_preserves_coeffLower (v : AddValuation F (WithTop ℚ))
    (A : Matrix ι ι F[X]) (B : Matrix ι ι F) (hu : v B.det = 0) (e : ℚ) :
    CoeffLower v (congruence A B).det e ↔ CoeffLower v A.det e := by
  unfold CoeffLower
  simp only [congruence_det_coeff, pow_two, AddValuation.map_mul, hu, zero_add]

/-- Arbitrary rational row weights are allowed here; in particular this
applies to the positive weights in the inner range. -/
theorem weighted_det_bound (v : AddValuation F (WithTop ℚ))
    (A : Matrix ι ι F[X]) (w : ι → ℚ)
    (hA : ∀ i j, CoeffLower v (A i j) (w i + w j)) :
    CoeffLower v A.det (2 * ∑ i, w i) := by
  apply polynomial_det_lower_of_permutation_bounds v A (fun i j => w i + w j)
    (2 * ∑ i, w i) hA
  intro σ
  rw [Finset.sum_add_distrib, Equiv.sum_comp σ w]
  exact le_of_eq (by ring)

theorem integer_det_valuation_zero (p : ℕ) [Fact p.Prime]
    (B : Matrix ι ι ℤ) (hu : ¬ (p : ℤ) ∣ B.det) :
    rationalPadicValuation p (B.map (Int.castRingHom ℚ)).det = 0 := by
  have hn : B.det ≠ 0 := fun h => hu (h ▸ dvd_zero _)
  have hq : (B.det : ℚ) ≠ 0 := by exact_mod_cast hn
  change rationalPadicValuation p (B.map (fun x : ℤ => (x : ℚ))).det = 0
  rw [← Int.cast_det]
  simp [rationalPadicValuation_apply, hq, padicValRat.of_int,
    padicValInt.eq_zero_of_not_dvd hu]

theorem integer_basis_weighted_det_bound (p : ℕ) [Fact p.Prime]
    (A : Matrix ι ι ℚ[X]) (B : Matrix ι ι ℤ) (w : ι → ℚ)
    (hu : ¬ (p : ℤ) ∣ B.det)
    (hA : ∀ i j, CoeffLower (rationalPadicValuation p)
      (congruence A (B.map (Int.castRingHom ℚ)) i j) (w i + w j)) :
    ∀ k, A.det.coeff k ≠ 0 → 2 * ∑ i, w i ≤ (padicValRat p (A.det.coeff k) : ℚ) := by
  have hh := weighted_det_bound (rationalPadicValuation p)
    (congruence A (B.map (Int.castRingHom ℚ))) w hA
  have hh' := (congruence_preserves_coeffLower (rationalPadicValuation p) A
    (B.map (Int.castRingHom ℚ)) (integer_det_valuation_zero p B hu) _).mp hh
  intro k hk
  exact ((rationalPadicValuation_lower_iff p _ _).mp (hh' k)).resolve_left hk

#print axioms integer_basis_weighted_det_bound

def gram (φ : F[X] →ₗ[F] F[X]) (v : ι → F[X]) : Matrix ι ι F[X] :=
  fun i j => φ (v i * v j)

def basisRows (B : Matrix ι ι F) (v : ι → F[X]) : ι → F[X] :=
  fun i => ∑ j, B i j • v j

/-- Applying a polynomial functional to products of new row polynomials
is exactly matrix congruence of the original Gram matrix. -/
theorem gram_basisRows (φ : F[X] →ₗ[F] F[X]) (v : ι → F[X])
    (B : Matrix ι ι F) : gram φ (basisRows B v) = congruence (gram φ v) B := by
  apply Matrix.ext
  intro i j
  simp only [gram, basisRows, congruence, Matrix.mul_assoc, Matrix.mul_apply,
    Matrix.map_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, smul_smul, map_sum, map_smul]
  simp only [smul_eq_C_mul, map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

#print axioms gram_basisRows

end Zeta5BasisTransfer
