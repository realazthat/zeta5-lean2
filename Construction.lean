import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# The explicit determinant construction in Section 2

Source: A. Fauzan, Zenodo 22826419, 17 September 2026.
This file defines the polynomial quotient, simple-pole residues, affine
Hankel matrix and determinant over the rationals. It proves unconditionally
that the determinant has the claimed degree. It does not assert the
analytic or p-adic estimates required to prove irrationality.

The definitions use general N,h; the paper has N=3n, h=37n and K=N+h.
The rational function after cancellation is D_N(t)^5 t^e / D_tail(t).
-/

noncomputable section
open scoped BigOperators
open Polynomial Matrix

namespace Zeta5Construction

/-- Equation (2.2), with mathlib's B₁=-1/2 convention. -/
def moment (e : ℕ) : ℚ :=
  (-1)^e * bernoulli (2*e+2) * (2*e+3) * (2*e+4) * (2*e+5) / 24

/-- The rational functional restricted to polynomials. -/
def polynomialFunctional : ℚ[X] →ₗ[ℚ] ℚ :=
  Polynomial.lsum fun e => moment e • LinearMap.id

/-- The finite fifth harmonic sum, H_j^(5). -/
def harmonic5 (j : ℕ) : ℚ := ∑ v ∈ Finset.range j, 1 / ((v+1 : ℕ) : ℚ)^5

/-- D_N(t)=∏_{j=1}^N(t+j²). -/
def denominator (N : ℕ) : ℚ[X] :=
  ∏ k ∈ Finset.range N, (X + C (((k+1 : ℕ) : ℚ)^2))

/-- The h surviving pole indices N+1,...,N+h. -/
def poleIndex (N : ℕ) {h : ℕ} (i : Fin h) : ℕ := N+1+i.val

/-- The simple poles -j². -/
def node (N : ℕ) {h : ℕ} (i : Fin h) : ℚ := -((poleIndex N i : ℕ) : ℚ)^2

/-- D_tail(t)=∏_{j=N+1}^{N+h}(t+j²). -/
def tailDenominator (N h : ℕ) : ℚ[X] :=
  ∏ i : Fin h, (X-C (node N i))

/-- D_tail'(-j²), expressed as the product of the other linear factors. -/
def poleDenominator (N : ℕ) {h : ℕ} (i : Fin h) : ℚ :=
  ∏ k ∈ Finset.univ.erase i, (node N i-node N k)

/-- Numerator of the rational function after D_N cancellation. -/
def numerator (N e : ℕ) : ℚ[X] := denominator N ^ 5 * X^e

/-- The constant polynomial part from Euclidean division. -/
def quotientMoment (N h e : ℕ) : ℚ :=
  polynomialFunctional (numerator N e / tailDenominator N h)

/-- Residue at the surviving simple pole. -/
def residue (N e : ℕ) {h : ℕ} (i : Fin h) : ℚ :=
  (numerator N e).eval (node N i) / poleDenominator N i

/-- Equation (2.3). -/
def poleFunctional (j : ℕ) : ℚ[X] :=
  C ((j : ℚ)^4) * (X-C (harmonic5 j)) - C (1/4) + C (1/(2*(j : ℚ)))

/-- The constant term of equation (2.3). -/
def poleConstant (j : ℕ) : ℚ :=
  -(j : ℚ)^4 * harmonic5 j - 1/4 + 1/(2*(j : ℚ))

/-- The coefficient multiplying j^(i+j) in the matrix's X coefficient. -/
def weight (N : ℕ) {h : ℕ} (i : Fin h) : ℚ :=
  ((poleIndex N i : ℕ) : ℚ)^4 * (denominator N).eval (node N i)^5 /
    poleDenominator N i

/-- The rational coefficient of X in the Hankel matrix. -/
def coefficientMatrix (N h : ℕ) : Matrix (Fin h) (Fin h) ℚ :=
  fun i j => ∑ k : Fin h, weight N k * node N k ^ (i.val+j.val)

/-- The rational constant coefficient of the Hankel matrix. -/
def constantMatrix (N h : ℕ) : Matrix (Fin h) (Fin h) ℚ :=
  fun i j => quotientMoment N h (i.val+j.val) +
    ∑ k : Fin h, residue N (i.val+j.val) k * poleConstant (poleIndex N k)

/-- G_K(X), in affine normal form. -/
def hankelMatrix (N h : ℕ) : Matrix (Fin h) (Fin h) ℚ[X] :=
  (X : ℚ[X]) • (coefficientMatrix N h).map C + (constantMatrix N h).map C

/-- Δ_K(X). -/
def determinant (N h : ℕ) : ℚ[X] := (hankelMatrix N h).det

lemma poleIndex_pos (N : ℕ) {h : ℕ} (i : Fin h) : 0 < poleIndex N i := by
  simp only [poleIndex]
  omega

lemma node_injective (N h : ℕ) : Function.Injective (node N : Fin h → ℚ) := by
  intro i j hij
  have hi : (0 : ℚ) < poleIndex N i := by exact_mod_cast poleIndex_pos N i
  have hj : (0 : ℚ) < poleIndex N j := by exact_mod_cast poleIndex_pos N j
  have hp : (poleIndex N i : ℚ) = poleIndex N j := by
    dsimp [node] at hij
    nlinarith
  have hp' : poleIndex N i = poleIndex N j := by exact_mod_cast hp
  apply Fin.ext
  dsimp [poleIndex] at hp'
  omega

lemma poleDenominator_ne_zero (N : ℕ) {h : ℕ} (i : Fin h) :
    poleDenominator N i ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  apply sub_ne_zero.mpr
  intro eq
  have hik := node_injective N h eq
  exact (Finset.mem_erase.mp hk).1 hik.symm

lemma denominator_eval_node_ne_zero (N : ℕ) {h : ℕ} (i : Fin h) :
    (denominator N).eval (node N i) ≠ 0 := by
  simp only [denominator, eval_prod, eval_add, eval_X, eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  have hkn : k < N := Finset.mem_range.mp hk
  have hlt : ((k+1 : ℕ) : ℚ) < poleIndex N i := by
    exact_mod_cast (show k+1 < poleIndex N i by dsimp [poleIndex]; omega)
  have hkpos : (0 : ℚ) < ((k+1 : ℕ) : ℚ) := by positivity
  dsimp [node]
  nlinarith

lemma weight_ne_zero (N : ℕ) {h : ℕ} (i : Fin h) : weight N i ≠ 0 := by
  apply div_ne_zero
  · apply mul_ne_zero
    · apply pow_ne_zero
      exact_mod_cast (ne_of_gt (poleIndex_pos N i))
    · exact pow_ne_zero _ (denominator_eval_node_ne_zero N i)
  · exact poleDenominator_ne_zero N i

/-- The residue formula factors into a common weight and a power of the node. -/
lemma residue_mul_fourth (N e : ℕ) {h : ℕ} (k : Fin h) :
    residue N e k * (poleIndex N k : ℚ)^4 = weight N k * node N k ^ e := by
  simp only [residue, numerator, eval_mul, eval_pow, eval_X, weight]
  ring

/-- The displayed pole functional is affine with the advertised coefficients. -/
lemma poleFunctional_affine (j : ℕ) :
    poleFunctional j = X*C ((j : ℚ)^4) + C (poleConstant j) := by
  simp only [poleFunctional, poleConstant, map_add, map_sub, map_neg, map_mul]
  ring

/-- Each entry is exactly the polynomial quotient contribution plus the
simple-pole contributions prescribed by (2.2)--(2.4). -/
theorem hankelMatrix_entry (N h : ℕ) (i j : Fin h) :
    hankelMatrix N h i j = C (quotientMoment N h (i.val+j.val)) +
      ∑ k : Fin h, C (residue N (i.val+j.val) k) * poleFunctional (poleIndex N k) := by
  simp only [hankelMatrix, coefficientMatrix, constantMatrix, Matrix.add_apply,
    Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_add, map_sum,
    map_mul, poleFunctional_affine, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  have hs : ∑ k : Fin h, X * (C (weight N k) * C (node N k ^ (i.val+j.val))) =
      ∑ k : Fin h, C (residue N (i.val+j.val) k) *
        (X * C ((poleIndex N k : ℚ)^4)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hr := congrArg (C : ℚ → ℚ[X]) (residue_mul_fourth N (i.val+j.val) k)
    simp only [map_mul] at hr
    calc
      _ = X * (C (weight N k) * C (node N k ^ (i.val+j.val))) := rfl
      _ = X * (C (residue N (i.val+j.val) k) * C ((poleIndex N k : ℚ)^4)) := by rw [hr]
      _ = _ := by ring
  rw [hs]
  ring

/-- The Vandermonde factorization in Section 2.3. -/
theorem coefficientMatrix_factorization (N h : ℕ) :
    coefficientMatrix N h =
      (Matrix.vandermonde (node N : Fin h → ℚ))ᵀ *
      Matrix.diagonal (weight N) * Matrix.vandermonde (node N) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [coefficientMatrix, Matrix.mul_diagonal,
    Matrix.transpose_apply, Matrix.vandermonde_apply, pow_add]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The explicit tail denominator is exactly the uncancelled part of D_K. -/
theorem denominator_split (N h : ℕ) :
    denominator (N+h) = denominator N * tailDenominator N h := by
  unfold denominator
  rw [Finset.prod_range_add]
  congr 1
  simp only [tailDenominator, node, poleIndex, map_neg, sub_neg_eq_add]
  rw [← Fin.prod_univ_eq_prod_range (fun k : ℕ => (X : ℚ[X]) + C (((N+k+1 : ℕ) : ℚ)^2)) h]
  apply Finset.prod_congr rfl
  intro k hk
  congr 3
  norm_cast
  omega

/-- The product used in the residue formula really is D_tail' at its pole. -/
theorem tailDenominator_derivative_at_node (N : ℕ) {h : ℕ} (i : Fin h) :
    (tailDenominator N h).derivative.eval (node N i) = poleDenominator N i := by
  unfold tailDenominator
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [Polynomial.derivative_mul, Polynomial.derivative_sub,
    Polynomial.derivative_X, Polynomial.derivative_C, sub_zero,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_mul,
    Polynomial.eval_one, one_mul, add_zero, eval_prod, poleDenominator]

/-- Its determinant is the squared Vandermonde times the product of weights. -/
theorem coefficientMatrix_det (N h : ℕ) :
    (coefficientMatrix N h).det =
      (Matrix.vandermonde (node N : Fin h → ℚ)).det^2 * ∏ k : Fin h, weight N k := by
  rw [coefficientMatrix_factorization, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, Matrix.det_diagonal]
  ring

/-- Every actual weight and every actual node difference is nonzero. -/
theorem coefficientMatrix_det_ne_zero (N h : ℕ) :
    (coefficientMatrix N h).det ≠ 0 := by
  rw [coefficientMatrix_det]
  exact mul_ne_zero
    (pow_ne_zero _ (Matrix.det_vandermonde_ne_zero_iff.mpr (node_injective N h)))
    (Finset.prod_ne_zero_iff.mpr (fun k _ => weight_ne_zero N k))

/-- The top coefficient is the determinant of the coefficient matrix. -/
theorem determinant_coeff_h (N h : ℕ) :
    (determinant N h).coeff h = (coefficientMatrix N h).det := by
  simpa only [determinant, hankelMatrix, Fintype.card_fin] using
    (Polynomial.coeff_det_X_add_C_card (coefficientMatrix N h) (constantMatrix N h))

/-- Unconditional degree theorem for the explicitly constructed polynomials. -/
theorem determinant_natDegree (N h : ℕ) : (determinant N h).natDegree = h := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · simpa only [determinant, hankelMatrix, Fintype.card_fin] using
      (Polynomial.natDegree_det_X_add_C_le (coefficientMatrix N h) (constantMatrix N h))
  · rw [determinant_coeff_h]
    exact coefficientMatrix_det_ne_zero N h

/-- The paper's Δ_{40n} has degree 37n. -/
theorem paper_determinant_degree (n : ℕ) :
    (determinant (3*n) (37*n)).natDegree = 37*n := determinant_natDegree _ _

/-- Equation (2.5), with K=N+h. -/
def normalizingScalar (N h : ℕ) : ℚ :=
  (Nat.factorial (N+h) : ℚ)^(2*h) * 4^(h-1) /
    ((Nat.factorial N : ℚ)^(12*h) *
      ∏ i ∈ Finset.range (h-1), (Nat.factorial (2*(i+1)) : ℚ)^2)

lemma normalizingScalar_pos (N h : ℕ) : 0 < normalizingScalar N h := by
  unfold normalizingScalar
  apply div_pos
  · apply mul_pos
    · exact pow_pos (by exact_mod_cast Nat.factorial_pos (N+h)) _
    · positivity
  · apply mul_pos
    · exact pow_pos (by exact_mod_cast Nat.factorial_pos N) _
    · apply Finset.prod_pos
      intro i hi
      exact pow_pos (by exact_mod_cast Nat.factorial_pos (2*(i+1))) _

/-- The normalized F_K before the p-adic multiplier is applied. -/
def normalizedDeterminant (N h : ℕ) : ℚ[X] :=
  C (normalizingScalar N h) * determinant N h

/-- A nonzero rational normalization preserves the exact degree. -/
theorem scaled_determinant_degree (N h : ℕ) (s : ℚ) (hs : s ≠ 0) :
    (C s * determinant N h).natDegree = h := by
  rw [Polynomial.natDegree_C_mul hs, determinant_natDegree]

theorem normalizedDeterminant_degree (N h : ℕ) :
    (normalizedDeterminant N h).natDegree = h :=
  scaled_determinant_degree N h _ (ne_of_gt (normalizingScalar_pos N h))

/-- The positive weight in Proposition 2.2. Including the zero term does not
change the paper's sum over positive integers. -/
def integralWeight (y : ℝ) : ℝ :=
  (2*Real.pi)^4 * y^5 / 12 *
    ∑' l : ℕ, (l : ℝ)^4 * Real.exp (-(2*Real.pi*y) * l)

lemma integralWeight_summable {y : ℝ} (hy : 0 < y) :
    Summable (fun l : ℕ => (l : ℝ)^4 * Real.exp (-(2*Real.pi*y) * l)) :=
  Real.summable_pow_mul_exp_neg_nat_mul 4 (by positivity)

/-- The actual infinite series defining the paper's weight is strictly
positive throughout the integration interval; no assumed positivity. -/
theorem integralWeight_pos {y : ℝ} (hy : 0 < y) : 0 < integralWeight y := by
  unfold integralWeight
  apply mul_pos
  · positivity
  · apply (integralWeight_summable hy).tsum_pos
      (fun l => mul_nonneg (pow_nonneg (Nat.cast_nonneg l) _) (Real.exp_nonneg _)) 1
    simp only [Nat.cast_one, one_pow, one_mul]
    exact Real.exp_pos _

end Zeta5Construction
