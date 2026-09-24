import OuterMoments

/-! Linearity and exact cancellation for the paper's rational functional. -/
noncomputable section
open scoped BigOperators
open Polynomial Matrix

namespace Zeta5NumeratorFunctional
open Zeta5Construction Zeta5OuterMoments

variable {F : Type*} [Field F]

lemma add_div_monic (P Q D : F[X]) (hD : D.Monic) :
    (P+Q)/D = P/D+Q/D := by
  simp only [← divByMonic_eq_div _ hD]
  exact (div_modByMonic_unique (P /ₘ D + Q /ₘ D) (P %ₘ D + Q %ₘ D) hD
    ⟨by rw [mul_add, add_left_comm, add_assoc, modByMonic_add_div, ← add_assoc,
      add_comm (D * _), modByMonic_add_div],
      (degree_add_le _ _).trans_lt (max_lt (degree_modByMonic_lt _ hD)
        (degree_modByMonic_lt _ hD))⟩).1

lemma smul_div_monic (c : F) (P D : F[X]) (hD : D.Monic) :
    (c • P)/D = c • (P/D) := by
  simp only [← divByMonic_eq_div _ hD]
  exact (div_modByMonic_unique (c • (P /ₘ D)) (c • (P %ₘ D)) hD
    ⟨by rw [mul_smul_comm, ← smul_add, modByMonic_add_div],
      (degree_smul_le _ _).trans_lt (degree_modByMonic_lt _ hD)⟩).1

/-- Euclidean quotient by a fixed monic polynomial is linear. -/
def quotientLinearMap (D : F[X]) (hD : D.Monic) : F[X] →ₗ[F] F[X] where
  toFun P := P / D
  map_add' P Q := add_div_monic P Q D hD
  map_smul' c P := smul_div_monic c P D hD

/-- Multiplying numerator and denominator by a monic factor does not change
its polynomial quotient, even when a nonzero remainder is present. -/
lemma cancel_monic_quotient (E P D : F[X]) (hE : E.Monic) (hD : D.Monic) :
    (E*P)/(E*D) = P/D := by
  rw [← divByMonic_eq_div _ (hE.mul hD), ← divByMonic_eq_div _ hD]
  apply (div_modByMonic_unique (P /ₘ D) (E * (P %ₘ D)) (hE.mul hD) ?_).1
  constructor
  · rw [mul_assoc, ← mul_add, modByMonic_add_div]
  · rw [Polynomial.degree_mul, Polynomial.degree_mul]
    exact WithBot.add_lt_add_left (Polynomial.degree_ne_bot.mpr hE.ne_zero) (degree_modByMonic_lt P hD)

/-- The full fixed-denominator functional, with an arbitrary polynomial-part
functional. Its pole values are exactly the paper's affine values. -/
def numeratorFunctional (N h : ℕ) (μ : ℚ[X] →ₗ[ℚ] ℚ) : ℚ[X] →ₗ[ℚ] ℚ[X] where
  toFun P := C (μ (P / tailDenominator N h)) +
    ∑ k : Fin h, C (P.eval (node N k) / poleDenominator N k) * poleFunctional (poleIndex N k)
  map_add' P Q := by
    simp only [add_div_monic _ _ _ (construction_tail_monic N h), map_add, eval_add,
      add_div, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' c P := by
    simp only [smul_div_monic _ _ _ (construction_tail_monic N h), map_smul,
      eval_smul, smul_eq_mul, mul_div_assoc, map_mul]
    simp only [smul_add, Finset.smul_sum, smul_eq_C_mul, RingHom.id_apply]
    ring

lemma numeratorFunctional_apply (N h : ℕ) (μ : ℚ[X] →ₗ[ℚ] ℚ) (P : ℚ[X]) :
    numeratorFunctional N h μ P = C (μ (P / tailDenominator N h)) +
      ∑ k : Fin h, C (P.eval (node N k) / poleDenominator N k) * poleFunctional (poleIndex N k) := rfl

/-- The actual Hankel entries are values of this linear functional. -/
theorem hankelMatrix_as_functional (N h : ℕ) (i j : Fin h) :
    hankelMatrix N h i j = numeratorFunctional N h polynomialFunctional
      (denominator N ^ 5 * (X^i.val * X^j.val)) := by
  rw [hankelMatrix_entry, numeratorFunctional_apply, ← pow_add]
  rfl

lemma tail_eval_node (N h : ℕ) (k : Fin h) : (tailDenominator N h).eval (node N k) = 0 := by
  simp only [tailDenominator, eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  simp

/-- When the complete denominator cancels, the original pole terms vanish. -/
theorem numeratorFunctional_cancel_all (N h : ℕ) (μ : ℚ[X] →ₗ[ℚ] ℚ) (P : ℚ[X]) :
    numeratorFunctional N h μ (tailDenominator N h * P) = C (μ P) := by
  rw [numeratorFunctional_apply,
    ← EuclideanDomain.eq_div_of_mul_eq_right (construction_tail_monic N h).ne_zero rfl]
  simp only [eval_mul, tail_eval_node, zero_mul, zero_div, map_zero,
    Finset.sum_const_zero, add_zero]

/-- The modified moment sequence is itself a genuine rational linear map. -/
def correctedMomentLinearMap (p : ℕ) : ℚ[X] →ₗ[ℚ] ℚ :=
  Polynomial.lsum fun e => correctedMoment p e • LinearMap.id

lemma correctedMomentLinearMap_apply (p : ℕ) (P : ℚ[X]) :
    correctedMomentLinearMap p P = correctedPolynomialMoment p P := by
  change (∑ e ∈ P.support, correctedMoment p e * P.coeff e) =
    ∑ e ∈ P.support, P.coeff e * correctedMoment p e
  simp only [mul_comm]

/-- The corrected source matrix uses the same linear functional and pole values. -/
theorem actualCorrectedHankel_as_functional (N h p : ℕ) (i j : Fin h) :
    actualCorrectedHankel N h p i j = numeratorFunctional N h (correctedMomentLinearMap p)
      (denominator N ^ 5 * (X^i.val * X^j.val)) := by
  rw [numeratorFunctional_apply, ← pow_add, correctedMomentLinearMap_apply]
  change _ = C (correctedPolynomialMoment p (numerator N (i.val+j.val) / tailDenominator N h)) +
    ∑ k : Fin h, C (residue N (i.val+j.val) k) * poleFunctional (poleIndex N k)
  simp only [actualCorrectedHankel, actualCorrectedConstantMatrix,
    coefficientMatrix, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
    smul_eq_mul, map_add, map_sum, map_mul, poleFunctional_affine, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  have hs : ∑ k : Fin h, X * (C (weight N k) * C (node N k ^ (i.val+j.val))) =
      ∑ k : Fin h, C (residue N (i.val+j.val) k) *
        (X * C ((poleIndex N k : ℚ)^4)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hr := congrArg (C : ℚ → ℚ[X]) (residue_mul_fourth N (i.val+j.val) k)
    simp only [map_mul] at hr
    rw [← hr]
    ring
  rw [hs]
  ring

#print axioms numeratorFunctional
#print axioms hankelMatrix_as_functional
#print axioms numeratorFunctional_cancel_all
#print axioms actualCorrectedHankel_as_functional
end Zeta5NumeratorFunctional
