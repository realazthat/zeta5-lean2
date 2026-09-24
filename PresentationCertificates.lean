import PartialFractions
import RationalPullback

namespace Zeta5Local
open Polynomial

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]

/-- The exact cleared polynomial identity for finite partial fractions. -/
theorem partial_fraction_polynomial_identity (A : F[X]) (s : Finset ι) (r : ι → F)
    (hinj : Set.InjOn r s) :
    A = Lagrange.nodal s r * (A / Lagrange.nodal s r) +
      ∑ i ∈ s, C (A.eval (r i) / ∏ k ∈ s.erase i, (r i-r k)) * Lagrange.nodal (s.erase i) r := by
  have he := modByMonic_add_div A (Lagrange.nodal s r)
  rw [remainder_eq_interpolate A s r hinj,
    divByMonic_eq_div A (Lagrange.nodal_monic (s := s) (v := r)),
    Lagrange.interpolate_eq_nodalWeight_mul_nodal_div_X_sub_C] at he
  have hsum : (∑ i ∈ s, C (Lagrange.nodalWeight s r i) *
      (Lagrange.nodal s r / (X-C (r i))) * C (A.eval (r i))) =
      ∑ i ∈ s, C (A.eval (r i) / ∏ k ∈ s.erase i, (r i-r k)) * Lagrange.nodal (s.erase i) r := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Lagrange.nodal_erase_eq_nodal_div hi]
    simp only [Lagrange.nodalWeight, Finset.prod_inv_distrib, div_eq_mul_inv, map_mul]
    ring
  rw [hsum] at he
  linear_combination -he

/-- Exact affine substitution of a cleared simple-pole presentation. -/
theorem presentation_affine_identity (A D P : F[X]) (s : Finset ι)
    (c : ι → F) (Di : ι → F[X]) (a b : F) (hb : b ≠ 0)
    (he : A = D*P + ∑ i ∈ s, C (c i)*Di i) :
    A.comp (C a+C b*X) = D.comp (C a+C b*X)*P.comp (C a+C b*X) +
      ∑ i ∈ s, C (c i/b)*(C b*(Di i).comp (C a+C b*X)) := by
  rw [he, add_comp, mul_comp, sum_comp]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_comp, C_comp, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ hb]

/-- The pole and its cofactor transform together, retaining the factor b
that is required in each transformed residue. -/
theorem presentation_affine_factor (D E : F[X]) (r a b : F) (hb : b ≠ 0)
    (he : D = (X-C r)*E) :
    D.comp (C a+C b*X) = (X-C ((r-a)/b))*(C b*E.comp (C a+C b*X)) := by
  rw [he, mul_comp, sub_comp, X_comp, C_comp]
  have hc : C ((r-a)/b)*C b = (C r-C a : F[X]) := by
    rw [← map_mul, div_mul_cancel₀ _ hb, map_sub]
  linear_combination (E.comp (C a+C b*X))*hc

/-- The polynomial numerator identity underlying the two signed poles of
an individual μ pole after the quadratic pullback. -/
lemma polePullback_polynomial_identity (j : ℕ) :
    (X : ℚ[X])^5 = (C ((j : ℚ)^2)-X^2)*polePullbackPolynomial j +
      C (-((j : ℚ)^4)/2)* (-(X+C (j : ℚ))-(X-C (j : ℚ))) := by
  apply Polynomial.funext
  intro x
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_neg, eval_pow,
    polePullbackPolynomial]
  ring

/-- Cleared signed-pole factorization under t=-x². -/
theorem presentation_quadratic_factor (T Ti : ℚ[X]) (j : ℕ)
    (he : T = (X+C ((j : ℚ)^2))*Ti) :
    T.comp (-(X^2)) = (X-C (j : ℚ))*(-(X+C (j : ℚ))*Ti.comp (-(X^2))) ∧
    T.comp (-(X^2)) = (X+C (j : ℚ))*(-(X-C (j : ℚ))*Ti.comp (-(X^2))) := by
  rw [he, mul_comp, add_comp, X_comp, C_comp, map_pow]
  constructor <;> ring

/-- The full cleared rational identity after the μ-to-τ quadratic pullback.
This is an algebraic certificate, so it remains valid after arbitrary field
embeddings, affine substitution, and numerator/denominator rescaling. -/
theorem presentation_quadratic_identity (A T Q : ℚ[X]) (s : Finset ι)
    (j : ι → ℕ) (a : ι → ℚ) (Ti : ι → ℚ[X])
    (hT : ∀ i ∈ s, T = (X+C ((j i : ℚ)^2))*Ti i)
    (he : A = T*Q + ∑ i ∈ s, C (a i)*Ti i) :
    X^5*A.comp (-(X^2)) = T.comp (-(X^2))*rationalPullbackPolynomial Q s j a +
      ∑ i ∈ s, C (a i*(-((j i : ℚ)^4)/2)) *
        (-(X+C (j i : ℚ))*(Ti i).comp (-(X^2)) +
          -(X-C (j i : ℚ))*(Ti i).comp (-(X^2))) := by
  have hterm (i : ι) (hi : i ∈ s) :
      X^5*(C (a i)*(Ti i).comp (-(X^2))) =
      T.comp (-(X^2))*(C (a i)*polePullbackPolynomial (j i)) +
      C (a i*(-((j i : ℚ)^4)/2)) *
        (-(X+C (j i : ℚ))*(Ti i).comp (-(X^2)) +
          -(X-C (j i : ℚ))*(Ti i).comp (-(X^2))) := by
    rw [hT i hi, mul_comp, add_comp, X_comp, C_comp, map_mul]
    linear_combination (C (a i)*(Ti i).comp (-(X^2))) * polePullback_polynomial_identity (j i)
  rw [he, add_comp, mul_comp, sum_comp, mul_add, Finset.mul_sum]
  simp_rw [mul_comp, C_comp]
  rw [rationalPullbackPolynomial, mul_add, Finset.mul_sum]
  have hs := Finset.sum_congr rfl hterm
  rw [Finset.sum_add_distrib] at hs
  linear_combination hs

#print axioms presentation_quadratic_identity
#print axioms presentation_affine_identity
end Zeta5Local
