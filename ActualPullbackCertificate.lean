import PresentationCertificates
import ActualRationalDistribution

namespace Zeta5Local
open Polynomial Zeta5Construction

noncomputable def actualTailCofactor (N h : ℕ) (i : Fin h) : ℚ[X] :=
  Lagrange.nodal (Finset.univ.erase i) (node N)

lemma actualTail_factor (N h : ℕ) (i : Fin h) :
    tailDenominator N h = (X+C ((Zeta5Construction.poleIndex N i : ℚ)^2))*actualTailCofactor N h i := by
  have he := Lagrange.nodal_eq_mul_nodal_erase (s := Finset.univ)
    (v := node N) (Finset.mem_univ i)
  simpa only [Lagrange.nodal, tailDenominator, actualTailCofactor, node, map_neg,
    sub_neg_eq_add] using he

lemma actual_mu_polynomial_identity (N h : ℕ) (A : ℚ[X]) :
    A = tailDenominator N h * (A / tailDenominator N h) +
      ∑ i : Fin h, C (A.eval (node N i) / Zeta5Construction.poleDenominator N i)*actualTailCofactor N h i := by
  exact partial_fraction_polynomial_identity A Finset.univ (node N)
    (node_injective N h).injOn

noncomputable def actualSignedRoot (N : ℕ) {h : ℕ} (ib : Fin h × Bool) : ℚ :=
  if ib.2 = true then -(Zeta5Construction.poleIndex N ib.1 : ℚ)
  else (Zeta5Construction.poleIndex N ib.1 : ℚ)

noncomputable def actualSignedCofactor (N h : ℕ) (ib : Fin h × Bool) : ℚ[X] :=
  if ib.2 = true then
    -(X-C (Zeta5Construction.poleIndex N ib.1 : ℚ)) * (actualTailCofactor N h ib.1).comp (-(X^2))
  else
    -(X+C (Zeta5Construction.poleIndex N ib.1 : ℚ)) * (actualTailCofactor N h ib.1).comp (-(X^2))

lemma actualSigned_factor (N h : ℕ) (ib : Fin h × Bool) :
    (tailDenominator N h).comp (-(X^2)) =
      (X-C (actualSignedRoot N ib))*actualSignedCofactor N h ib := by
  have he := presentation_quadratic_factor _ _ (Zeta5Construction.poleIndex N ib.1)
    (actualTail_factor N h ib.1)
  rcases ib with ⟨i,b⟩
  cases b
  · simpa only [actualSignedRoot, actualSignedCofactor, Bool.false_eq_true, if_false] using he.1
  · simpa only [actualSignedRoot, actualSignedCofactor, if_true, map_neg, sub_neg_eq_add] using he.2

/-- An exact cleared signed-pole certificate for the actual μ rational
numerator. Its polynomial quotient and residues are the same data appearing
in `numeratorFunctional_padic_distribution`. -/
theorem actualPullback_certificate (N h : ℕ) (A : ℚ[X]) :
    X^5*A.comp (-(X^2)) =
      (tailDenominator N h).comp (-(X^2))*actualPullbackPolynomial N h A +
      ∑ ib : Fin h × Bool, C (actualPullbackResidue N A ib.1)*actualSignedCofactor N h ib := by
  have he := presentation_quadratic_identity A (tailDenominator N h)
    (A / tailDenominator N h) Finset.univ (Zeta5Construction.poleIndex N)
    (fun i : Fin h => A.eval (node N i)/Zeta5Construction.poleDenominator N i)
    (actualTailCofactor N h) (fun i hi => actualTail_factor N h i)
    (actual_mu_polynomial_identity N h A)
  simpa only [actualPullbackPolynomial, actualPullbackResidue, Fintype.sum_prod_type,
    Fintype.sum_bool, actualSignedCofactor, Bool.false_eq_true, if_false, if_true,
    ← mul_add, add_comm] using he

#print axioms actualPullback_certificate
end Zeta5Local
