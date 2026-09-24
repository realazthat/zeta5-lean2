import SmallPrimeRootEquiv
import SmallPrimeActual
import CanonicalPresentation
import SmallPrimeDeterminant

set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Polynomial
open scoped BigOperators
namespace Zeta5Local
open Zeta5Construction Zeta5NumeratorFunctional Zeta5SmallPrimeDeterminant

lemma actualSignedRoot_zero_injective (K : ℕ) :
    Function.Injective (actualSignedRoot 0 : Fin K×Bool → ℚ) := by
  intro i j hij
  apply (smallPrimeRootEquiv K).injective
  apply Subtype.ext
  rw [←smallPrimeRootEquiv_root K i,←smallPrimeRootEquiv_root K j] at hij
  dsimp [smallPrimeRoot] at hij
  have h : ((smallPrimeRootEquiv K i).val : ℚ)=(smallPrimeRootEquiv K j).val := by linarith
  exact_mod_cast h

lemma fullPullback_value (N h : ℕ) (A : ℚ[X]) :
    numeratorFunctional N h polynomialFunctional A =
      C (rationalTauFunctional (actualPullbackPolynomial N h A)) +
      ∑ ib : Fin (N+h)×Bool, C (fullPullbackResidue N h A ib.1)*
        poleValue (actualSignedIntegerRoot 0 ib) := by
  have hidx (i : Fin h) : Zeta5Construction.poleIndex 0 (Fin.natAdd N i)=
      Zeta5Construction.poleIndex N i := by simp only [Zeta5Construction.poleIndex,Fin.val_natAdd]; omega
  rw [fullPullback_residue_sum N h A (fun c ib => C c*poleValue (actualSignedIntegerRoot 0 ib))
    (by intro ib; simp)]
  simp only [fullSignedIntegerRoot_tail,Fintype.sum_prod_type,Fintype.sum_bool,
    actualSignedIntegerRoot,Bool.false_eq_true,if_false,if_true,hidx]
  rw [numeratorFunctional_pullback]
  simp only [actualPullbackPolynomial,actualPullbackResidue,mul_add,Finset.sum_add_distrib]
  ring

/-- Pullback numerator with the sign needed for the monic signed-root denominator. -/
def fullSmallPrimeNumerator (N h : ℕ) (A : ℚ[X]) : ℚ[X] :=
  C ((-1:ℚ)^(N+h))*X^5*(denominator N*A).comp (-(X^2))

lemma smallPrime_full_presentation (N h : ℕ) (A : ℚ[X]) :
    smallPrimeQuotient (N+h) (fullSmallPrimeNumerator N h A) =
        C (((N+h).factorial:ℚ)^2)*actualPullbackPolynomial N h A ∧
    ∀ ib : Fin (N+h)×Bool,
      smallPrimeResidue (N+h) (fullSmallPrimeNumerator N h A)
        (smallPrimeRootEquiv (N+h) ib).val =
      ((N+h).factorial:ℚ)^2*fullPullbackResidue N h A ib.1 := by
  let k : ℚ := ((N+h).factorial:ℚ)^2
  let z : ℚ := (-1:ℚ)^(N+h)
  let U := fullSmallPrimeNumerator N h A
  have hf (ib : Fin (N+h)×Bool) (_ : ib∈Finset.univ) :
      Lagrange.nodal Finset.univ (actualSignedRoot 0 (h:=N+h)) =
        (X-C (actualSignedRoot 0 ib))*(C z*actualSignedCofactor 0 (N+h) ib) := by
    rw [actualSignedRoot_nodal (N+h),fullPullback_factor N h ib]
    dsimp [z]
    ring
  have he : C k*U = Lagrange.nodal Finset.univ (actualSignedRoot 0 (h:=N+h))*
      (C k*actualPullbackPolynomial N h A)+
      ∑ ib : Fin (N+h)×Bool, C (k*fullPullbackResidue N h A ib.1)*
        (C z*actualSignedCofactor 0 (N+h) ib) := by
    dsimp [U,fullSmallPrimeNumerator]
    rw [mul_assoc (C z) (X^5),fullPullback_certificate N h A]
    rw [actualSignedRoot_nodal (N+h)]
    simp only [mul_add,Finset.mul_sum,map_mul]
    congr 1
    · dsimp [z]; ring
    · apply Finset.sum_congr rfl
      intro ib _
      dsimp [z]; ring
  have hu := canonical_presentation_unique (C k*U) (C k*actualPullbackPolynomial N h A)
    Finset.univ (actualSignedRoot 0 (h:=N+h))
    (fun ib : Fin (N+h)×Bool => k*fullPullbackResidue N h A ib.1)
    (fun ib => C z*actualSignedCofactor 0 (N+h) ib)
    (actualSignedRoot_injective (N+h)).injOn hf he
  constructor
  · simpa only [smallPrimeQuotient,actualSignedRoot_nodal,smallPrimeRoot_nodal] using hu.1.symm
  · intro ib
    have hr := hu.2 ib (Finset.mem_univ ib)
    rw [←Lagrange.eval_nodal,actualSignedRoot_nodal_cofactor] at hr
    simpa only [smallPrimeResidue,←Lagrange.eval_nodal,smallPrimeRoot_nodal_cofactor,
      smallPrimeRootEquiv_root,eval_mul,eval_C] using hr.symm

/-- Exact equality of the small-prime canonical τ polynomial with the actual μ functional. -/
theorem smallPrimeTauPolynomial_full_pullback (N h : ℕ) (A : ℚ[X]) :
    smallPrimeTauPolynomial (N+h) (fullSmallPrimeNumerator N h A) =
      C (((N+h).factorial:ℚ)^2)*numeratorFunctional N h polynomialFunctional A := by
  have hu := smallPrime_full_presentation N h A
  rw [smallPrimeTauPolynomial,hu.1,←smul_eq_C_mul,map_smul]
  simp only [smul_eq_mul,map_mul]
  rw [smallPrimeRootEquiv_sum]
  simp only [hu.2,smallPrimeRootEquiv_integer,map_mul]
  rw [fullPullback_value,mul_add,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro ib _
  ring

#print axioms fullPullback_value
#print axioms smallPrimeTauPolynomial_full_pullback
end Zeta5Local
