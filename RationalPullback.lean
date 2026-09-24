import ConstructionPullback
import LocalFunctional
import RationalDistribution
import NumeratorFunctional

namespace Zeta5Local
open Polynomial

noncomputable def polePullbackPolynomial (j : ℕ) : ℚ[X] :=
  -X ^ 3 - C ((j : ℚ)^2) * X

lemma tau_polePullbackPolynomial (j : ℕ) :
    rationalTauFunctional (polePullbackPolynomial j) = -(1/4 : ℚ) := by
  have h1 : rationalTauFunctional (X : ℚ[X]) = 0 := by
    simpa [rationalTauMoment] using rationalTauFunctional_X_pow 1
  rw [polePullbackPolynomial, map_sub, map_neg, rationalTauFunctional_X_pow,
    ← smul_eq_C_mul, map_smul, h1]
  norm_num [rationalTauMoment]

lemma construction_harmonic_eq (n : ℕ) : Zeta5Construction.harmonic5 n = harmonic5 n := by
  simp [Zeta5Construction.harmonic5, harmonic5, Nat.cast_add, Nat.cast_one]

/-- Equation3.1 for each actual simple pole of μ, including its constant
term. Both signed integer poles of τ occur after t=-x². -/
theorem construction_pole_pullback (j : ℕ) (hj : 0 < j) :
    Zeta5Construction.poleFunctional j =
      C (rationalTauFunctional (polePullbackPolynomial j)) +
      C (-((j : ℚ)^4)/2) * (poleValue (j : ℤ) + poleValue (-(j : ℤ))) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  have hh := pole_pullback_value n
  rw [Zeta5Construction.poleFunctional, construction_harmonic_eq,
    tau_polePullbackPolynomial]
  push_cast at hh ⊢
  simp only [neg_div, map_neg]
  linear_combination -hh

noncomputable def rationalPullbackPolynomial {ι : Type*} (Q : ℚ[X])
    (s : Finset ι) (j : ι → ℕ) (a : ι → ℚ) : ℚ[X] :=
  X ^ 5 * Q.comp (-(X ^ 2)) + ∑ i ∈ s, C (a i) * polePullbackPolynomial (j i)

/-- Full exact pullback for any finite μ partial-fraction presentation.
This keeps its polynomial quotient and all original residues. -/
theorem rationalPresentation_pullback {ι : Type*} (Q : ℚ[X])
    (s : Finset ι) (j : ι → ℕ) (a : ι → ℚ) (hj : ∀ i ∈ s, 0 < j i) :
    C (Zeta5Construction.polynomialFunctional Q) +
      ∑ i ∈ s, C (a i) * Zeta5Construction.poleFunctional (j i) =
      C (rationalTauFunctional (rationalPullbackPolynomial Q s j a)) +
        ∑ i ∈ s, C (a i * (-((j i : ℚ)^4)/2)) *
          (poleValue (j i : ℤ) + poleValue (-(j i : ℤ))) := by
  rw [rationalPullbackPolynomial, map_add, map_sum,
    ← Zeta5Construction.polynomialFunctional_pullback]
  simp_rw [← smul_eq_C_mul, map_smul, smul_eq_mul]
  rw [map_add, map_sum]
  simp_rw [map_mul]
  simp only [smul_eq_C_mul]
  have he : (∑ i ∈ s, C (a i) * Zeta5Construction.poleFunctional (j i)) =
      ∑ i ∈ s, C (a i) *
        (C (rationalTauFunctional (polePullbackPolynomial (j i))) +
          C (-((j i : ℚ)^4)/2) * (poleValue (j i : ℤ) + poleValue (-(j i : ℤ)))) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [construction_pole_pullback _ (hj i hi)]
  rw [he]
  simp only [mul_add, Finset.sum_add_distrib, map_mul, mul_assoc]
  ring

/-- The actual fixed-denominator μ numerator functional therefore has an
exact τ presentation on signed integer poles. -/
theorem numeratorFunctional_pullback (N h : ℕ) (A : ℚ[X]) :
    Zeta5NumeratorFunctional.numeratorFunctional N h Zeta5Construction.polynomialFunctional A =
      C (rationalTauFunctional
        (rationalPullbackPolynomial (A / Zeta5Construction.tailDenominator N h)
          Finset.univ (Zeta5Construction.poleIndex N)
          (fun i : Fin h => A.eval (Zeta5Construction.node N i) /
            Zeta5Construction.poleDenominator N i))) +
      ∑ i : Fin h, C ((A.eval (Zeta5Construction.node N i) /
          Zeta5Construction.poleDenominator N i) *
          (-((Zeta5Construction.poleIndex N i : ℚ)^4)/2)) *
        (poleValue (Zeta5Construction.poleIndex N i : ℤ) +
          poleValue (-(Zeta5Construction.poleIndex N i : ℤ))) := by
  rw [Zeta5NumeratorFunctional.numeratorFunctional_apply]
  exact rationalPresentation_pullback _ _ _ _ (fun i hi => by
    simp only [Zeta5Construction.poleIndex]
    omega)

#print axioms numeratorFunctional_pullback
end Zeta5Local
