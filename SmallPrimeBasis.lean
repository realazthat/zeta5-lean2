import SmallPrimeFunctional
import Construction

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5Local
open Polynomial
open scoped BigOperators

noncomputable def smallPrimeQ : ℕ → ℚ[X]
  | 0 => 1
  | n+1 => C ((-1:ℚ)^(n+1)*2/((2*(n+1)).factorial:ℚ)) * X *
      Zeta5Construction.denominator n

noncomputable def smallPrimeF (N i : ℕ) : ℚ[X] :=
  C (((N.factorial:ℚ)^6)⁻¹) * Zeta5Construction.denominator N^3 * smallPrimeQ i

@[simp] lemma smallPrimeQ_zero : smallPrimeQ 0 = 1 := rfl

lemma smallPrimeQ_scalar_ne_zero (n : ℕ) :
    (-1:ℚ)^(n+1)*2/((2*(n+1)).factorial:ℚ) ≠ 0 := by
  apply div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (by norm_num))
  exact_mod_cast Nat.factorial_ne_zero _

lemma smallPrimeDenominator_monic (N : ℕ) : (Zeta5Construction.denominator N).Monic := by
  unfold Zeta5Construction.denominator
  exact Polynomial.monic_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_add_C _)

lemma smallPrimeDenominator_natDegree (N : ℕ) : (Zeta5Construction.denominator N).natDegree = N := by
  unfold Zeta5Construction.denominator
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_add_C _)]
  simp only [Polynomial.natDegree_X_add_C, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rfl

lemma smallPrimeQ_natDegree (i : ℕ) : (smallPrimeQ i).natDegree = i := by
  cases i with
  | zero => simp
  | succ n =>
    simp only [smallPrimeQ]
    rw [mul_assoc, Polynomial.natDegree_C_mul (smallPrimeQ_scalar_ne_zero n),
      Polynomial.natDegree_X_mul, smallPrimeDenominator_natDegree]
    exact (smallPrimeDenominator_monic n).ne_zero

lemma smallPrimeQ_leadingCoeff (n : ℕ) :
    (smallPrimeQ (n+1)).leadingCoeff = (-1:ℚ)^(n+1)*2/((2*(n+1)).factorial:ℚ) := by
  simp only [smallPrimeQ, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
    Polynomial.leadingCoeff_X, (smallPrimeDenominator_monic n).leadingCoeff, mul_one]

lemma smallPrimeQ_leadingCoeff_zero : (smallPrimeQ 0).leadingCoeff = 1 := by simp

#print axioms smallPrimeQ_natDegree
#print axioms smallPrimeQ_leadingCoeff
end Zeta5Local
