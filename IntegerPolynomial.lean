import InnerNormalized
import SmallPrimeBound
import NormalizationLog

/-!
# Integer coefficients of the actual constructed polynomial

The three prime ranges and the primes outside the normalization support
are handled by unconditional local estimates proved in the imported modules.
-/

noncomputable section
open Polynomial Filter
namespace Zeta5Parameters
open Zeta5Construction

theorem actual_localExponent_bound (n M p : ℕ) [Fact p.Prime]
    (ha : Admissible n M) (k : ℕ)
    (hk : (normalizedDeterminant (N n) (h n)).coeff k≠0) :
    localExponent n M p≤padicValRat p ((normalizedDeterminant (N n) (h n)).coeff k) := by
  by_cases hsmall : p*M≤K n
  · have hn : 0<n := by
      obtain ⟨hM,hK⟩ := ha
      dsimp [K] at hK
      nlinarith
    exact Zeta5SmallPrimeDeterminant.actual_small_localExponent_bound n M p hn hsmall k hk
  · by_cases hinner : 3*p≤K n
    · exact Zeta5InnerNormalized.actual_inner_localExponent_bound n M p ha (by omega) hinner k hk
    · exact Zeta5OuterNormalized.actual_outer_localExponent_bound n M p ha (by omega) (by omega) k hk

/-- The rational polynomial defined from the paper's actual determinant and
prime normalizer is the image of an integer polynomial. -/
theorem paperPolynomial_integer (n M : ℕ) (ha : Admissible n M) :
    ∃ Q : ℤ[X], Q.map (Int.castRingHom ℚ)=paperPolynomial n M := by
  apply paperPolynomial_integer_of_local_bounds n M
  · intro p hp k hk
    letI : Fact p.Prime := ⟨normalizationPrimes_prime n p hp⟩
    exact actual_localExponent_bound n M p ha k hk
  · intro p hp houtside k hk
    letI : Fact p.Prime := ⟨hp⟩
    exact Zeta5OuterNormalized.actual_outside_normalization_bound n M p ha houtside k hk

theorem eventually_paperPolynomial_integer (M : ℕ) (hM : 40≤M) :
    ∀ᶠ n : ℕ in atTop, ∃ Q : ℤ[X], Q.map (Int.castRingHom ℚ)=paperPolynomial n M := by
  filter_upwards [eventually_admissible M hM] with n hn
  exact paperPolynomial_integer n M hn

#print axioms actual_localExponent_bound
#print axioms paperPolynomial_integer
#print axioms eventually_paperPolynomial_integer
end Zeta5Parameters
