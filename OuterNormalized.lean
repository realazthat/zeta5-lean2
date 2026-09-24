import OuterWeightAggregation
import PaperParameters
import ScalarValuation

/-! Actual outer-prime endpoints for the normalized source determinant. -/
noncomputable section
open scoped BigOperators
open Polynomial
namespace Zeta5OuterNormalized
open Zeta5Construction Zeta5Outer Zeta5OuterDeterminant Zeta5OuterLargePrimes
open Zeta5OuterWeightAggregation Zeta5Parameters

lemma prime_half_decomposition (p : ℕ) [Fact p.Prime] (hp3 : 3 ≤ p) :
    p = 2*((p-1)/2)+1 := by
  have hodd := (Fact.out : p.Prime).eq_two_or_odd.resolve_left (by omega)
  omega

lemma paper_outer_geometry (n p : ℕ) (hn : 0<n) (houter : K n < 3*p) :
    7≤p ∧ 2*N n<p ∧ 2*(N n+h n)<p^2 ∧ N n+h n=K n := by
  dsimp [K,N,h] at *
  have hp7 : 7≤p := by omega
  have hs : 3*n+37*n=40*n := by omega
  refine ⟨hp7,by omega,?_,hs⟩
  nlinarith

/-- The full corrected outer bound for the actual source determinant,
including primes beyond K. No local valuation hypotheses remain. -/
theorem actual_coarseOuterExponent_bound (n p : ℕ) [Fact p.Prime]
    (hn : 0<n) (houter : K n<3*p) (k : ℕ)
    (hk : (determinant (N n) (h n)).coeff k ≠ 0) :
    coarseOuterExponent n p ≤ padicValRat p ((determinant (N n) (h n)).coeff k) := by
  obtain ⟨hp7,hNp,hK2,hsize⟩ := paper_outer_geometry n p hn houter
  have hp := prime_half_decomposition p (by omega)
  by_cases hlarge : K n<p
  · rw [coarseOuterExponent, if_pos hlarge]
    apply actual_large_prime_determinant_bound p ((p-1)/2) (N n) (h n) hp hp7
      (by omega) _ k hk
    dsimp [N,h,K] at *
    omega
  · have hKp : p≤N n+h n := by omega
    have hK3 : N n+h n<3*p := by omega
    have hh := actual_outer_determinant_bound p ((p-1)/2) (N n) (h n)
      hp hp7 hK3 hK2 hNp hKp k hk
    have he : (coarseOuterExponent n p : ℚ) =
        2*(∑ i : RowIndex p ((p-1)/2) (N n) (h n) hp,
          rowWeight p ((p-1)/2) (N n) (h n) hp i)-
          (((N n+h n)+4*N n+2-2*p : ℕ) : ℚ) := by
      rw [rowWeight_sum p ((p-1)/2) (N n) (h n) hp hNp hKp hK3, hsize]
      unfold coarseOuterExponent removedExtraCount overlap correctionRank
      rw [if_neg hlarge]
      by_cases htwo : K n<2*p
      · rw [if_pos htwo, if_pos htwo]
        simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg, Int.cast_natCast, Int.cast_ofNat, Nat.cast_add]
        ring
      · rw [if_neg htwo, if_neg htwo]
        simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg, Int.cast_natCast, Int.cast_ofNat, Nat.cast_add]
        ring
    rw [← he] at hh
    exact_mod_cast hh

lemma determinant_coeff_ne_zero_of_normalized (N h k : ℕ)
    (hk : (normalizedDeterminant N h).coeff k ≠ 0) : (determinant N h).coeff k ≠ 0 := by
  intro hz
  apply hk
  rw [normalizedDeterminant, coeff_C_mul, hz, mul_zero]

lemma normalizedDeterminant_coeff_valuation (p N h k : ℕ) [Fact p.Prime]
    (hk : (normalizedDeterminant N h).coeff k ≠ 0) :
    padicValRat p ((normalizedDeterminant N h).coeff k) =
      padicValRat p (normalizingScalar N h)+padicValRat p ((determinant N h).coeff k) := by
  rw [normalizedDeterminant, coeff_C_mul]
  exact padicValRat.mul (ne_of_gt (normalizingScalar_pos N h))
    (determinant_coeff_ne_zero_of_normalized N h k hk)

/-- Outer estimates after the actual rational prefactor S_K. -/
theorem actual_normalized_outer_bound (n p : ℕ) [Fact p.Prime]
    (hn : 0<n) (houter : K n<3*p) (k : ℕ)
    (hk : (normalizedDeterminant (N n) (h n)).coeff k ≠ 0) :
    padicValRat p (normalizingScalar (N n) (h n))+coarseOuterExponent n p ≤
      padicValRat p ((normalizedDeterminant (N n) (h n)).coeff k) := by
  rw [normalizedDeterminant_coeff_valuation p _ _ _ hk]
  exact add_le_add (le_refl _) (actual_coarseOuterExponent_bound n p hn houter k
    (determinant_coeff_ne_zero_of_normalized _ _ _ hk))

/-- The actual localExponent branch needed by the normalizer, for every outer prime. -/
theorem actual_outer_localExponent_bound (n M p : ℕ) [Fact p.Prime]
    (ha : Admissible n M) (hsmall : K n<p*M) (houter : K n<3*p) (k : ℕ)
    (hk : (normalizedDeterminant (N n) (h n)).coeff k ≠ 0) :
    localExponent n M p ≤ padicValRat p ((normalizedDeterminant (N n) (h n)).coeff k) := by
  have hn : 0<n := by
    obtain ⟨hM,hN⟩ := ha
    dsimp [K] at hN
    nlinarith
  rw [localExponent, if_neg (by omega), if_neg (by omega)]
  exact actual_normalized_outer_bound n p hn houter k hk

#print axioms actual_coarseOuterExponent_bound
#print axioms actual_outer_localExponent_bound
lemma prime_outside_normalization_large (n p : ℕ) [Fact p.Prime]
    (houtside : p ∉ normalizationPrimes n) : 2*h n<p := by
  by_contra hle
  apply houtside
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_range.mpr (by omega), Fact.out⟩

lemma normalizingScalar_valuation_zero_outside (n M p : ℕ) [Fact p.Prime]
    (ha : Admissible n M) (houtside : p ∉ normalizationPrimes n) :
    padicValRat p (normalizingScalar (N n) (h n)) = 0 := by
  have hpbig := prime_outside_normalization_large n p houtside
  have hM := ha.1
  have hKp : K n<p := by dsimp [K,h] at *; omega
  have hNp : N n<p := by dsimp [N,K] at *; omega
  have hcutoff : K n≤M*p := by nlinarith
  rw [Zeta5InnerAsymptotics.actual_normalizingScalar_valuation n M p ha hcutoff,
    Nat.div_eq_of_lt hKp, Nat.div_eq_of_lt hNp]
  have hs : (∑ i ∈ Finset.range (h n-1), (((2*(i+1))/p : ℕ) : ℤ)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [Nat.div_eq_of_lt (by omega : 2*(i+1)<p)]
    rfl
  rw [hs]
  ring

/-- All primes absent from the finite normalizer already act integrally on
the actual normalized determinant. This discharges the outside-prime hypothesis
of `paperPolynomial_integer_of_local_bounds`. -/
theorem actual_outside_normalization_bound (n M p : ℕ) [Fact p.Prime]
    (ha : Admissible n M) (houtside : p ∉ normalizationPrimes n) (k : ℕ)
    (hk : (normalizedDeterminant (N n) (h n)).coeff k ≠ 0) :
    0 ≤ padicValRat p ((normalizedDeterminant (N n) (h n)).coeff k) := by
  have hpbig := prime_outside_normalization_large n p houtside
  have hKp : K n<p := by dsimp [K,h] at *; omega
  have hn : 0<n := by
    obtain ⟨hM,hN⟩ := ha
    dsimp [K] at hN
    nlinarith
  have hh := actual_normalized_outer_bound n p hn (by omega) k hk
  rw [normalizingScalar_valuation_zero_outside n M p ha houtside,
    coarseOuterExponent, if_pos hKp, add_zero] at hh
  exact hh

#print axioms actual_outside_normalization_bound
end Zeta5OuterNormalized
