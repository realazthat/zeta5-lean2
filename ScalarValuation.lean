import InnerErrorBound
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace Zeta5InnerAsymptotics
open Zeta5Parameters

theorem factorial_valuation_one_level (p A : ℕ) [hp : Fact p.Prime] (hA : A<p^2) :
    padicValNat p (Nat.factorial A) = A/p := by
  by_cases h0 : A=0
  · simp [h0]
  rw [padicValNat_factorial ((Nat.log_lt_iff_lt_pow hp.out.one_lt h0).mpr hA)]
  norm_num

theorem factorial_rat_valuation_one_level (p A : ℕ) [Fact p.Prime] (hA : A<p^2) :
    padicValRat p (Nat.factorial A:ℚ) = ((A/p:ℕ):ℤ) := by
  rw [← padicValRat_of_nat, factorial_valuation_one_level p A hA]

/-- Legendre's formula for the paper's exact normalizing scalar. -/
theorem normalizingScalar_valuation_one_level (N h p : ℕ) [hp : Fact p.Prime]
    (hp5 : 5≤p) (hsq : 2*(N+h)<p^2) :
    padicValRat p (Zeta5Construction.normalizingScalar N h) =
      2*(h:ℤ)*(((N+h)/p:ℕ):ℤ)-12*(h:ℤ)*((N/p:ℕ):ℤ)-
      2*∑ i ∈ Finset.range (h-1), (((2*(i+1))/p:ℕ):ℤ) := by
  have hf (A:ℕ) : (Nat.factorial A:ℚ)≠0 := by exact_mod_cast Nat.factorial_ne_zero A
  have hprod : (∏ i ∈ Finset.range (h-1), (Nat.factorial (2*(i+1)):ℚ)^2)≠0 :=
    Finset.prod_ne_zero_iff.mpr (fun i hi => pow_ne_zero _ (hf _))
  have h4 : padicValRat p (4:ℚ)=0 := by
    have hd : ¬p∣4 := Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
    have hv := padicValNat.eq_zero_of_not_dvd hd
    rw [← show ((4:ℕ):ℚ)=(4:ℚ) by norm_num,← padicValRat_of_nat,hv]
    rfl
  unfold Zeta5Construction.normalizingScalar
  rw [padicValRat.div (mul_ne_zero (pow_ne_zero _ (hf _)) (by positivity))
    (mul_ne_zero (pow_ne_zero _ (hf _)) hprod),
    padicValRat.mul (pow_ne_zero _ (hf _)) (by positivity),
    padicValRat.mul (pow_ne_zero _ (hf _)) hprod,
    Zeta5Normalization.valuation_prod _ _ (fun i hi => pow_ne_zero _ (hf _))]
  simp only [padicValRat.pow, h4, mul_zero, add_zero]
  rw [factorial_rat_valuation_one_level p (N+h) (by omega),
    factorial_rat_valuation_one_level p N (by omega)]
  have hs : (∑ i ∈ Finset.range (h-1),
      (2:ℤ)*padicValRat p (Nat.factorial (2*(i+1)):ℚ)) =
      2*∑ i ∈ Finset.range (h-1), (((2*(i+1))/p:ℕ):ℤ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [factorial_rat_valuation_one_level p (2*(i+1)) (by have := Finset.mem_range.mp hi; omega)]
  simp only [Nat.cast_ofNat]
  rw [hs]
  push_cast
  ring

theorem actual_prime_square_large (n M p : ℕ) (ha : Admissible n M)
    (hcutoff : K n≤M*p) : 5*K n<p^2 := by
  have h := actual_prime_gt_error n M p ha hcutoff
  have hp : 0<p := by omega
  have hm : 5*M<p := by omega
  have hh := Nat.mul_lt_mul_of_pos_right hm hp
  nlinarith

theorem actual_normalizingScalar_valuation (n M p : ℕ) [Fact p.Prime]
    (ha : Admissible n M) (hcutoff : K n≤M*p) :
    padicValRat p (Zeta5Construction.normalizingScalar (N n) (h n)) =
      2*(h n:ℤ)*((K n/p:ℕ):ℤ)-12*(h n:ℤ)*((N n/p:ℕ):ℤ)-
      2*∑ i ∈ Finset.range (h n-1), (((2*(i+1))/p:ℕ):ℤ) := by
  have hK : N n+h n=K n := by dsimp [N,h,K]; omega
  have hlarge := actual_prime_gt_error n M p ha hcutoff
  have hsq := actual_prime_square_large n M p ha hcutoff
  simpa only [hK] using normalizingScalar_valuation_one_level (N n) (h n) p
    (by omega) (by rw [hK]; omega)

#print axioms actual_normalizingScalar_valuation
end Zeta5InnerAsymptotics
