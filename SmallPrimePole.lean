import SmallPrimeLipschitz
import LocalFunctional

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5Local
open Polynomial IsUltrametricDist

lemma harmonic5_norm (p n : ℕ) [hp : Fact p.Prime] :
    ‖(harmonic5 n : ℚ_[p])‖ ≤ (p:ℝ)^(5*Nat.log p n) := by
  unfold harmonic5
  push_cast
  apply norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro i hi
  rw [norm_div, norm_one, norm_pow, one_div, ← inv_pow,
    ← Nat.cast_one (R:=ℚ_[p]), ← Nat.cast_add, padic_nat_inv_norm p (i+1) (by omega),
    ← pow_mul]
  apply pow_le_pow_right₀ (by exact_mod_cast hp.out.one_le)
  have hlog : Nat.log p (i+1) ≤ Nat.log p n := Nat.log_mono_right (Finset.mem_range.mp hi)
  have hval := padicValNat_le_nat_log (p:=p) (i+1)
  omega

lemma poleIndex_le_bound (K : ℕ) (r : ℤ) (hr : -(K:ℤ)≤r ∧ r≤K) : poleIndex r ≤ K := by
  unfold poleIndex
  split_ifs <;> omega

lemma poleValue_coeff_norm (p K : ℕ) [hp : Fact p.Prime] (r : ℤ)
    (hr : -(K:ℤ)≤r ∧ r≤K) (n : ℕ) :
    ‖((poleValue r).coeff n : ℚ_[p])‖ ≤ (p:ℝ)^(5*Nat.log p K) := by
  unfold poleValue
  rw [Polynomial.coeff_sub]
  by_cases hn0 : n=0
  · subst n
    simp only [Polynomial.coeff_C_zero, Polynomial.coeff_X_zero, sub_zero]
    exact (harmonic5_norm p (poleIndex r)).trans
      (pow_le_pow_right₀ (by exact_mod_cast hp.out.one_le)
        (Nat.mul_le_mul_left 5 (Nat.log_mono_right (poleIndex_le_bound K r hr))))
  · by_cases hn1 : n=1
    · subst n
      simp only [Polynomial.coeff_C_succ, Polynomial.coeff_X_one, zero_sub,
        Rat.cast_neg, Rat.cast_one, norm_neg, norm_one]
      exact one_le_pow₀ (by exact_mod_cast hp.out.one_le)
    · simp [Polynomial.coeff_C, Polynomial.coeff_X, hn0, hn1, Ne.symm hn1]

#print axioms harmonic5_norm
#print axioms poleValue_coeff_norm
end Zeta5Local
