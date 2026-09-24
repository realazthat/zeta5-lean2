import SmallPrimeFunctional
import Mathlib.Algebra.BigOperators.NatAntidiagonal

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5Local
open Polynomial IsUltrametricDist

lemma padic_choose_norm (p k : ℕ) [Fact p.Prime] (x : ℤ_[p]) :
    ‖Ring.choose (x : ℚ_[p]) k‖ ≤ 1 := by
  have h : ((Ring.choose x k : ℤ_[p]) : ℚ_[p]) = Ring.choose (x : ℚ_[p]) k :=
    Ring.map_choose (PadicInt.Coe.ringHom (p := p)) x k
  exact (congrArg norm h).symm.le.trans (Ring.choose x k).property

lemma padic_nat_inv_norm (p n : ℕ) [hp : Fact p.Prime] (hn : n ≠ 0) :
    ‖(n : ℚ_[p])‖⁻¹ = (p : ℝ) ^ padicValNat p n := by
  rw [Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hn)]
  rw [show (n : ℚ_[p]) = ((n : ℚ) : ℚ_[p]) by simp,
    Padic.valuation_ratCast, padicValRat.of_nat, ← zpow_neg, neg_neg, zpow_natCast]

lemma padic_choose_small_norm (p k : ℕ) [hp : Fact p.Prime] (x : ℤ_[p]) :
    ‖Ring.choose (x : ℚ_[p]) (k+1)‖ ≤ ‖(x : ℚ_[p])‖ * (p : ℝ)^Nat.log p (k+1) := by
  have heq := Ring.choose_smul_choose (x : ℚ_[p]) (n := k+1) (k := 1) (by omega)
  simp only [Nat.choose_one_right, nsmul_eq_mul, Ring.choose_one_right,
    Nat.cast_one, Nat.add_sub_cancel] at heq
  have heq' : Ring.choose (x : ℚ_[p]) (k+1) =
      (x : ℚ_[p]) * Ring.choose ((x : ℚ_[p])-1) k / (k+1) := by
    apply (eq_div_iff (by exact_mod_cast Nat.succ_ne_zero k)).2
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using heq
  rw [heq', norm_div, norm_mul, div_eq_mul_inv]
  have hc : ‖Ring.choose ((x : ℚ_[p])-1) k‖ ≤ 1 := by
    simpa only [PadicInt.coe_sub, PadicInt.coe_one] using padic_choose_norm p k (x-1)
  have hi : ‖((k : ℚ_[p])+1)‖⁻¹ ≤ (p : ℝ)^Nat.log p (k+1) := by
    rw [← Nat.cast_one (R := ℚ_[p]), ← Nat.cast_add,
      padic_nat_inv_norm p (k+1) (by omega)]
    exact pow_le_pow_right₀ (by exact_mod_cast hp.out.one_le) (padicValNat_le_nat_log _)
  exact (mul_le_mul (mul_le_mul_of_nonneg_left hc (norm_nonneg _)) hi
    (by positivity) (by positivity)).trans_eq (by ring)

lemma padic_choose_sub_norm (p k : ℕ) [hp : Fact p.Prime] (x y : ℤ_[p]) :
    ‖Ring.choose (x : ℚ_[p]) k - Ring.choose (y : ℚ_[p]) k‖ ≤
      ‖((x-y : ℤ_[p]) : ℚ_[p])‖ * (p : ℝ)^Nat.log p k := by
  cases k with
  | zero => simp
  | succ k =>
    have heq := Ring.add_choose_eq (k+1)
      (Commute.all (y : ℚ_[p]) ((x-y : ℤ_[p]) : ℚ_[p]))
    rw [Finset.Nat.sum_antidiagonal_succ'] at heq
    simp only [PadicInt.coe_sub, add_sub_cancel, Ring.choose_zero_right, mul_one] at heq
    rw [heq, add_sub_cancel_left]
    apply norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro ij hij
    rw [norm_mul]
    have hj : ij.2+1 ≤ k+1 := by
      have := Finset.mem_antidiagonal.mp hij
      omega
    have hpow : (p : ℝ)^Nat.log p (ij.2+1) ≤ (p : ℝ)^Nat.log p (k+1) :=
      pow_le_pow_right₀ (by exact_mod_cast hp.out.one_le) (Nat.log_mono_right hj)
    have hb := (padic_choose_small_norm p ij.2 (x-y)).trans
      (mul_le_mul_of_nonneg_left hpow (norm_nonneg _))
    exact (mul_le_mul (padic_choose_norm p ij.1 y) hb
      (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

lemma binomialPolynomial_eval₂ (p k : ℕ) [Fact p.Prime] (x : ℚ_[p]) :
    (binomialPolynomial k).eval₂ (Rat.castHom ℚ_[p]) x = Ring.choose x k := by
  simpa only [binomialPolynomial, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] using
    Ring.map_choose (Polynomial.eval₂RingHom (Rat.castHom ℚ_[p]) x) X k

lemma padic_newton_expansion (p : ℕ) [Fact p.Prime] (P : ℚ[X]) (x : ℚ_[p]) :
    P.eval₂ (Rat.castHom ℚ_[p]) x =
      ∑ k ∈ Finset.range (P.natDegree+1),
        (newtonCoefficient P k : ℚ_[p]) * Ring.choose x k := by
  have h := congrArg (fun Q : ℚ[X] => Q.eval₂ (Rat.castHom ℚ_[p]) x)
    (newton_expansion P)
  simpa only [Polynomial.eval₂_finsetSum, Polynomial.eval₂_smul,
    binomialPolynomial_eval₂, Rat.coe_castHom] using h

/-- Integer-valued polynomials satisfy the logarithmic Lipschitz estimate on Z_p. -/
theorem integerValued_lipschitz (p : ℕ) [hp : Fact p.Prime]
    (P : ℚ[X]) (C : ℝ) (d : ℕ) (hdeg : P.natDegree ≤ d) (hC : 0 ≤ C)
    (hP : ∀ n : ℕ, ‖((P.eval (n : ℚ) : ℚ) : ℚ_[p])‖ ≤ C) (x y : ℤ_[p]) :
    ‖P.eval₂ (Rat.castHom ℚ_[p]) (x : ℚ_[p]) -
      P.eval₂ (Rat.castHom ℚ_[p]) (y : ℚ_[p])‖ ≤
      C * ‖((x-y : ℤ_[p]) : ℚ_[p])‖ * (p : ℝ)^Nat.log p d := by
  rw [padic_newton_expansion p P (x : ℚ_[p]),
    padic_newton_expansion p P (y : ℚ_[p]), ← Finset.sum_sub_distrib]
  apply norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro k hk
  rw [← mul_sub, norm_mul]
  have hkdeg : k ≤ d := by have := Finset.mem_range.mp hk; omega
  have hpow : (p : ℝ)^Nat.log p k ≤ (p : ℝ)^Nat.log p d :=
    pow_le_pow_right₀ (by exact_mod_cast hp.out.one_le) (Nat.log_mono_right hkdeg)
  have hb := (padic_choose_sub_norm p k x y).trans
    (mul_le_mul_of_nonneg_left hpow (norm_nonneg _))
  exact (mul_le_mul (newtonCoefficient_norm p P C hC hP k) hb
    (norm_nonneg _) hC).trans_eq (by ring)

/-- Bounds on natural values extend to every p-adic integer by the Newton expansion. -/
theorem integerValued_norm_on_padicInt (p : ℕ) [Fact p.Prime]
    (P : ℚ[X]) (C : ℝ) (hC : 0 ≤ C)
    (hP : ∀ n : ℕ, ‖((P.eval (n : ℚ) : ℚ) : ℚ_[p])‖ ≤ C) (x : ℤ_[p]) :
    ‖P.eval₂ (Rat.castHom ℚ_[p]) (x : ℚ_[p])‖ ≤ C := by
  rw [padic_newton_expansion p P (x : ℚ_[p])]
  apply norm_sum_le_of_forall_le_of_nonneg hC
  intro k hk
  rw [norm_mul]
  exact (mul_le_mul (newtonCoefficient_norm p P C hC hP k)
    (padic_choose_norm p k x) (norm_nonneg _) hC).trans_eq (mul_one _)

/-- Removing finitely many initial natural values does not change a p-adic polynomial bound. -/
theorem polynomial_norm_of_nat_tail (p : ℕ) [hp : Fact p.Prime]
    (P : ℚ[X]) (C : ℝ) (K : ℕ)
    (hP : ∀ n : ℕ, K < n → ‖((P.eval (n : ℚ) : ℚ) : ℚ_[p])‖ ≤ C) (n : ℕ) :
    ‖((P.eval (n : ℚ) : ℚ) : ℚ_[p])‖ ≤ C := by
  have hp0 : ‖(p : ℚ_[p])‖ < 1 := by
    rw [Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  have ht : Filter.Tendsto (fun k : ℕ => ((n+(K+1)*p^k : ℕ) : ℚ_[p]))
      Filter.atTop (nhds (n : ℚ_[p])) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hp0).const_mul ((K+1 : ℕ) : ℚ_[p])
    have h' := h.const_add (n:ℚ_[p])
    simpa only [mul_zero, add_zero, Nat.cast_add, Nat.cast_mul, Nat.cast_pow] using h'
  have hc := P.continuous_eval₂ (Rat.castHom ℚ_[p])
  have hlim := (hc.tendsto (n : ℚ_[p])).comp ht
  have hbound (k : ℕ) :
      ‖P.eval₂ (Rat.castHom ℚ_[p]) ((n+(K+1)*p^k : ℕ) : ℚ_[p])‖ ≤ C := by
    have hk : 1 ≤ p^k := Nat.one_le_pow _ _ hp.out.pos
    have hkn : K < n+(K+1)*p^k := by nlinarith
    have he := Polynomial.eval₂_at_apply (p := P) (Rat.castHom ℚ_[p]) ((n+(K+1)*p^k : ℕ):ℚ)
    simp only [Rat.coe_castHom, Rat.cast_natCast] at he
    rw [he]
    exact hP _ hkn
  have h := le_of_tendsto' hlim.norm hbound
  have he := Polynomial.eval₂_at_apply (p := P) (Rat.castHom ℚ_[p]) (n:ℚ)
  simp only [Rat.coe_castHom, Rat.cast_natCast] at he
  rwa [he] at h

#print axioms padic_choose_sub_norm
#print axioms integerValued_lipschitz
#print axioms integerValued_norm_on_padicInt
#print axioms polynomial_norm_of_nat_tail
end Zeta5Local
