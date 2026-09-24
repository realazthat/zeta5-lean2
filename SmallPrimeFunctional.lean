import PolynomialDistribution
import Mathlib.NumberTheory.Padics.MahlerBasis
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Polynomial.Taylor

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta5Local
open Polynomial

noncomputable def binomialPolynomial (n : ℕ) : ℚ[X] := Ring.choose X n

lemma binomialPolynomial_comp (n : ℕ) (Q : ℚ[X]) :
    (binomialPolynomial n).comp Q = Ring.choose Q n := by
  simpa [binomialPolynomial] using Ring.map_choose (Polynomial.compRingHom Q) X n

lemma binomialPolynomial_eval (n : ℕ) (x : ℚ) :
    (binomialPolynomial n).eval x = Ring.choose x n := by
  simpa [binomialPolynomial] using Ring.map_choose (Polynomial.evalRingHom x) X n

lemma binomialPolynomial_factorial (n : ℕ) :
    (n.factorial : ℚ) • binomialPolynomial n = descPochhammer ℚ n := by
  have h := Ring.descPochhammer_eq_factorial_smul_choose (X : ℚ[X]) n
  rw [← Polynomial.aeval_eq_smeval, Polynomial.aeval_X_left_eq_map,
    descPochhammer_map] at h
  simpa only [binomialPolynomial, Nat.cast_smul_eq_nsmul] using h.symm

lemma binomialPolynomial_eq (n : ℕ) :
    binomialPolynomial n = (n.factorial : ℚ)⁻¹ • descPochhammer ℚ n := by
  rw [← binomialPolynomial_factorial]
  rw [inv_smul_smul₀ (by exact_mod_cast Nat.factorial_ne_zero n)]

lemma descPochhammer_eval_neg_one (n : ℕ) :
    (descPochhammer ℚ n).eval (-1) = (-1 : ℚ)^n * n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [descPochhammer_succ_eval, ih, pow_succ, Nat.factorial_succ]
    push_cast
    ring

lemma binomialPolynomial_coeff_one (n : ℕ) :
    (binomialPolynomial (n+1)).coeff 1 = (-1 : ℚ)^n / (n+1) := by
  rw [binomialPolynomial_eq, Polynomial.coeff_smul,
    descPochhammer_succ_left, show 1 = 0+1 by rfl, coeff_X_mul,
    coeff_zero_eq_eval_zero, eval_comp]
  simp only [eval_sub, eval_X, eval_one, zero_sub, descPochhammer_eval_neg_one,
    smul_eq_mul, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

lemma binomialPolynomial_translation (n : ℕ) :
    (binomialPolynomial (n+1)).comp (1+X) - binomialPolynomial (n+1) =
      binomialPolynomial n := by
  rw [binomialPolynomial_comp, add_comm (1 : ℚ[X]), Ring.choose_succ_succ]
  exact add_sub_cancel_right _ _

/-- The binomial-basis formula preceding equation (3.9). -/
theorem bernoulliFunctional_binomial (n : ℕ) :
    bernoulliFunctional (binomialPolynomial n) = (-1 : ℚ)^n/(n+1) := by
  have h := bernoulliFunctional_translation (binomialPolynomial (n+1))
  rwa [binomialPolynomial_translation, binomialPolynomial_coeff_one] at h

theorem bernoulliFunctional_binomial_valuation (p n : ℕ) [Fact p.Prime] :
    padicValRat p (bernoulliFunctional (binomialPolynomial n)) =
      -(padicValNat p (n+1) : ℤ) := by
  rw [bernoulliFunctional_binomial, padicValRat.div
    (pow_ne_zero _ (by norm_num)) (by positivity), padicValRat.pow]
  simp only [padicValRat.neg, padicValRat.one, mul_zero, zero_sub]
  congr 1
  rw [show (n : ℚ)+1 = ((n+1 : ℕ) : ℚ) by push_cast; rfl, padicValRat.of_nat]

theorem bernoulliFunctional_binomial_norm (p n : ℕ) [hp : Fact p.Prime] :
    ‖(bernoulliFunctional (binomialPolynomial n) : ℚ_[p])‖ ≤
      (p : ℝ) ^ Nat.log p (n+1) := by
  have hq : bernoulliFunctional (binomialPolynomial n) ≠ 0 := by
    rw [bernoulliFunctional_binomial]
    exact div_ne_zero (pow_ne_zero _ (by norm_num)) (by positivity)
  rw [Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hq),
    Padic.valuation_ratCast, bernoulliFunctional_binomial_valuation,
    neg_neg, zpow_natCast]
  exact pow_le_pow_right₀ (by exact_mod_cast hp.out.one_le) (padicValNat_le_nat_log (n+1))

open scoped fwdDiff

noncomputable def newtonCoefficient (P : ℚ[X]) (n : ℕ) : ℚ :=
  Δ_[1]^[n] P.eval 0

lemma newtonCoefficient_eq_zero (P : ℚ[X]) {n : ℕ} (hn : P.natDegree < n) :
    newtonCoefficient P n = 0 := by
  unfold newtonCoefficient
  rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hn]
  rfl

/-- The finite Newton expansion with its actual forward-difference coefficients. -/
theorem newton_expansion (P : ℚ[X]) :
    P = ∑ n ∈ Finset.range (P.natDegree+1), newtonCoefficient P n • binomialPolynomial n := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective (Nat.cast_injective (R := ℚ))).mono
  rintro x ⟨n, rfl⟩
  change P.eval (n : ℚ) = _
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_smul,
    binomialPolynomial_eval, Ring.choose_natCast, smul_eq_mul]
  let f : ℕ → ℚ := fun k => newtonCoefficient P k * (n.choose k : ℚ)
  have hd : (∑ k ∈ Finset.range (P.natDegree+1), f k) =
      ∑ k ∈ Finset.range (max (P.natDegree+1) (n+1)), f k := by
    apply Finset.sum_subset (Finset.range_mono (le_max_left _ _))
    intro k hk hkn
    have hdeg : P.natDegree < k := by
      have := (Finset.mem_range.not.mp hkn)
      omega
    simp [f, newtonCoefficient_eq_zero P hdeg]
  have hn : (∑ k ∈ Finset.range (n+1), f k) =
      ∑ k ∈ Finset.range (max (P.natDegree+1) (n+1)), f k := by
    apply Finset.sum_subset (Finset.range_mono (le_max_right _ _))
    intro k hk hkn
    have hnk : n < k := by
      have := (Finset.mem_range.not.mp hkn)
      omega
    simp [f, Nat.choose_eq_zero_of_lt hnk]
  change P.eval (n : ℚ) = ∑ k ∈ Finset.range (P.natDegree+1), f k
  rw [hd, ← hn]
  simpa [f, newtonCoefficient, nsmul_eq_mul, mul_comm] using
    shift_eq_sum_fwdDiff_iter (1 : ℚ) P.eval n 0

open IsUltrametricDist

theorem newtonCoefficient_norm (p : ℕ) [Fact p.Prime] (P : ℚ[X]) (C : ℝ)
    (hC : 0 ≤ C) (hP : ∀ n : ℕ, ‖((P.eval (n : ℚ) : ℚ) : ℚ_[p])‖ ≤ C) (k : ℕ) :
    ‖(newtonCoefficient P k : ℚ_[p])‖ ≤ C := by
  unfold newtonCoefficient
  rw [fwdDiff_iter_eq_sum_shift]
  push_cast
  apply norm_sum_le_of_forall_le_of_nonneg hC
  intro i hi
  simp only [zero_add, nsmul_eq_mul, mul_one]
  exact (IsUltrametricDist.norm_zsmul_le _ _).trans (hP i)

/-- A degree-d integer-valued polynomial loses at most log_p(d+1) under L. -/
theorem bernoulliFunctional_integerValued_norm (p : ℕ) [hp : Fact p.Prime]
    (P : ℚ[X]) (C : ℝ) (hC : 0 ≤ C)
    (hP : ∀ n : ℕ, ‖((P.eval (n : ℚ) : ℚ) : ℚ_[p])‖ ≤ C) :
    ‖(bernoulliFunctional P : ℚ_[p])‖ ≤ C * (p : ℝ)^Nat.log p (P.natDegree+1) := by
  have heq := congrArg bernoulliFunctional (newton_expansion P)
  simp only [map_sum, map_smul, smul_eq_mul] at heq
  rw [heq]
  push_cast
  apply norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hC (by positivity))
  intro k hk
  rw [norm_mul]
  have hkdeg : k+1 ≤ P.natDegree+1 := Finset.mem_range.mp hk
  have hlog : Nat.log p (k+1) ≤ Nat.log p (P.natDegree+1) := Nat.log_mono_right hkdeg
  have hb := (bernoulliFunctional_binomial_norm p k).trans
    (pow_le_pow_right₀ (by exact_mod_cast hp.out.one_le) hlog)
  exact mul_le_mul (newtonCoefficient_norm p P C hC hP k) hb (norm_nonneg _) hC

lemma binomialPolynomial_derivative_eval (k : ℕ) (x : ℚ) :
    (binomialPolynomial k).derivative.eval x =
      ∑ ij ∈ Finset.antidiagonal k,
        Ring.choose x ij.1 * (binomialPolynomial ij.2).coeff 1 := by
  rw [← Polynomial.taylor_coeff_one, Polynomial.taylor_apply,
    binomialPolynomial_comp, add_comm X, Ring.add_choose_eq k (Commute.all _ _)]
  rw [Polynomial.finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro ij hij
  have hC : Ring.choose (C x) ij.1 = C (Ring.choose x ij.1) := by
    exact (Ring.map_choose (C : ℚ →+* ℚ[X]) x ij.1).symm
  rw [hC, Polynomial.coeff_C_mul]
  rfl

lemma binomialPolynomial_coeff_one_norm (p k : ℕ) [hp : Fact p.Prime] :
    ‖((binomialPolynomial k).coeff 1 : ℚ_[p])‖ ≤ (p : ℝ)^Nat.log p k := by
  cases k with
  | zero => norm_num [binomialPolynomial, Polynomial.coeff_one]
  | succ k =>
    rw [binomialPolynomial_coeff_one, ← bernoulliFunctional_binomial]
    exact bernoulliFunctional_binomial_norm p k

theorem binomialPolynomial_derivative_norm (p k n : ℕ) [hp : Fact p.Prime] :
    ‖(((binomialPolynomial k).derivative.eval (n : ℚ) : ℚ) : ℚ_[p])‖ ≤
      (p : ℝ)^Nat.log p k := by
  rw [binomialPolynomial_derivative_eval]
  simp only [Ring.choose_natCast]
  push_cast
  apply norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro ij hij
  rw [norm_mul]
  have hn : ‖(n.choose ij.1 : ℚ_[p])‖ ≤ 1 := by
    simpa using Padic.norm_int_le_one (p := p) (n.choose ij.1 : ℤ)
  have hj : ij.2 ≤ k := (Finset.mem_antidiagonal.mp hij).symm ▸ Nat.le_add_left _ _
  have hb := (binomialPolynomial_coeff_one_norm p ij.2).trans
    (pow_le_pow_right₀ (by exact_mod_cast hp.out.one_le) (Nat.log_mono_right hj))
  exact (mul_le_mul hn hb (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

theorem derivative_integerValued_norm (p : ℕ) [hp : Fact p.Prime]
    (P : ℚ[X]) (C : ℝ) (d : ℕ) (hdeg : P.natDegree ≤ d) (hC : 0 ≤ C)
    (hP : ∀ n : ℕ, ‖((P.eval (n : ℚ) : ℚ) : ℚ_[p])‖ ≤ C) (n : ℕ) :
    ‖((P.derivative.eval (n : ℚ) : ℚ) : ℚ_[p])‖ ≤
      C * (p : ℝ)^Nat.log p (d+1) := by
  have heq := congrArg (fun Q : ℚ[X] => Q.derivative.eval (n : ℚ)) (newton_expansion P)
  simp only [map_sum, map_smul, Polynomial.eval_finsetSum, Polynomial.eval_smul,
    smul_eq_mul] at heq
  rw [heq]
  push_cast
  apply norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hC (by positivity))
  intro k hk
  rw [norm_mul]
  have hkdeg : k ≤ d+1 := by have := Finset.mem_range.mp hk; omega
  have hb := (binomialPolynomial_derivative_norm p k n).trans
    (pow_le_pow_right₀ (by exact_mod_cast hp.out.one_le) (Nat.log_mono_right hkdeg))
  exact mul_le_mul (newtonCoefficient_norm p P C hC hP k) hb (norm_nonneg _) hC

/-- The third derivative contributes at most three copies of the logarithmic loss. -/
theorem third_derivative_integerValued_norm (p : ℕ) [hp : Fact p.Prime]
    (P : ℚ[X]) (C : ℝ) (d : ℕ) (hdeg : P.natDegree ≤ d) (hC : 0 ≤ C)
    (hP : ∀ n : ℕ, ‖((P.eval (n : ℚ) : ℚ) : ℚ_[p])‖ ≤ C) (n : ℕ) :
    ‖((P.derivative.derivative.derivative.eval (n : ℚ) : ℚ) : ℚ_[p])‖ ≤
      C * ((p : ℝ)^Nat.log p (d+1))^3 := by
  have hd1 : P.derivative.natDegree ≤ d :=
    (natDegree_derivative_le P).trans ((Nat.sub_le _ _).trans hdeg)
  have hd2 : P.derivative.derivative.natDegree ≤ d :=
    (natDegree_derivative_le _).trans ((Nat.sub_le _ _).trans hd1)
  have h1 := derivative_integerValued_norm p P C d hdeg hC hP
  have h2 := derivative_integerValued_norm p P.derivative
    (C * (p : ℝ)^Nat.log p (d+1)) d hd1 (mul_nonneg hC (by positivity)) h1
  have h3 := derivative_integerValued_norm p P.derivative.derivative
    (C * (p : ℝ)^Nat.log p (d+1) * (p : ℝ)^Nat.log p (d+1)) d hd2
    (by positivity) h2 n
  convert h3 using 1 <;> ring

/-- Equation (3.9), with the exact norm of 1/24 left explicit. -/
theorem rationalTauFunctional_integerValued_norm (p : ℕ) [hp : Fact p.Prime]
    (P : ℚ[X]) (C : ℝ) (d : ℕ) (hdeg : P.natDegree ≤ d) (hC : 0 ≤ C)
    (hP : ∀ n : ℕ, ‖((P.eval (n : ℚ) : ℚ) : ℚ_[p])‖ ≤ C) :
    ‖(rationalTauFunctional P : ℚ_[p])‖ ≤
      C * (p : ℝ)^(4 * Nat.log p (d+1)) * ‖(24 : ℚ_[p])‖⁻¹ := by
  have hd1 : P.derivative.natDegree ≤ d :=
    (natDegree_derivative_le P).trans ((Nat.sub_le _ _).trans hdeg)
  have hd2 : P.derivative.derivative.natDegree ≤ d :=
    (natDegree_derivative_le _).trans ((Nat.sub_le _ _).trans hd1)
  have hd3 : P.derivative.derivative.derivative.natDegree ≤ d :=
    (natDegree_derivative_le _).trans ((Nat.sub_le _ _).trans hd2)
  have hb := bernoulliFunctional_integerValued_norm p
    P.derivative.derivative.derivative
    (C * ((p : ℝ)^Nat.log p (d+1))^3) (by positivity)
    (third_derivative_integerValued_norm p P C d hdeg hC hP)
  have hl : (p : ℝ)^Nat.log p (P.derivative.derivative.derivative.natDegree+1) ≤
      (p : ℝ)^Nat.log p (d+1) :=
    pow_le_pow_right₀ (by exact_mod_cast hp.out.one_le)
      (Nat.log_mono_right (Nat.add_le_add_right hd3 1))
  have hb' := hb.trans (mul_le_mul_of_nonneg_left hl (by positivity))
  rw [rationalTauFunctional_apply]
  push_cast
  rw [norm_div, div_eq_mul_inv]
  apply (mul_le_mul_of_nonneg_right hb' (by positivity)).trans_eq
  congr 1
  rw [Nat.mul_comm 4, pow_mul]
  ring

#print axioms bernoulliFunctional_binomial
#print axioms newton_expansion
#print axioms bernoulliFunctional_integerValued_norm
#print axioms binomialPolynomial_derivative_norm
#print axioms derivative_integerValued_norm
#print axioms rationalTauFunctional_integerValued_norm
end Zeta5Local
