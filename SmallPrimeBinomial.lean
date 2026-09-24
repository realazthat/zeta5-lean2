import SmallPrimeBasis
import SmallPrimeLipschitz

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5Local
open Polynomial
open scoped BigOperators

lemma choose_factorial_eval (n : ℕ) (x : ℚ) :
    (n.factorial:ℚ)*Ring.choose x n = (descPochhammer ℚ n).eval x := by
  have h := congrArg (Polynomial.eval x) (binomialPolynomial_factorial n)
  simpa only [Polynomial.eval_smul, binomialPolynomial_eval, smul_eq_mul] using h

lemma centered_descPochhammer (n : ℕ) (x : ℚ) :
    (descPochhammer ℚ (2*n+1)).eval (x+n) =
      x * ∏ k ∈ Finset.range n, (x^2-((k+1:ℕ):ℚ)^2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)+1 = (2*n+1)+1+1 by omega, descPochhammer_succ_left,
      Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one]
    have he : x+((n+1:ℕ):ℚ)-1=x+n := by push_cast; ring
    rw [he, descPochhammer_succ_eval, ih, Finset.prod_range_succ]
    push_cast
    ring

lemma choose_pair_factorial (n : ℕ) (x : ℚ) :
    ((2*(n+1)).factorial:ℚ) *
      (Ring.choose (x+(n+1)) (2*(n+1)) + Ring.choose (x+n) (2*(n+1))) =
      2*x^2 * ∏ k ∈ Finset.range n, (x^2-((k+1:ℕ):ℚ)^2) := by
  rw [mul_add, choose_factorial_eval, choose_factorial_eval]
  have hn : 2*(n+1) = (2*n+1)+1 := by omega
  rw [hn]
  nth_rw 1 [descPochhammer_succ_left]
  rw [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one]
  have he : x+(n+1)-1=x+(n:ℚ) := by ring
  rw [he, descPochhammer_succ_eval (2*n+1) (x+n), centered_descPochhammer]
  push_cast
  ring

lemma denominator_pullback_eval (N : ℕ) (x : ℚ) :
    (Zeta5Construction.denominator N).eval (-x^2) =
      (-1:ℚ)^N * ∏ k ∈ Finset.range N, (x^2-((k+1:ℕ):ℚ)^2) := by
  unfold Zeta5Construction.denominator
  rw [Polynomial.eval_prod]
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  calc
    _ = ∏ k ∈ Finset.range N, (-1:ℚ)*(x^2-((k+1:ℕ):ℚ)^2) := by
      apply Finset.prod_congr rfl
      intro k hk
      ring
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

/-- The paper's binomial identity for q_i(-x²). -/
theorem smallPrimeQ_binomial (n : ℕ) (x : ℚ) :
    (smallPrimeQ (n+1)).eval (-x^2) =
      Ring.choose (x+(n+1)) (2*(n+1)) + Ring.choose (x+n) (2*(n+1)) := by
  have hf : ((2*(n+1)).factorial:ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  apply (mul_left_cancel₀ hf)
  rw [choose_pair_factorial]
  simp only [smallPrimeQ, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  rw [denominator_pullback_eval, pow_succ (-1:ℚ) n]
  have hs : (-1:ℚ)^n * (-1)^n = 1 := by
    rw [← mul_pow]
    norm_num
  field_simp
  linear_combination (x^2*(∏ k∈Finset.range n, (x^2-((k+1:ℕ):ℚ)^2))) * hs

lemma shifted_descPochhammer (n : ℕ) (x : ℚ) :
    (descPochhammer ℚ n).eval (x+n) = ∏ k∈Finset.range n, (x+((k+1:ℕ):ℚ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [descPochhammer_succ_left, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one]
    have he : x+((n+1:ℕ):ℚ)-1=x+n := by push_cast; ring
    rw [he, ih, Finset.prod_range_succ]
    ring

lemma choose_factorial_shift (n : ℕ) (x : ℚ) :
    (n.factorial:ℚ)*Ring.choose (x+n) n = ∏ k∈Finset.range n, (x+((k+1:ℕ):ℚ)) := by
  rw [choose_factorial_eval, shifted_descPochhammer]

/-- The paper's product of two binomials for D_N(-x²)/(N!)². -/
theorem denominator_binomial (N : ℕ) (x : ℚ) :
    (Zeta5Construction.denominator N).eval (-x^2)/(N.factorial:ℚ)^2 =
      Ring.choose ((N:ℚ)-x) N * Ring.choose ((N:ℚ)+x) N := by
  have hfac : (N.factorial:ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  apply (div_eq_iff (pow_ne_zero _ hfac)).mpr
  have hm := choose_factorial_shift N (-x)
  have hp := choose_factorial_shift N x
  unfold Zeta5Construction.denominator
  rw [Polynomial.eval_prod]
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  calc
    _ = (∏ k∈Finset.range N, (-x+((k+1:ℕ):ℚ))) *
        (∏ k∈Finset.range N, (x+((k+1:ℕ):ℚ))) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro k hk
      ring
    _ = _ := by rw [← hm, ← hp]; simp only [neg_add_eq_sub, add_comm x]; ring

lemma rational_int_choose_norm (p : ℕ) [Fact p.Prime] (z : ℤ) (k : ℕ) :
    ‖((Ring.choose (z:ℚ) k : ℚ) : ℚ_[p])‖ ≤ 1 := by
  have h : Ring.choose (z:ℚ) k = ((Ring.choose z k:ℤ):ℚ) :=
    (Ring.map_choose (Int.castRingHom ℚ) z k).symm
  rw [h, Rat.cast_intCast]
  exact Padic.norm_int_le_one _

/-- Every q_i becomes integer-valued under t=-x². -/
theorem smallPrimeQ_integerValued (p i n : ℕ) [Fact p.Prime] :
    ‖(((smallPrimeQ i).eval (-(n:ℚ)^2):ℚ):ℚ_[p])‖ ≤ 1 := by
  cases i with
  | zero => simp
  | succ i =>
    rw [smallPrimeQ_binomial]
    push_cast
    apply (IsUltrametricDist.norm_add_le_max _ _).trans
    apply max_le
    · simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one, Rat.cast_natCast] using
        rational_int_choose_norm p ((n:ℤ)+(i+1)) (2*(i+1))
    · simpa only [Int.cast_add, Int.cast_natCast, Rat.cast_natCast] using
        rational_int_choose_norm p ((n:ℤ)+i) (2*(i+1))

theorem denominator_integerValued (p N n : ℕ) [Fact p.Prime] :
    ‖(((Zeta5Construction.denominator N).eval (-(n:ℚ)^2)/(N.factorial:ℚ)^2:ℚ):ℚ_[p])‖ ≤ 1 := by
  rw [denominator_binomial]
  push_cast
  rw [norm_mul]
  have hm := rational_int_choose_norm p ((N:ℤ)-n) N
  have hp := rational_int_choose_norm p ((N:ℤ)+n) N
  simp only [Int.cast_sub, Int.cast_add, Int.cast_natCast] at hm hp
  simpa only [one_mul] using mul_le_mul hm hp (norm_nonneg _) (by norm_num : (0:ℝ)≤1)

theorem smallPrimeF_integerValued (p N i n : ℕ) [Fact p.Prime] :
    ‖(((smallPrimeF N i).eval (-(n:ℚ)^2):ℚ):ℚ_[p])‖ ≤ 1 := by
  have he : (smallPrimeF N i).eval (-(n:ℚ)^2) =
      ((Zeta5Construction.denominator N).eval (-(n:ℚ)^2)/(N.factorial:ℚ)^2)^3 *
        (smallPrimeQ i).eval (-(n:ℚ)^2) := by
    simp only [smallPrimeF, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow]
    ring
  rw [he]
  push_cast
  rw [norm_mul, norm_pow]
  have hD := denominator_integerValued p N n
  push_cast at hD
  have hq := smallPrimeQ_integerValued p i n
  simpa only [one_mul] using mul_le_mul (pow_le_one₀ (norm_nonneg _) hD (n:=3)) hq (norm_nonneg _)
    (by norm_num : (0:ℝ)≤1)

#print axioms smallPrimeQ_binomial
#print axioms denominator_binomial
#print axioms smallPrimeF_integerValued
end Zeta5Local
