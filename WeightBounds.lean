import Construction
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace Zeta5Construction

lemma fourth_power_le_choose (n : ℕ) :
    ((n : ℝ) + 1)^4 ≤ 24 * ((n+4).choose 4 : ℝ) := by
  have hh := Nat.descFactorial_eq_factorial_mul_choose (n+4) 4
  have hid : (n+4).descFactorial 4 = (n+1)*(n+2)*(n+3)*(n+4) := by
    simp [Nat.descFactorial_succ]
    ring
  rw [hid] at hh
  norm_num at hh
  have hc : ((n : ℝ)+1)*((n : ℝ)+2)*((n : ℝ)+3)*((n : ℝ)+4) =
      24 * ((n+4).choose 4 : ℝ) := by exact_mod_cast hh
  rw [← hc]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  nlinarith [sq_nonneg (n : ℝ), mul_nonneg (sq_nonneg (n : ℝ)) hn]

lemma fourth_geometric_bound {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑' n : ℕ, ((n : ℝ)+1)^4 * q^(n+1) ≤ 24*q/(1-q)^5 := by
  have hqn : ‖q‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hq0]
  have hmajor : Summable (fun n : ℕ => 24*q * ((n+4).choose 4 : ℝ) * q^n) := by
    simpa only [mul_assoc] using
      (summable_choose_mul_geometric_of_norm_lt_one 4 hqn).mul_left (24*q)
  have hterm : ∀ n : ℕ, ((n : ℝ)+1)^4*q^(n+1) ≤
      24*q*((n+4).choose 4 : ℝ)*q^n := by
    intro n
    calc
      _ = ((n : ℝ)+1)^4*(q^n*q) := by rw [pow_succ q n]
      _ ≤ (24*((n+4).choose 4 : ℝ))*(q^n*q) :=
        mul_le_mul_of_nonneg_right (fourth_power_le_choose n) (by positivity)
      _ = _ := by ring
  have hsmall : Summable (fun n : ℕ => ((n : ℝ)+1)^4*q^(n+1)) :=
    hmajor.of_nonneg_of_le (fun n => by positivity) hterm
  calc
    _ ≤ ∑' n : ℕ, 24*q*((n+4).choose 4 : ℝ)*q^n := by
      exact hsmall.tsum_le_tsum hterm hmajor
    _ = _ := by
      simp only [mul_assoc, tsum_mul_left, tsum_choose_mul_geometric_of_norm_lt_one 4 hqn]
      ring

lemma weight_denominator_bound {y : ℝ} (hy : 0 < y) :
    y / (1 - Real.exp (-(2*Real.pi*y))) ≤ 1+y := by
  have hu : 0 < 2*Real.pi*y := by positivity
  have hden : 0 < 1-Real.exp (-(2*Real.pi*y)) := by
    have := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hu)
    linarith
  rw [div_le_iff₀ hden]
  have hlarge : 1+y ≤ Real.exp (2*Real.pi*y) := by
    have hp := Real.pi_gt_three
    have hh := Real.add_one_le_exp (2*Real.pi*y)
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hlarge
    (Real.exp_nonneg (-(2*Real.pi*y)))
  rw [← Real.exp_add] at hm
  simp only [add_neg_cancel, Real.exp_zero] at hm
  nlinarith

/-- The elementary exponential bound (6.11), for the actual series weight. -/
theorem integralWeight_upper {y : ℝ} (hy : 0 < y) :
    integralWeight y ≤ 8192*(1+y)^5*Real.exp (-(2*Real.pi*y)) := by
  let q := Real.exp (-(2*Real.pi*y))
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by
    exact neg_neg_of_pos (show 0 < 2*Real.pi*y by positivity))
  have hd : 0 < 1-q := sub_pos.mpr hq1
  have hseries : (∑' l : ℕ, (l : ℝ)^4 * Real.exp (-(2*Real.pi*y)*l)) =
      ∑' n : ℕ, ((n : ℝ)+1)^4*q^(n+1) := by
    rw [(integralWeight_summable hy).tsum_eq_zero_add]
    simp only [Nat.cast_zero, zero_pow (by decide : 4 ≠ 0), zero_mul, zero_add]
    apply tsum_congr
    intro n
    simp only [Nat.cast_add, Nat.cast_one, q, ← Real.exp_nat_mul]
    congr 2
    ring
  have hs := fourth_geometric_bound hq0.le hq1
  rw [← hseries] at hs
  unfold integralWeight
  calc
    _ ≤ ((2*Real.pi)^4*y^5/12) * (24*q/(1-q)^5) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = 2*(2*Real.pi)^4*(y/(1-q))^5*q := by rw [div_pow]; ring
    _ ≤ 2*(2*Real.pi)^4*(1+y)^5*q := by
      gcongr
      exact weight_denominator_bound hy
    _ ≤ 8192*(1+y)^5*q := by
      have hp : (2*Real.pi)^4 ≤ (8 : ℝ)^4 := by
        gcongr
        linarith [Real.pi_lt_four]
      nlinarith [mul_le_mul_of_nonneg_right hp (show 0 ≤ (1+y)^5*q by positivity)]

#print axioms integralWeight_upper

end Zeta5Construction
