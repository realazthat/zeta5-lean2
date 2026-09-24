import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Zeta5Kernel

lemma paired_inverse_im (y a : ℝ) :
    (1 / ((y : ℂ) * Complex.I - (a : ℂ)) +
      1 / ((y : ℂ) * Complex.I + (a : ℂ))).im =
      -2 * y / (y ^ 2 + a ^ 2) := by
  simp only [Complex.add_im, one_div, Complex.inv_im, Complex.normSq_apply,
    Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_self,
    Complex.sub_im, Complex.mul_im, mul_one, zero_add, sub_zero,
    Complex.add_re, Complex.add_im, add_zero, zero_sub]
  ring

lemma imag_axis_not_integer {y : ℝ} (hy : 0 < y) :
    (y : ℂ) * Complex.I ∈ Complex.integerComplement := by
  rintro ⟨k, hk⟩
  have := congrArg Complex.im hk
  simp at this
  linarith

lemma cot_imag_axis (y : ℝ) :
    (Complex.cot ((Real.pi : ℂ) * ((y : ℂ) * Complex.I))).im =
      -(Real.exp (-2 * Real.pi * y) + 1) /
        (1 - Real.exp (-2 * Real.pi * y)) := by
  rw [Complex.cot_pi_eq_exp_ratio]
  have he : (2 : ℂ) * Real.pi * Complex.I * ((y : ℂ) * Complex.I) =
      ((-2 * Real.pi * y : ℝ) : ℂ) := by
    push_cast
    calc
      _ = (2 * Real.pi * (y : ℂ)) * (Complex.I * Complex.I) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [he, ← Complex.ofReal_exp]
  simp only [Complex.div_im, Complex.add_im, Complex.ofReal_im,
    Complex.one_im, add_zero, Complex.mul_re, Complex.I_re,
    Complex.sub_re, Complex.one_re, Complex.ofReal_re, zero_mul,
    Complex.I_im, Complex.sub_im, sub_self, mul_zero, sub_zero,
    Complex.add_re, Complex.mul_im, mul_one, one_mul, zero_add,
    Complex.normSq_apply]
  have hc : -2 * Real.pi * y = -(2 * Real.pi * y) := by ring
  simp only [hc]
  by_cases h : 1 - Real.exp (-(2 * Real.pi * y)) = 0
  · simp [h]
  · field_simp
    <;> ring

lemma inverse_imag_axis (y : ℝ) :
    (1 / ((y : ℂ) * Complex.I)).im = -1 / y := by
  simp [div_mul_eq_div_div, Complex.div_I, one_div, neg_div]

lemma kernel_from_cot_series (y : ℝ) (hy : 0 < y)
    (hs : Summable (fun n : ℕ =>
      1 / ((y : ℂ) * Complex.I - (n + 1)) +
      1 / ((y : ℂ) * Complex.I + (n + 1))))
    (heq : (Real.pi : ℂ) * Complex.cot (Real.pi * ((y : ℂ) * Complex.I)) -
      1 / ((y : ℂ) * Complex.I) = ∑' n : ℕ,
      (1 / ((y : ℂ) * Complex.I - (n + 1)) +
      1 / ((y : ℂ) * Complex.I + (n + 1)))) :
    1 / (1 - Real.exp (-2 * Real.pi * y)) =
      1 / (2 * Real.pi * y) + 1 / 2 +
        (y / Real.pi) * ∑' n : ℕ, 1 / (y ^ 2 + ((n : ℝ) + 1) ^ 2) := by
  have hi := congrArg Complex.im heq
  rw [Complex.im_tsum hs] at hi
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, cot_imag_axis, inverse_imag_axis] at hi
  have ht : (∑' n : ℕ,
      (1 / ((y : ℂ) * Complex.I - (n + 1)) +
        1 / ((y : ℂ) * Complex.I + (n + 1))).im) =
      (-2 * y) * ∑' n : ℕ, 1 / (y ^ 2 + ((n : ℝ) + 1) ^ 2) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    simpa only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one,
      mul_one_div] using paired_inverse_im y ((n : ℝ) + 1)
  rw [ht] at hi
  have hc : -2 * Real.pi * y = -(2 * Real.pi * y) := by ring
  simp only [hc] at hi ⊢
  generalize hEdef : Real.exp (-(2 * Real.pi * y)) = E at hi ⊢
  have hE : 1 - E ≠ 0 := by
    rw [← hEdef]
    have : Real.exp (-(2 * Real.pi * y)) < 1 := by
      rw [Real.exp_lt_one_iff]
      nlinarith [Real.pi_pos]
    linarith
  field_simp [ne_of_gt hy, Real.pi_ne_zero, hE] at hi ⊢
  linear_combination -hi

theorem bose_kernel_scaled (y : ℝ) (hy : 0 < y) :
    1 / (1 - Real.exp (-2 * Real.pi * y)) =
      1 / (2 * Real.pi * y) + 1 / 2 +
        (y / Real.pi) * ∑' n : ℕ, 1 / (y ^ 2 + ((n : ℝ) + 1) ^ 2) := by
  exact kernel_from_cot_series y hy
    (summable_cotTerm (imag_axis_not_integer hy))
    (cot_series_rep' (imag_axis_not_integer hy))

theorem bose_kernel (u : ℝ) (hu : 0 < u) :
    1 / (1 - Real.exp (-u)) =
      1 / u + 1 / 2 + 2 * u *
        ∑' n : ℕ, 1 / (u ^ 2 + (2 * Real.pi * ((n : ℝ) + 1)) ^ 2) := by
  have hy : 0 < u / (2 * Real.pi) := by positivity
  have h := bose_kernel_scaled (u / (2 * Real.pi)) hy
  have ha : 2 * Real.pi * (u / (2 * Real.pi)) = u := by
    field_simp
  have hb : -2 * Real.pi * (u / (2 * Real.pi)) = -u := by
    field_simp
  rw [ha, hb] at h
  rw [h]
  congr 1
  rw [← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro n
  have hn : 0 < u ^ 2 + (2 * Real.pi * ((n : ℝ) + 1)) ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos hu) (sq_nonneg _)
  have hn' : 0 < (u / (2 * Real.pi)) ^ 2 + ((n : ℝ) + 1) ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos hy) (sq_nonneg _)
  field_simp
  <;> ring

#print axioms bose_kernel

end Zeta5Kernel
