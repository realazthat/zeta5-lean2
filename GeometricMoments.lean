import Moments

noncomputable section
open scoped BigOperators
open MeasureTheory Set Polynomial

namespace Zeta5Construction

/-- The Laplace integral defining the shifted reciprocal fifth-power sum. -/
def boseIntegrand (j : ℕ) (u : ℝ) : ℝ :=
  u^4 * Real.exp (-(j*u)) / (1-Real.exp (-u))

lemma fifthPowerTail_summable (j : ℕ) :
    Summable (fun n : ℕ => 1/(j+n : ℝ)^5) := by
  have hh := (summable_nat_add_iff j).mpr
    (Real.summable_one_div_nat_pow.mpr (by decide : 1 < (5 : ℕ)))
  apply hh.congr
  intro n
  simp only [Nat.cast_add]
  congr 2
  ring

lemma laplaceFifthTerm_integrable (j n : ℕ) (hj : 0 < j) :
    IntegrableOn (fun u : ℝ => u^4 * Real.exp (-((j+n : ℝ)*u))) (Ioi 0) := by
  apply power_exp_integrable
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  positivity

lemma laplaceFifthTerm_integral (j n : ℕ) (hj : 0 < j) :
    (∫ u : ℝ in Ioi 0, u^4 * Real.exp (-((j+n : ℝ)*u))) =
      24 * (1/(j+n : ℝ)^5) := by
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  rw [power_exp_integral 4 (by positivity)]
  norm_num
  ring

lemma laplaceFifthTerm_norm_summable (j : ℕ) (hj : 0 < j) :
    Summable (fun n : ℕ => ∫ u : ℝ in Ioi 0, ‖u^4 * Real.exp (-((j+n : ℝ)*u))‖) := by
  have hh (n : ℕ) : (∫ u : ℝ in Ioi 0, ‖u^4 * Real.exp (-((j+n : ℝ)*u))‖) =
      24 * (1/(j+n : ℝ)^5) := by
    rw [← laplaceFifthTerm_integral j n hj]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    apply Real.norm_of_nonneg
    positivity
  simp_rw [hh]
  exact (fifthPowerTail_summable j).mul_left 24

lemma boseIntegrand_eq_tsum (j : ℕ) {u : ℝ} (hu : 0 < u) :
    boseIntegrand j u = ∑' n : ℕ, u^4 * Real.exp (-((j+n : ℝ)*u)) := by
  have he : ‖Real.exp (-u)‖ < 1 := by
    rw [Real.norm_of_nonneg (Real.exp_nonneg _), Real.exp_lt_one_iff]
    linarith
  have hg := tsum_geometric_of_norm_lt_one he
  unfold boseIntegrand
  calc
    _ = (u^4 * Real.exp (-(j*u))) * ∑' n : ℕ, Real.exp (-u)^n := by
      rw [hg]
      ring
    _ = ∑' n : ℕ, (u^4 * Real.exp (-(j*u))) * Real.exp (-u)^n :=
      tsum_mul_left.symm
    _ = _ := by
      apply tsum_congr
      intro n
      rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- The geometric-series/Gamma half of the simple-pole integral identity. -/
theorem boseIntegral_eq_fifthPowerTail (j : ℕ) (hj : 0 < j) :
    (∫ u : ℝ in Ioi 0, boseIntegrand j u) =
      24 * ∑' n : ℕ, 1/(j+n : ℝ)^5 := by
  calc
    _ = ∫ u : ℝ in Ioi 0, ∑' n : ℕ, u^4 * Real.exp (-((j+n : ℝ)*u)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      exact boseIntegrand_eq_tsum j hu
    _ = ∑' n : ℕ, ∫ u : ℝ in Ioi 0, u^4 * Real.exp (-((j+n : ℝ)*u)) :=
      (integral_tsum_of_summable_integral_norm
        (fun n => laplaceFifthTerm_integrable j n hj)
        (laplaceFifthTerm_norm_summable j hj)).symm
    _ = _ := by simp_rw [laplaceFifthTerm_integral j _ hj, tsum_mul_left]

lemma boseIntegrand_integrable (j : ℕ) (hj : 0 < j) :
    IntegrableOn (boseIntegrand j) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [boseIntegral_eq_fifthPowerTail j hj]
  apply ne_of_gt
  apply mul_pos (by norm_num)
  apply (fifthPowerTail_summable j).tsum_pos (fun n => by positivity) 0
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  positivity

lemma harmonic5_cast (j : ℕ) :
    (harmonic5 j : ℝ) = ∑ n ∈ Finset.range j, 1/(n+1 : ℝ)^5 := by
  simp only [harmonic5, Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_pow,
    Rat.cast_natCast, Nat.cast_add, Nat.cast_one, Rat.cast_add]

lemma harmonic5_cast_eq_sum_range (j : ℕ) :
    (harmonic5 j : ℝ) = (∑ n ∈ Finset.range j, 1/(n : ℝ)^5) + 1/(j : ℝ)^5 := by
  rw [harmonic5_cast]
  have hh := Finset.sum_range_succ' (fun n : ℕ => 1/(n : ℝ)^5) j
  simp only [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one, Nat.cast_zero,
    zero_pow (by decide : 5 ≠ 0), div_zero, add_zero] at hh
  exact hh.symm

/-- Rewriting the shifted reciprocal-power series into ζ(5)-H_j plus
its endpoint correction, without invoking any special-function identity. -/
theorem fifthPowerTail_eq_series_sub_harmonic (j : ℕ) :
    (∑' n : ℕ, 1/(j+n : ℝ)^5) =
      (∑' n : ℕ, 1/(n : ℝ)^5) - (harmonic5 j : ℝ) + 1/(j : ℝ)^5 := by
  have hs := Real.summable_one_div_nat_pow.mpr (by decide : 1 < (5 : ℕ))
  have hh := hs.sum_add_tsum_nat_add j
  have ht : (∑' n : ℕ, 1/((n+j : ℕ) : ℝ)^5) =
      (∑' n : ℕ, 1/(j+n : ℝ)^5) := by
    apply tsum_congr
    intro n
    simp only [Nat.cast_add]
    congr 2
    ring
  rw [ht] at hh
  rw [harmonic5_cast_eq_sum_range]
  linarith

end Zeta5Construction
