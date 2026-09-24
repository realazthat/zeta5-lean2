import RealNormalization
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
open scoped BigOperators
open MeasureTheory Set intervalIntegral

namespace Zeta5Construction

lemma rightSum_le_integral_of_antitone {g : ℝ → ℝ}
    (hg : AntitoneOn g (Ioi 0))
    (hint : ∀ a b, IntervalIntegrable g volume a b) (m : ℕ) :
    ∑ i ∈ Finset.range m, g (i+1)  ≤  ∫ x in (0:ℝ)..m, g x := by
  have hs := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun i : ℕ => (i:ℝ)) (n := m) (fun i hi => hint i ((i+1:ℕ):ℝ))
  simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one] at hs
  rw [← hs]
  apply Finset.sum_le_sum
  intro i hi
  have hc := intervalIntegral.integral_mono_on_of_le_Ioo
    (show (i:ℝ) ≤ i+1 by linarith)
    (intervalIntegrable_const (c := g (i+1))) (hint i (i+1))
    (fun x hx => by
      have hi0 : (0:ℝ) ≤ i := by positivity
      exact hg (show x ∈ Ioi (0:ℝ) by exact lt_of_le_of_lt hi0 hx.1)
        (show (i:ℝ)+1 ∈ Ioi (0:ℝ) by change 0 < (i:ℝ)+1; positivity) hx.2.le)
  simpa using hc

lemma integral_le_rightSum_of_monotone {g : ℝ → ℝ}
    (hg : MonotoneOn g (Ici 0))
    (hint : ∀ a b, IntervalIntegrable g volume a b) (m : ℕ) :
    (∫ x in (0:ℝ)..m, g x)  ≤  ∑ i ∈ Finset.range m, g (i+1) := by
  have hs := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun i : ℕ => (i:ℝ)) (n := m) (fun i hi => hint i ((i+1:ℕ):ℝ))
  simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one] at hs
  rw [← hs]
  apply Finset.sum_le_sum
  intro i hi
  have hc := intervalIntegral.integral_mono_on
    (show (i:ℝ) ≤ i+1 by linarith)
    (hint i (i+1)) (intervalIntegrable_const (c := g (i+1)))
    (fun x hx => by
      have hi0 : (0:ℝ) ≤ i := by positivity
      exact hg (show x ∈ Ici (0:ℝ) by exact hi0.trans hx.1)
        (show (i:ℝ)+1 ∈ Ici (0:ℝ) by change 0 ≤ (i:ℝ)+1; positivity) hx.2)
  simpa using hc

lemma logQuadratic_sub_log {t K x : ℝ} (ht : 0 < t) (hK : 0 < K) (hx : 0 < x) :
    Real.log (t+(x/K)^2)-2*Real.log x = Real.log (t/x^2+1/K^2) := by
  have he : (t+(x/K)^2)/x^2 = t/x^2+1/K^2 := by field_simp
  have hp : Real.log (x^2) = 2*Real.log x := by rw [Real.log_pow]; norm_num
  rw [← hp, ← Real.log_div (by positivity) (by positivity), he]

lemma logQuadratic_sub_log_antitone {t K : ℝ} (ht : 0 < t) (hK : 0 < K) :
    AntitoneOn (fun x : ℝ => Real.log (t+(x/K)^2)-2*Real.log x) (Ioi 0) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := hx
  have hy0 : 0 < y := hy
  dsimp only
  rw [logQuadratic_sub_log ht hK hx, logQuadratic_sub_log ht hK hy]
  apply Real.log_le_log (by positivity)
  gcongr

lemma logQuadratic_continuous {t K : ℝ} (ht : 0 < t) :
    Continuous (fun x : ℝ => Real.log (t+(x/K)^2)) := by
  apply Continuous.log (by fun_prop)
  intro x
  exact ne_of_gt (by positivity)

lemma sum_log_succ_eq_log_factorial (m : ℕ) :
    ∑ i ∈ Finset.range m, Real.log (i+1 : ℝ) = Real.log (m.factorial : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity)]
    push_cast
    ring

/-- The right Riemann-sum error is dominated by the logarithmic singularity at zero. -/
lemma logQuadratic_riemann_error_le_factorial {t K : ℝ} (ht : 0 < t) (hK : 0 < K)
    (m : ℕ) :
    (∑ i ∈ Finset.range m, Real.log (t+(((i+1:ℕ):ℝ)/K)^2)) -
      K*(∫ u in (0:ℝ)..((m:ℝ)/K), Real.log (t+u^2))  ≤ 
      2*Real.log (m.factorial:ℝ)-2*((m:ℝ)*Real.log m-m) := by
  have hf := logQuadratic_continuous (K := K) ht
  have hint (a b : ℝ) : IntervalIntegrable
      (fun x : ℝ => Real.log (t+(x/K)^2)-2*Real.log x) volume a b :=
    (hf.intervalIntegrable a b).sub (intervalIntegrable_log'.const_mul 2)
  have hs := rightSum_le_integral_of_antitone
    (logQuadratic_sub_log_antitone ht hK) hint m
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  rw [sum_log_succ_eq_log_factorial,
    intervalIntegral.integral_sub (hf.intervalIntegrable 0 m) (intervalIntegrable_log'.const_mul 2),
    intervalIntegral.integral_const_mul, integral_log_from_zero] at hs
  have hscale := intervalIntegral.integral_comp_div
    (fun u : ℝ => Real.log (t+u^2)) hK.ne' (a := 0) (b := (m:ℝ))
  simp only [zero_div, smul_eq_mul] at hscale
  rw [hscale] at hs
  push_cast
  linarith

/-- Equation (6.12), for the positive t used by the Gram integral. -/
theorem denominator_riemann_error {t K : ℝ} {m : ℕ}
    (ht : 0 < t) (hK : 0 < K) (hm : 0 < m) (hmK : (m:ℝ)  ≤  K) :
    0  ≤  (∑ i ∈ Finset.range m, Real.log (t+(((i+1:ℕ):ℝ)/K)^2)) -
      K*(∫ u in (0:ℝ)..((m:ℝ)/K), Real.log (t+u^2)) ∧
    (∑ i ∈ Finset.range m, Real.log (t+(((i+1:ℕ):ℝ)/K)^2)) -
      K*(∫ u in (0:ℝ)..((m:ℝ)/K), Real.log (t+u^2))  ≤  2*Real.log K+2 := by
  constructor
  · have hmono : MonotoneOn (fun x : ℝ => Real.log (t+(x/K)^2)) (Ici 0) := by
      intro x hx y hy hxy
      have hx0 : 0 ≤ x / K := div_nonneg hx hK.le
      apply Real.log_le_log (by positivity)
      gcongr
    have hi := integral_le_rightSum_of_monotone hmono
      (fun a b => (logQuadratic_continuous (K := K) ht).intervalIntegrable a b) m
    have hscale := intervalIntegral.integral_comp_div
      (fun u : ℝ => Real.log (t+u^2)) hK.ne' (a := 0) (b := (m:ℝ))
    simp only [zero_div, smul_eq_mul] at hscale
    rw [hscale] at hi
    push_cast
    linarith
  · have he := logQuadratic_riemann_error_le_factorial ht hK m
    have hf := log_factorial_upper hm
    have hl : Real.log (m:ℝ)  ≤  Real.log K :=
      Real.log_le_log (by exact_mod_cast hm) hmK
    linarith

#print axioms denominator_riemann_error

end Zeta5Construction
