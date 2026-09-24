import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.AbelSummation
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Tactic
import PrimeNumberTheoremAnd.Consequences

/-!
# Prime-weighted asymptotics for Section 5

The final theorems instantiate the proved Chebyshev form of PNT from the
PrimeNumberTheoremAnd project. In particular they do not assume PNT as an
axiom or an unproved hypothesis. This file uses that project's Lean 4.32.2
environment; the determinant files currently use Lean 4.19.
-/

open Filter Asymptotics MeasureTheory
open scoped Topology

namespace Zeta5PrimeSums

set_option maxHeartbeats 800000

theorem scaled_asymptotic_ratio {f : ℝ → ℝ}
    (h : f ~[atTop] id) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => f (a * x) / x) atTop (𝓝 a) := by
  have hratio : Tendsto (fun x : ℝ => f x / x) atTop (𝓝 1) := by
    exact (isEquivalent_iff_tendsto_one
      (show ∀ᶠ x : ℝ in atTop, id x ≠ 0 from
        (eventually_gt_atTop 0).mono fun x hx => ne_of_gt hx)).mp h
  have ht := (hratio.comp (tendsto_id.const_mul_atTop ha)).mul_const a
  simp only [Function.comp_def, id_eq, one_mul] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  field_simp

theorem interval_asymptotic_ratio {f : ℝ → ℝ}
    (h : f ~[atTop] id) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun x : ℝ => (f (b * x) - f (a * x)) / x)
      atTop (𝓝 (b - a)) := by
  simpa only [sub_div] using (scaled_asymptotic_ratio h hb).sub
    (scaled_asymptotic_ratio h ha)

/-- Normalize the θ integral to the fixed interval [0,1]. Its integrand
converges pointwise to t and is dominated by (log 4)t. -/
theorem normalized_theta_integral_tendsto
    (hθ : Chebyshev.theta ~[atTop] id) :
    Tendsto (fun x : ℝ => ∫ t in (0 : ℝ)..1, Chebyshev.theta (x * t) / x)
      atTop (𝓝 (1 / 2)) := by
  have hlim : Tendsto
      (fun x : ℝ => ∫ t in (0 : ℝ)..1, Chebyshev.theta (x * t) / x)
      atTop (𝓝 (∫ t in (0 : ℝ)..1, t)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun t : ℝ => Real.log 4 * t)
    · exact Filter.Eventually.of_forall fun x =>
        ((Chebyshev.theta_mono.measurable.comp
          (measurable_const.mul measurable_id)).div_const x).aestronglyMeasurable
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      apply Filter.Eventually.of_forall
      intro t ht
      have ht0 : 0 ≤ t := (by simpa only [Set.uIoc_of_le zero_le_one] using ht :
        t ∈ Set.Ioc (0 : ℝ) 1).1.le
      rw [Real.norm_eq_abs, abs_of_nonneg
        (div_nonneg (Chebyshev.theta_nonneg _) hx.le)]
      apply (div_le_iff₀ hx).mpr
      nlinarith [Chebyshev.theta_le_log4_mul_x (mul_nonneg hx.le ht0)]
    · exact (continuous_const.mul continuous_id).intervalIntegrable _ _
    · apply Filter.Eventually.of_forall
      intro t ht
      have ht0 : 0 < t := (by simpa only [Set.uIoc_of_le zero_le_one] using ht :
        t ∈ Set.Ioc (0 : ℝ) 1).1
      simpa only [mul_comm] using scaled_asymptotic_ratio hθ ht0
  convert hlim using 1 <;> norm_num [integral_id]

theorem theta_integral_tendsto
    (hθ : Chebyshev.theta ~[atTop] id) :
    Tendsto (fun x : ℝ => (∫ t in (0 : ℝ)..x, Chebyshev.theta t) / x ^ 2)
      atTop (𝓝 (1 / 2)) := by
  apply (normalized_theta_integral_tendsto hθ).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_comp_mul_left _ hx.ne']
  simp only [mul_zero, mul_one, smul_eq_mul]
  field_simp

/-- The prime-weighted Chebyshev sum needed for affine pieces of R. -/
noncomputable def weightedTheta (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.Icc 0 ⌊x⌋₊ with p.Prime, (p : ℝ) * Real.log p

theorem weightedTheta_abel {x : ℝ} (hx : 0 ≤ x) :
    weightedTheta x = x * Chebyshev.theta x -
      ∫ t in (0 : ℝ)..x, Chebyshev.theta t := by
  have hInt : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc 0 x) :=
    (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).integrableOn_Icc
  have h := sum_mul_eq_sub_integral_mul
    (c := fun n : ℕ => if n.Prime then Real.log n else 0)
    (f := fun t : ℝ => t) hx (fun _ _ => differentiableAt_id)
    (by simpa only [deriv_id''] using hInt)
  simp only [deriv_id'', one_mul, mul_ite, mul_zero,
    ← Finset.sum_filter] at h
  simpa only [weightedTheta, ← Chebyshev.theta_eq_sum_Icc,
    intervalIntegral.integral_of_le hx] using h

theorem weightedTheta_ratio_tendsto
    (hθ : Chebyshev.theta ~[atTop] id) :
    Tendsto (fun x : ℝ => weightedTheta x / x ^ 2) atTop (𝓝 (1 / 2)) := by
  have h₁ : Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) := by
    simpa using scaled_asymptotic_ratio hθ (a := 1) zero_lt_one
  have h₂ := h₁.sub (theta_integral_tendsto hθ)
  have heq : (fun x : ℝ => weightedTheta x / x ^ 2) =ᶠ[atTop]
      (fun x : ℝ => Chebyshev.theta x / x -
        (∫ t in (0 : ℝ)..x, Chebyshev.theta t) / x ^ 2) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [weightedTheta_abel hx.le]
    field_simp
  convert h₂.congr' heq.symm using 1 <;> norm_num

theorem scaled_weightedTheta_ratio_tendsto
    (hθ : Chebyshev.theta ~[atTop] id) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => weightedTheta (c * x) / x ^ 2)
      atTop (𝓝 (c ^ 2 / 2)) := by
  have h := ((weightedTheta_ratio_tendsto hθ).comp
    (tendsto_id.const_mul_atTop hc)).mul_const (c ^ 2)
  simp only [Function.comp_def, id_eq] at h
  have h' : Tendsto
      (fun x : ℝ => weightedTheta (c * x) / (c * x) ^ 2 * c ^ 2)
      atTop (𝓝 (c ^ 2 / 2)) := by
    convert h using 1 <;> ring
  apply h'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  field_simp

/-- Endpoint form of the contribution of an affine piece R(x)=a x+b. -/
theorem affine_endpoint_tendsto
    (hθ : Chebyshev.theta ~[atTop] id)
    (a b u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    Tendsto (fun x : ℝ =>
      (a * x * (Chebyshev.theta (v * x) - Chebyshev.theta (u * x)) +
        b * (weightedTheta (v * x) - weightedTheta (u * x))) / x ^ 2)
      atTop (𝓝 (a * (v - u) + b * (v ^ 2 - u ^ 2) / 2)) := by
  have h := ((interval_asymptotic_ratio hθ hu hv).const_mul a).add
    (((scaled_weightedTheta_ratio_tendsto hθ hv).sub
      (scaled_weightedTheta_ratio_tendsto hθ hu)).const_mul b)
  have h' : Tendsto (fun x : ℝ =>
      a * ((Chebyshev.theta (v * x) - Chebyshev.theta (u * x)) / x) +
        b * (weightedTheta (v * x) / x ^ 2 - weightedTheta (u * x) / x ^ 2))
      atTop (𝓝 (a * (v - u) + b * (v ^ 2 - u ^ 2) / 2)) := by
    convert h using 1 <;> ring
  apply h'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  field_simp

theorem sum_Ioc_eq_difference (lo hi : ℕ) (h : lo ≤ hi) (f : ℕ → ℝ) :
    ∑ p ∈ Finset.Ioc lo hi, f p =
      (∑ p ∈ Finset.Icc 0 hi, f p) - ∑ p ∈ Finset.Icc 0 lo, f p := by
  have hsub : Finset.Icc 0 lo ⊆ Finset.Icc 0 hi := by
    intro p hp
    simp only [Finset.mem_Icc] at hp ⊢
    omega
  have hset : Finset.Icc 0 hi \ Finset.Icc 0 lo = Finset.Ioc lo hi := by
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [← Finset.sum_sdiff_eq_sub hsub, hset]

theorem affine_prime_sum_eq_endpoints
    (a b lo hi : ℝ) (h : lo ≤ hi) :
    (∑ p ∈ Finset.Ioc ⌊lo⌋₊ ⌊hi⌋₊ with p.Prime,
      (a + b * (p : ℝ)) * Real.log p) =
        a * (Chebyshev.theta hi - Chebyshev.theta lo) +
          b * (weightedTheta hi - weightedTheta lo) := by
  rw [Finset.sum_filter,
    sum_Ioc_eq_difference _ _ (Nat.floor_mono h)]
  simp_rw [← Finset.sum_filter]
  simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
    mul_assoc, weightedTheta, Chebyshev.theta_eq_sum_Icc]
  ring

/-- The actual interval prime sum for any affine piece of the paper's R.
The endpoints use strict lower and weak upper cutoffs, as in Section 5. -/
theorem affine_prime_sum_tendsto
    (hθ : Chebyshev.theta ~[atTop] id)
    (a b u v : ℝ) (hu : 0 < u) (huv : u ≤ v) :
    Tendsto (fun x : ℝ =>
      (∑ p ∈ Finset.Ioc ⌊u * x⌋₊ ⌊v * x⌋₊ with p.Prime,
        (a * x + b * (p : ℝ)) * Real.log p) / x ^ 2)
      atTop (𝓝 (a * (v - u) + b * (v ^ 2 - u ^ 2) / 2)) := by
  apply (affine_endpoint_tendsto hθ a b u v hu (hu.trans_le huv)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [affine_prime_sum_eq_endpoints _ _ _ _ (mul_le_mul_of_nonneg_right huv hx.le)]

/-- Express the interval endpoints in the paper's variable t=x/p. -/
theorem reciprocal_affine_prime_sum_tendsto
    (hθ : Chebyshev.theta ~[atTop] id)
    (a b c d : ℝ) (hc : 0 < c) (hcd : c ≤ d) :
    Tendsto (fun x : ℝ =>
      (∑ p ∈ Finset.Ioc ⌊x / d⌋₊ ⌊x / c⌋₊ with p.Prime,
        (p : ℝ) * (a * (x / p) + b) * Real.log p) / x ^ 2)
      atTop (𝓝 (a * (1 / c - 1 / d) + b * ((1 / c) ^ 2 - (1 / d) ^ 2) / 2)) := by
  have hd : 0 < d := hc.trans_le hcd
  have huv : 1 / d ≤ 1 / c := one_div_le_one_div_of_le hc hcd
  apply (affine_prime_sum_tendsto hθ a b (1 / d) (1 / c)
    (one_div_pos.mpr hd) huv).congr'
  apply Filter.Eventually.of_forall
  intro x
  have heq (z : ℝ) : 1 / z * x = x / z := by ring
  simp only [heq]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.mem_filter.mp hp).2.ne_zero
  field_simp

/-- The limiting constant is exactly the integral appearing in (5.11). -/
theorem affine_kernel_integral
    (a b c d : ℝ) (hc : 0 < c) (hd : 0 < d) :
    (∫ t in c..d, (a * t + b) / t ^ 3) =
      a * (1 / c - 1 / d) + b * ((1 / c) ^ 2 - (1 / d) ^ 2) / 2 := by
  have hn : (0 : ℝ) ∉ Set.uIcc c d := Set.notMem_uIcc_of_lt hc hd
  have h2 := intervalIntegral.intervalIntegrable_zpow (a := c) (b := d)
    (μ := volume) (n := (-2 : ℤ)) (Or.inr hn)
  have h3 := intervalIntegral.intervalIntegrable_zpow (a := c) (b := d)
    (μ := volume) (n := (-3 : ℤ)) (Or.inr hn)
  have hf : (fun t : ℝ => (a * t + b) / t ^ 3) =
      (fun t : ℝ => a * t ^ (-2 : ℤ) + b * t ^ (-3 : ℤ)) := by
    ext t
    by_cases ht : t = 0
    · norm_num [ht]
    · norm_num [zpow_neg, zpow_ofNat]
      field_simp
  rw [hf, intervalIntegral.integral_add (h2.const_mul a) (h3.const_mul b),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_zpow (Or.inr ⟨by norm_num, hn⟩),
    integral_zpow (Or.inr ⟨by norm_num, hn⟩)]
  norm_num [zpow_neg, zpow_ofNat, one_div]
  field_simp
  ring

theorem reciprocal_affine_prime_sum_integral_tendsto
    (hθ : Chebyshev.theta ~[atTop] id)
    (a b c d : ℝ) (hc : 0 < c) (hcd : c ≤ d) :
    Tendsto (fun x : ℝ =>
      (∑ p ∈ Finset.Ioc ⌊x / d⌋₊ ⌊x / c⌋₊ with p.Prime,
        (p : ℝ) * (a * (x / p) + b) * Real.log p) / x ^ 2)
      atTop (𝓝 (∫ t in c..d, (a * t + b) / t ^ 3)) := by
  rw [affine_kernel_integral a b c d hc (hc.trans_le hcd)]
  exact reciprocal_affine_prime_sum_tendsto hθ a b c d hc hcd

/-- A finite collection of affine pieces can be combined without invoking
any unformalized general partial-summation or weak-convergence result. -/
theorem finite_affine_pieces_tendsto
    (hθ : Chebyshev.theta ~[atTop] id)
    {ι : Type*} (S : Finset ι) (a b c d : ι → ℝ)
    (hc : ∀ i ∈ S, 0 < c i) (hcd : ∀ i ∈ S, c i ≤ d i) :
    Tendsto (fun x : ℝ =>
      (∑ i ∈ S, ∑ p ∈ Finset.Ioc ⌊x / d i⌋₊ ⌊x / c i⌋₊ with p.Prime,
        (p : ℝ) * (a i * (x / p) + b i) * Real.log p) / x ^ 2)
      atTop (𝓝 (∑ i ∈ S, ∫ t in c i..d i, (a i * t + b i) / t ^ 3)) := by
  simpa only [Finset.sum_div] using
    tendsto_finsetSum S (fun i hi =>
      reciprocal_affine_prime_sum_integral_tendsto hθ
        (a i) (b i) (c i) (d i) (hc i hi) (hcd i hi))

/-- The uniformly bounded local errors in (5.7) vanish after prime summation
and division by K². This uses the elementary θ upper bound, not PNT. -/
theorem bounded_prime_errors_tendsto
    (E : ℝ → ℕ → ℝ) (C c : ℝ) (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hE : ∀ᶠ x : ℝ in atTop, ∀ p ∈ Finset.Icc 0 ⌊c * x⌋₊,
      p.Prime → ‖E x p‖ ≤ C) :
    Tendsto (fun x : ℝ =>
      (∑ p ∈ Finset.Icc 0 ⌊c * x⌋₊ with p.Prime,
        E x p * Real.log p) / x ^ 2) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun x : ℝ => C * Real.log 4 * c / x) ?_
    (tendsto_const_nhds.div_atTop tendsto_id)
  filter_upwards [eventually_gt_atTop (0 : ℝ), hE] with x hx hEx
  have hs : ‖∑ p ∈ Finset.Icc 0 ⌊c * x⌋₊ with p.Prime,
      E x p * Real.log p‖ ≤ C * Chebyshev.theta (c * x) := by
    calc
      _ ≤ ∑ p ∈ (Finset.Icc 0 ⌊c * x⌋₊).filter Nat.Prime,
          ‖E x p * Real.log p‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ (Finset.Icc 0 ⌊c * x⌋₊).filter Nat.Prime,
          C * Real.log p := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hpRange, hpPrime⟩ := Finset.mem_filter.mp hp
        have hpLog : 0 ≤ Real.log (p : ℝ) :=
          Real.log_nonneg (by exact_mod_cast hpPrime.one_lt.le)
        rw [norm_mul, Real.norm_of_nonneg hpLog]
        exact mul_le_mul_of_nonneg_right (hEx p hpRange hpPrime) hpLog
      _ = _ := by rw [← Finset.mul_sum, Chebyshev.theta_eq_sum_Icc]
  rw [norm_div, Real.norm_of_nonneg (sq_nonneg x)]
  calc
    _ ≤ (C * Chebyshev.theta (c * x)) / x ^ 2 :=
      div_le_div_of_nonneg_right hs (sq_nonneg x)
    _ ≤ (C * (Real.log 4 * (c * x))) / x ^ 2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (Chebyshev.theta_le_log4_mul_x (mul_nonneg hc hx.le)) hC)
        (sq_nonneg x)
    _ = C * Real.log 4 * c / x := by field_simp

/-- Unconditional: the first weighted prime moment has the expected limit. -/
theorem weighted_prime_sum_asymptotic :
    Tendsto (fun x : ℝ => weightedTheta x / x ^ 2) atTop (𝓝 (1 / 2)) :=
  weightedTheta_ratio_tendsto chebyshev_asymptotic

/-- Unconditional version of the integral limit for a single affine piece. -/
theorem affine_prime_sum_asymptotic
    (a b c d : ℝ) (hc : 0 < c) (hcd : c ≤ d) :
    Tendsto (fun x : ℝ =>
      (∑ p ∈ Finset.Ioc ⌊x / d⌋₊ ⌊x / c⌋₊ with p.Prime,
        (p : ℝ) * (a * (x / p) + b) * Real.log p) / x ^ 2)
      atTop (𝓝 (∫ t in c..d, (a * t + b) / t ^ 3)) :=
  reciprocal_affine_prime_sum_integral_tendsto chebyshev_asymptotic a b c d hc hcd

/-- Unconditional finite piecewise-affine prime-sum theorem used to assemble
the local limiting contributions in Section 5. -/
theorem finite_affine_prime_sum_asymptotic
    {ι : Type*} (S : Finset ι) (a b c d : ι → ℝ)
    (hc : ∀ i ∈ S, 0 < c i) (hcd : ∀ i ∈ S, c i ≤ d i) :
    Tendsto (fun x : ℝ =>
      (∑ i ∈ S, ∑ p ∈ Finset.Ioc ⌊x / d i⌋₊ ⌊x / c i⌋₊ with p.Prime,
        (p : ℝ) * (a i * (x / p) + b i) * Real.log p) / x ^ 2)
      atTop (𝓝 (∑ i ∈ S, ∫ t in c i..d i, (a i * t + b i) / t ^ 3)) :=
  finite_affine_pieces_tendsto chebyshev_asymptotic S a b c d hc hcd

#print axioms weighted_prime_sum_asymptotic
#print axioms affine_prime_sum_asymptotic
#print axioms finite_affine_prime_sum_asymptotic
#print axioms bounded_prime_errors_tendsto

end Zeta5PrimeSums
