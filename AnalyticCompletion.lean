import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# Analytic completion used in Lemma 3.1

This file verifies convergence and the nonarchimedean norm estimates for the
series that define the extended functional. The moment bound on the kernel is
an explicit input. Instantiating it with the Bernoulli moments requires the
von Staudt–Clausen theorem, separately from these analytic arguments.
-/

namespace Zeta5Local
open Filter Topology IsUltrametricDist

variable {p : ℕ} [Fact p.Prime]

/-- A bounded coefficient kernel defines a convergent functional on every
restricted power series (a coefficient sequence tending to zero). -/
theorem bounded_kernel_summable (f κ : ℕ → ℚ_[p]) (C : ℝ)
    (hf : Tendsto f atTop (𝓝 0)) (hκ : ∀ n, ‖κ n‖ ≤ C) :
    Summable (fun n => f n * κ n) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop]
  apply squeeze_zero_norm (a := fun n => ‖f n‖ * C)
  · intro n
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hκ n) (norm_nonneg _)
  · simpa using hf.norm.mul_const C

/-- The extended functional has operator norm at most the bound of its
kernel; the statement avoids choosing a particular Tate-algebra API. -/
theorem bounded_kernel_norm (f κ : ℕ → ℚ_[p]) (B C : ℝ)
    (hB : 0 ≤ B) (hf : ∀ n, ‖f n‖ ≤ B) (hκ : ∀ n, ‖κ n‖ ≤ C) :
    ‖∑' n, f n * κ n‖ ≤ B * C := by
  apply (norm_tsum_le _).trans
  apply ciSup_le
  intro n
  rw [norm_mul]
  exact mul_le_mul (hf n) (hκ n) (norm_nonneg _) hB

/-- Uniform errors in coefficients give uniform errors in the extended
functional, proving continuity in the coefficient supremum norm. -/
theorem bounded_kernel_difference (f g κ : ℕ → ℚ_[p]) (B C : ℝ)
    (hB : 0 ≤ B)
    (hf : Tendsto f atTop (𝓝 0)) (hg : Tendsto g atTop (𝓝 0))
    (hfg : ∀ n, ‖f n - g n‖ ≤ B) (hκ : ∀ n, ‖κ n‖ ≤ C) :
    ‖(∑' n, f n * κ n) - (∑' n, g n * κ n)‖ ≤ B * C := by
  rw [← (bounded_kernel_summable f κ C hf hκ).tsum_sub
    (bounded_kernel_summable g κ C hg hκ)]
  simp_rw [← sub_mul]
  exact bounded_kernel_norm (fun n => f n - g n) κ B C hB hfg hκ

/-- Factors `p^j` absorb a possible loss of one power of `p`.
The initial term must already be integral, exactly as in Lemma 3.1. -/
theorem p_power_absorbs_loss (u : ℕ → ℚ_[p])
    (hzero : ‖u 0‖ ≤ 1) (hu : ∀ j, ‖u j‖ ≤ (p : ℝ)) :
    Summable (fun j => (p : ℚ_[p]) ^ j * u j) ∧
      ‖∑' j, (p : ℚ_[p]) ^ j * u j‖ ≤ 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hnorm : ‖(p : ℚ_[p])‖ * (p : ℝ) = 1 := by
    rw [Padic.norm_p]
    exact inv_mul_cancel₀ hp0.ne'
  have hpow : Tendsto (fun j : ℕ => (p : ℚ_[p]) ^ j) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one
  constructor
  · exact bounded_kernel_summable _ u p hpow hu
  · apply (norm_tsum_le _).trans
    apply ciSup_le
    intro j
    cases j with
    | zero => simpa using hzero
    | succ j =>
      rw [norm_mul, norm_pow]
      calc
        _ ≤ ‖(p : ℚ_[p])‖ ^ (j + 1) * (p : ℝ) :=
          mul_le_mul_of_nonneg_left (hu _) (by positivity)
        _ = ‖(p : ℚ_[p])‖ ^ j := by rw [pow_succ, mul_assoc, hnorm, mul_one]
        _ ≤ 1 := pow_le_one₀ (norm_nonneg _) Padic.norm_p_lt_one.le

/-- Integral principal-part contributions may be added without introducing
an additional factor: the p-adic norm uses the maximum, not the sum. -/
theorem integral_analytic_plus_principal_parts {ι : Type*} (s : Finset ι)
    (a : ℚ_[p]) (c : ι → ℚ_[p]) (ha : ‖a‖ ≤ 1)
    (hc : ∀ i ∈ s, ‖c i‖ ≤ 1) :
    ‖a + ∑ i ∈ s, c i‖ ≤ 1 := by
  exact (norm_add_le_max _ _).trans
    (max_le ha (norm_sum_le_of_forall_le_of_nonneg (by norm_num) hc))

#print axioms bounded_kernel_summable
#print axioms p_power_absorbs_loss
end Zeta5Local
