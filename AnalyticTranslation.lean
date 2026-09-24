import AnalyticFarPoles
import PolynomialDistribution

/-! Analytic continuation of the translation identity to far poles. -/
namespace Zeta5Local
open Filter Topology IsUltrametricDist Polynomial
variable {p : ℕ} [Fact p.Prime]

/-- Uniform decay by the first index controls a triangular p-adic double
series, without an archimedean factor counting its terms. -/
theorem summable_triangular (f : ℕ × ℕ → ℚ_[p]) (b : ℕ → ℝ)
    (hb : Tendsto b atTop (𝓝 0))
    (hzero : ∀ n k, n < k → f (n, k) = 0)
    (hbound : ∀ n k, k ≤ n → ‖f (n, k)‖ ≤ b n) : Summable f := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hb.eventually (Iio_mem_nhds hε))
  rw [eventually_cofinite]
  apply ((Finset.range N ×ˢ Finset.range N).finite_toSet).subset
  rintro ⟨n, k⟩ hbad
  by_contra hnot
  have hout : ¬(n < N ∧ k < N) := by simpa only [Finset.mem_coe,
    Finset.mem_product, Finset.mem_range] using hnot
  apply hbad
  rw [dist_zero_right]
  by_cases hk : k ≤ n
  · have hn : N ≤ n := by omega
    exact (hbound n k hk).trans_lt (hN n hn)
  · rw [hzero n k (by omega), norm_zero]
    exact hε

/-- Binomially expanded affine powers can be summed in either index. -/
theorem summable_binomial_kernel (hp7 : 7 ≤ p) (q : ℚ_[p]) (hq : ‖q‖ < 1) :
    Summable (fun nk : ℕ × ℕ => (nk.1.choose nk.2 : ℚ_[p]) *
      q ^ (nk.1 + 1) * (rationalTauMoment nk.2 : ℚ_[p])) := by
  apply summable_triangular _ (fun n => ‖q‖ ^ (n + 1) * (p : ℝ))
  · have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq).mul_const ‖q‖
    simpa only [zero_mul, ← pow_succ] using h.mul_const (p : ℝ)
  · intro n k hk
    simp [Nat.choose_eq_zero_of_lt hk]
  · intro n k hk
    rw [norm_mul, norm_mul, norm_pow]
    have hc : ‖(n.choose k : ℚ_[p])‖ ≤ 1 := by
      simpa using Padic.norm_int_le_one (n.choose k : ℤ)
    have hcoeff := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ ‖q‖ ^ (n + 1))
    simp only [one_mul] at hcoeff
    exact mul_le_mul hcoeff (rationalTauMoment_norm hp7 k) (norm_nonneg _) (by positivity)

lemma rationalTauFunctional_X_pow (n : ℕ) :
    rationalTauFunctional ((Polynomial.X : ℚ[X]) ^ n) = rationalTauMoment n := by
  simpa only [Polynomial.monomial_one_right_eq_X_pow, one_mul] using
    rationalTauFunctional_monomial n 1

/-- The coefficient identity that makes analytic pole translation work. -/
theorem kernel_binomial_relation (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * rationalTauMoment k =
      rationalTauMoment n + if n = 4 then 1 else 0 := by
  have h := rationalTauFunctional_translation ((Polynomial.X : ℚ[X]) ^ n)
  rw [Polynomial.X_pow_comp] at h
  norm_num [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative,
    Polynomial.coeff_X_pow] at h
  rw [← map_sub, Polynomial.one_add_X_pow_sub_X_pow, map_sum] at h
  simp only [← Nat.cast_smul_eq_nsmul ℚ, map_smul, rationalTauFunctional_X_pow,
    smul_eq_mul] at h
  rw [Finset.sum_range_succ, h]
  simp only [Nat.choose_self, Nat.cast_one, one_mul]
  by_cases hn : n = 4 <;> simp [hn, eq_comm] <;> ring

lemma hasSum_binomial_power (q : ℚ_[p]) (hq : ‖q‖ < 1) (k : ℕ) :
    HasSum (fun n : ℕ => (n.choose k : ℚ_[p]) * q ^ (n + 1))
      ((q / (1 - q)) ^ (k + 1)) := by
  have ht : HasSum (fun n : ℕ => ((n + k).choose k : ℚ_[p]) * q ^ (n + k + 1))
      ((q / (1 - q)) ^ (k + 1)) := by
    have hh := (hasSum_choose_mul_geometric_of_norm_lt_one k hq).mul_right (q ^ (k + 1))
    convert! hh using 1
    · funext n
      rw [mul_assoc, ← pow_add]
      congr 2
    · rw [div_pow]
      ring
  have hs : Summable (fun n : ℕ => (n.choose k : ℚ_[p]) * q ^ (n + 1)) :=
    (summable_nat_add_iff k).mp ht.summable
  have hz : ∑ n ∈ Finset.range k, (n.choose k : ℚ_[p]) * q ^ (n + 1) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hn)]
  have he := hs.sum_add_tsum_nat_add k
  rw [hz, zero_add, ht.tsum_eq] at he
  exact he ▸ hs.hasSum

noncomputable def kernelSeries (q : ℚ_[p]) : ℚ_[p] :=
  ∑' n : ℕ, q ^ (n + 1) * (rationalTauMoment n : ℚ_[p])

lemma kernelSeries_summable (hp7 : 7 ≤ p) (q : ℚ_[p]) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => q ^ (n + 1) * (rationalTauMoment n : ℚ_[p])) := by
  apply bounded_kernel_summable _ _ p _ (rationalTauMoment_norm hp7)
  have h := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).mul_const q
  simpa only [zero_mul, ← pow_succ] using h

set_option maxHeartbeats 400000 in
/-- The binomial transform gives the required analytic continuation under
translation. Double-series rearrangement is justified p-adically above. -/
theorem kernelSeries_translation (hp7 : 7 ≤ p) (q : ℚ_[p]) (hq : ‖q‖ < 1) :
    kernelSeries (q / (1 - q)) = kernelSeries q + q ^ 5 := by
  have hn (n : ℕ) : (∑' k : ℕ, (n.choose k : ℚ_[p]) * q ^ (n + 1) *
      (rationalTauMoment k : ℚ_[p])) =
      q ^ (n + 1) * ((rationalTauMoment n : ℚ_[p]) + if n = 4 then 1 else 0) := by
    rw [tsum_eq_sum (s := Finset.range (n + 1)) (fun k hk => by
      have hnk : n < k := by
        have hh : n + 1 ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
        omega
      simp [Nat.choose_eq_zero_of_lt hnk])]
    have hcoeff : (∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ_[p]) *
        (rationalTauMoment k : ℚ_[p])) =
        (rationalTauMoment n : ℚ_[p]) + if n = 4 then 1 else 0 := by
      have hh := congrArg (fun x : ℚ => (x : ℚ_[p])) (kernel_binomial_relation n)
      push_cast at hh
      simpa only [apply_ite, Rat.cast_one, Rat.cast_zero] using hh
    rw [← hcoeff, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hk (k : ℕ) : (∑' n : ℕ, (n.choose k : ℚ_[p]) * q ^ (n + 1) *
      (rationalTauMoment k : ℚ_[p])) =
      (q / (1 - q)) ^ (k + 1) * (rationalTauMoment k : ℚ_[p]) :=
    ((hasSum_binomial_power q hq k).mul_right _).tsum_eq
  let f : ℕ → ℕ → ℚ_[p] := fun n k => (n.choose k : ℚ_[p]) * q ^ (n + 1) *
    (rationalTauMoment k : ℚ_[p])
  have hf : Summable (Function.uncurry f) := summable_binomial_kernel hp7 q hq
  have hc := Summable.tsum_comm (f := f) hf
  change (∑' k : ℕ, ∑' n : ℕ, (n.choose k : ℚ_[p]) * q ^ (n + 1) *
      (rationalTauMoment k : ℚ_[p])) =
      ∑' n : ℕ, ∑' k : ℕ, (n.choose k : ℚ_[p]) * q ^ (n + 1) *
        (rationalTauMoment k : ℚ_[p]) at hc
  simp_rw [hn, hk] at hc
  change kernelSeries (q / (1 - q)) = _ at hc
  rw [hc]
  have hterms (n : ℕ) : q ^ (n + 1) *
      ((rationalTauMoment n : ℚ_[p]) + if n = 4 then 1 else 0) =
      q ^ (n + 1) * (rationalTauMoment n : ℚ_[p]) + if n = 4 then q ^ 5 else 0 := by
    split_ifs with h
    · subst n
      ring
    · simp
  simp_rw [hterms]
  have hd : Summable (fun n : ℕ => if n = 4 then q ^ 5 else 0) :=
    (hasSum_ite_eq 4 (q ^ 5)).summable
  rw [(kernelSeries_summable hp7 q hq).tsum_add hd]
  simp [kernelSeries]

lemma analyticPoleValue_eq_kernelSeries (s : ℚ_[p]) :
    analyticPoleValue s = -kernelSeries s⁻¹ := by
  simp only [analyticPoleValue, kernelSeries, neg_mul, tsum_neg]

/-- The analytic far-pole functional satisfies the same translation
identity as the polynomial and integer-pole parts. -/
theorem analyticPoleValue_translation (hp7 : 7 ≤ p) (s : ℚ_[p])
    (hs0 : s ≠ 0) (hs : ‖s⁻¹‖ < 1) :
    analyticPoleValue (s - 1) - analyticPoleValue s = -(s⁻¹ ^ 5) := by
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have he : s = 1 := sub_eq_zero.mp h
    simp [he] at hs
  have hfrac : s⁻¹ / (1 - s⁻¹) = (s - 1)⁻¹ := by
    field_simp
  rw [analyticPoleValue_eq_kernelSeries, analyticPoleValue_eq_kernelSeries,
    ← hfrac, kernelSeries_translation hp7 s⁻¹ hs]
  ring

#print axioms analyticPoleValue_translation

end Zeta5Local
