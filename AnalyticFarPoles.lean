import BernoulliKernel
import AnalyticCompletion

/-! Convergence of the analytic far-pole expansion and integrality of the
parameter used in distribution. The norm bound on C_p proved here is the
integrality needed in Lemma3.1; the stronger p^5 divisibility is not claimed. -/
namespace Zeta5Local
open Filter Topology IsUltrametricDist
variable {p : ℕ} [Fact p.Prime]

noncomputable def analyticPoleValue (s : ℚ_[p]) : ℚ_[p] :=
  ∑' n : ℕ, -(s⁻¹ ^ (n + 1)) * (rationalTauMoment n : ℚ_[p])

lemma farPole_coefficients_tendsto (s : ℚ_[p]) (hs : ‖s⁻¹‖ < 1) :
    Tendsto (fun n : ℕ => -(s⁻¹ ^ (n + 1))) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hs).mul_const s⁻¹
  simpa only [zero_mul, neg_zero, ← pow_succ] using h.neg

theorem analyticPole_summable (hp7 : 7 ≤ p) (s : ℚ_[p]) (hs : ‖s⁻¹‖ < 1) :
    Summable (fun n : ℕ => -(s⁻¹ ^ (n + 1)) * (rationalTauMoment n : ℚ_[p])) :=
  bounded_kernel_summable _ _ p (farPole_coefficients_tendsto s hs)
    (rationalTauMoment_norm hp7)

theorem analyticPole_norm (hp7 : 7 ≤ p) (s : ℚ_[p]) (hs : ‖s⁻¹‖ ≤ 1) :
    ‖analyticPoleValue s‖ ≤ ‖s⁻¹‖ * (p : ℝ) := by
  apply bounded_kernel_norm _ _ _ _ (norm_nonneg _)
  · intro n
    rw [norm_neg, norm_pow, pow_succ]
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hs)
  · exact rationalTauMoment_norm hp7

lemma farResidue_inverse_norm (a : ℕ) (ha : 0 < a) (hap : a < p) :
    ‖(-((a : ℚ_[p]) / (p : ℚ_[p])))⁻¹‖ = (p : ℝ)⁻¹ := by
  have hp : p.Prime := Fact.out
  have hcop : a.Coprime p :=
    (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt ha hap)).symm
  have haunit : ‖(a : ℚ_[p])‖ = 1 := Padic.norm_natCast_eq_one_iff.mpr hcop.symm
  rw [norm_inv, norm_neg, norm_div, haunit, Padic.norm_p]
  simp

/-- Every analytic far-pole term used in the distribution constant is
integral; this conclusion uses the complete functional kernel. -/
theorem farResidue_integral (hp7 : 7 ≤ p) (a : ℕ) (ha : 0 < a) (hap : a < p) :
    ‖analyticPoleValue (-((a : ℚ_[p]) / (p : ℚ_[p])))‖ ≤ 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hnorm := farResidue_inverse_norm (p := p) a ha hap
  have hle : ‖(-((a : ℚ_[p]) / (p : ℚ_[p])))⁻¹‖ ≤ 1 := by
    rw [hnorm]
    exact (inv_lt_one_of_one_lt₀ hp1).le
  have hh := analyticPole_norm hp7 (-((a : ℚ_[p]) / (p : ℚ_[p]))) hle
  rw [hnorm, inv_mul_cancel₀ (by positivity : (p : ℝ) ≠ 0)] at hh
  exact hh

noncomputable def distributionConstant (p : ℕ) [Fact p.Prime] : ℚ_[p] :=
  ∑ a ∈ Finset.Ico 1 p, analyticPoleValue (-((a : ℚ_[p]) / (p : ℚ_[p])))

theorem distributionConstant_integral (hp7 : 7 ≤ p) :
    ‖distributionConstant p‖ ≤ 1 := by
  apply norm_sum_le_of_forall_le_of_nonneg (by norm_num)
  intro a ha
  have h := Finset.mem_Ico.mp ha
  exact farResidue_integral hp7 a (by omega) h.2

/-- The substituted parameter Y=p^5X+C_p has integral coefficients. -/
theorem distributionParameter_integral (hp7 : 7 ≤ p) (n : ℕ) :
    ‖((Polynomial.C ((p : ℚ_[p]) ^ 5) * Polynomial.X +
      Polynomial.C (distributionConstant p)).coeff n)‖ ≤ 1 := by
  rw [Polynomial.coeff_add]
  apply (norm_add_le_max _ _).trans
  apply max_le
  · rw [Polynomial.coeff_C_mul]
    by_cases hn : n = 1
    · subst n
      simp only [Polynomial.coeff_X_one, mul_one, norm_pow]
      exact pow_le_one₀ (norm_nonneg _) Padic.norm_p_lt_one.le
    · simp [Polynomial.coeff_X, Ne.symm hn]
  · simp only [Polynomial.coeff_C]
    split_ifs
    · exact distributionConstant_integral hp7
    · norm_num

#print axioms analyticPole_summable
#print axioms distributionParameter_integral
end Zeta5Local
