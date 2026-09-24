import Mathlib.Algebra.Polynomial.DenomsClearable
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic

/-!
# A conditional formalization of the final argument in Zenodo 22826419

Source: Aabir Fauzan, "ζ(5) is irrational", 17 September 2026, v1.
https://zenodo.org/records/22826419

STATUS: This file does NOT prove that ζ(5) is irrational unconditionally.
It proves the final implication from the integer-polynomial estimates in
Theorem 2.1, and verifies the rational margins in equation (7.2).
The determinant construction and its estimates are not formalized here.
They are explicit hypotheses, not added axioms or hidden proof obligations.

Toolchain: Lean 4.32.2; dependency revisions are pinned in lake-manifest.json.
See README.md for the current status of the separate construction and
estimate modules. This file intentionally retains an independently checked
conditional reduction; the unconditional theorem must be assembled elsewhere.

-/

namespace Zeta5Reduction

/-- A polynomial family with degree at most `C * n` and positive evaluations
bounded by `exp (-c * n²)`, eventually. This is a hypothesis, not a construction. -/
def SmallPolynomialFamily (ξ : ℝ) (C : ℕ) (c : ℝ)
    (Q : ℕ → Polynomial ℤ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    (Q n).natDegree ≤ C * n ∧
    0 < Polynomial.eval ξ ((Q n).map (Int.castRingHom ℝ)) ∧
    Polynomial.eval ξ ((Q n).map (Int.castRingHom ℝ)) <
      Real.exp (-c * (n : ℝ) ^ 2)

/-- The degree-versus-decay criterion used in Sections 1.1 and 7. -/
theorem irrational_of_small_polynomial_family
    {ξ : ℝ} {C : ℕ} {c : ℝ} {Q : ℕ → Polynomial ℤ}
    (hc : 0 < c) (hQ : SmallPolynomialFamily ξ C c Q) :
    Irrational ξ := by
  rintro ⟨q, rfl⟩
  obtain ⟨N, hQ⟩ := hQ
  obtain ⟨n, hn⟩ := exists_nat_gt
    (max (N : ℝ) (max 0 ((C : ℝ) * Real.log (q.den : ℝ) / c)))
  have hnN : N ≤ n := by
    exact_mod_cast (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hn))
  have hn0 : (0 : ℝ) < n :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnc : (C : ℝ) * Real.log (q.den : ℝ) / c < n :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hnc' : (C : ℝ) * Real.log (q.den : ℝ) < (n : ℝ) * c :=
    (div_lt_iff₀ hc).mp hnc
  have hexponent : ((C * n : ℕ) : ℝ) * Real.log (q.den : ℝ) -
      c * (n : ℝ) ^ 2 < 0 := by
    push_cast
    nlinarith [mul_lt_mul_of_pos_right hnc' hn0]
  obtain ⟨hdeg, hpos, hsmall⟩ := hQ n hnN
  have hb : (0 : ℤ) < (q.den : ℤ) := by exact_mod_cast q.den_pos
  have hb1 : (1 : ℝ) ≤ q.den := by
    exact_mod_cast (Nat.succ_le_iff.mpr q.den_pos)
  have hb0 : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hrat : (q.num : ℝ) / (q.den : ℝ) = (q : ℝ) := by
    exact (Rat.cast_def q).symm
  have hlower := one_le_pow_mul_abs_eval_div
    (f := Q n) (a := q.num) (b := (q.den : ℤ)) (K := ℝ) hb
    (by
      have he : algebraMap ℤ ℝ = Int.castRingHom ℝ := Subsingleton.elim _ _
      simpa only [Int.cast_natCast, hrat, he] using ne_of_gt hpos)
  simp only [Int.cast_natCast, hrat] at hlower
  change 1 ≤ (q.den : ℝ) ^ (Q n).natDegree *
    |Polynomial.eval (q : ℝ) ((Q n).map (Int.castRingHom ℝ))| at hlower
  rw [abs_of_pos hpos] at hlower
  have hpow : (q.den : ℝ) ^ (Q n).natDegree ≤ (q.den : ℝ) ^ (C * n) :=
    pow_le_pow_right₀ hb1 hdeg
  have hlower' : 1 ≤ (q.den : ℝ) ^ (C * n) *
      Polynomial.eval (q : ℝ) ((Q n).map (Int.castRingHom ℝ)) :=
    hlower.trans (mul_le_mul_of_nonneg_right hpow hpos.le)
  have hupper := mul_lt_mul_of_pos_left hsmall (pow_pos hb0 (C * n))
  have hbound : (q.den : ℝ) ^ (C * n) * Real.exp (-c * (n : ℝ) ^ 2) < 1 := by
    rw [← Real.exp_log hb0, ← Real.exp_nat_mul, ← Real.exp_add]
    exact Real.exp_lt_one_iff.mpr (by simpa only [sub_eq_add_neg, neg_mul] using hexponent)
  exact (not_lt_of_ge hlower') (hupper.trans hbound)

/-- The actual real number targeted by the source paper. -/
noncomputable def zeta5 : ℝ := (riemannZeta (5 : ℂ)).re

/-- The target is the ordinary sum of reciprocal fifth powers.
The term at `n = 0` is zero under Lean's field division convention. -/
theorem zeta5_eq_series : zeta5 = ∑' n : ℕ, 1 / (n : ℝ) ^ 5 := by
  have hz : riemannZeta (5 : ℂ) = ∑' n : ℕ, 1 / (n : ℂ) ^ 5 := by
    simpa using (zeta_nat_eq_tsum_of_gt_one (by norm_num : 1 < (5 : ℕ)))
  have h : (riemannZeta (5 : ℂ)) =
      ((∑' n : ℕ, 1 / (n : ℝ) ^ 5 : ℝ) : ℂ) := by
    rw [hz, Complex.ofReal_tsum]
    simp only [Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_pow, Complex.ofReal_natCast]
  exact congrArg Complex.re h

/-- The precise unproved input needed from Theorem 2.1, equation (2.7). -/
def PaperPolynomialEstimates : Prop :=
  ∃ Q : ℕ → Polynomial ℤ, SmallPolynomialFamily zeta5 37 (139 / 5) Q

/-- Conditional only: proving `PaperPolynomialEstimates` is still required. -/
theorem irrational_zeta5_of_paper_estimates
    (h : PaperPolynomialEstimates) : Irrational zeta5 := by
  obtain ⟨Q, hQ⟩ := h
  exact irrational_of_small_polynomial_family (by norm_num) hQ

/-! ## Exact rational arithmetic from Sections 5 and 7

These theorems verify the arithmetic once the analytic estimates with these
constants have been obtained. They do not prove those analytic estimates.
-/

def lambda : ℚ := 37 / 40

def aStar : ℚ :=
  9928298118277006344769 / 7535670527041937280000

def normalizationBound (M : ℚ) : ℚ :=
  aStar + 7 * lambda / M - (2923 / 240 - 1 / 4) / M ^ 2 + 32 / M ^ 3

def realBound : ℚ := -2733991 / 2000000

/-- The identity used to combine equations (5.16), (5.18), and (5.19). -/
theorem aStar_identity :
    aStar = 127751 / 96000 - 2689 / 48000 +
      322437603634266857629 / 7535670527041937280000 := by
  norm_num [aStar]

/-- The first exact margin displayed in Appendix B.3. -/
theorem cutoff_200_margin :
    -1600 * (normalizationBound 200 + realBound) - 139 / 5 =
      3089837638249482469 / 58872425992515135000 := by
  norm_num [normalizationBound, aStar, lambda, realBound]

/-- The second exact margin displayed in Appendix B.3. -/
theorem cutoff_100000_margin :
    -1600 * (normalizationBound 100000 + realBound) - 7907 / 100 =
      29873543950273155160680943 / 3679526624532195937500000000 := by
  norm_num [normalizationBound, aStar, lambda, realBound]

/-- Equation (7.2), first inequality. -/
theorem cutoff_200_decay :
    (139 : ℚ) / 5 < -1600 * (normalizationBound 200 + realBound) := by
  norm_num [normalizationBound, aStar, lambda, realBound]

/-- Equation (7.2), second inequality. -/
theorem cutoff_100000_decay :
    (7907 : ℚ) / 100 < -1600 * (normalizationBound 100000 + realBound) := by
  norm_num [normalizationBound, aStar, lambda, realBound]

/-- The simplified allocation estimate may lose `1/36` in the normalized
logarithm while retaining ample strictly negative quadratic decay. -/
theorem relaxed_allocation_decay :
    (34 : ℚ) < -1600 * (normalizationBound 100000 + 1/36 + realBound) := by
  norm_num [normalizationBound, aStar, lambda, realBound]

/-- The two arithmetic identities used in Appendix C.2. -/
theorem approximation_exponent_margins :
    (6933 : ℚ) / 500 * (75 / 4) - 260 = -1 / 80 ∧
      (79 : ℚ) / 1600 - lambda / (75 / 4) = 1 / 24000 := by
  norm_num [lambda]

/-! The following commands expose all logical axioms used by the main results.
Only the standard Lean/mathlib foundations should occur; no `sorryAx` or
new axiom for any claim in the paper is permitted.
-/

#print axioms irrational_of_small_polynomial_family
#print axioms irrational_zeta5_of_paper_estimates
#print axioms zeta5_eq_series
#print axioms cutoff_200_decay
#print axioms cutoff_100000_decay

end Zeta5Reduction
