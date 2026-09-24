import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Exact rational certificates for logarithms, using repeated squaring.+No transcendental computation enters the trusted checker. -/
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta5LogCertificates

def rootChain (q : ℚ) : List ℚ → Bool
  | [] => decide (0 < q)
  | r :: rs => decide (0 < q ∧ 0 < r ∧ q ≤ r^2) && rootChain r rs

def upperBound (q : ℚ) : List ℚ → ℚ
  | [] => q - 1
  | r :: rs => 2 * upperBound r rs

def upperCheck (q : ℚ) (rs : List ℚ) (b : ℚ) : Bool :=
  rootChain q rs && decide (upperBound q rs ≤ b)

theorem log_le_upperBound (q : ℚ) (rs : List ℚ) (h : rootChain q rs = true) :
    Real.log (q : ℝ) ≤ (upperBound q rs : ℝ) := by
  induction rs generalizing q with
  | nil =>
    have hq : 0 < q := by simpa [rootChain] using h
    simpa [upperBound] using Real.log_le_sub_one_of_pos (show (0 : ℝ) < q by exact_mod_cast hq)
  | cons r rs ih =>
    have hh : (0 < q ∧ 0 < r ∧ q ≤ r^2) ∧ rootChain r rs = true := by
      simpa only [rootChain, Bool.and_eq_true, decide_eq_true_eq] using h
    have hqr : Real.log (q : ℝ) ≤ 2 * Real.log (r : ℝ) := by
      have hlog := Real.log_le_log (show (0 : ℝ) < q by exact_mod_cast hh.1.1)
        (show (q : ℝ) ≤ (r : ℝ)^2 by exact_mod_cast hh.1.2.2)
      simpa only [Real.log_pow, Nat.cast_ofNat] using hlog
    calc Real.log (q : ℝ) ≤ 2 * Real.log (r : ℝ) := hqr
      _ ≤ 2 * (upperBound r rs : ℝ) := mul_le_mul_of_nonneg_left (ih r hh.2) (by norm_num)
      _ = (upperBound q (r :: rs) : ℝ) := by simp [upperBound]

theorem log_le_of_check (q b : ℚ) (rs : List ℚ) (h : upperCheck q rs b = true) :
    Real.log (q : ℝ) ≤ (b : ℝ) := by
  have hh : rootChain q rs = true ∧ upperBound q rs ≤ b := by
    simpa only [upperCheck, Bool.and_eq_true, decide_eq_true_eq] using h
  exact (log_le_upperBound q rs hh.1).trans (by exact_mod_cast hh.2)

theorem le_log_of_check (q b : ℚ) (rs : List ℚ)
    (h : upperCheck q⁻¹ rs (-b) = true) : (b : ℝ) ≤ Real.log (q : ℝ) := by
  have hh := log_le_of_check q⁻¹ (-b) rs h
  simpa only [Rat.cast_inv, Rat.cast_neg, Real.log_inv, neg_le_neg_iff] using hh

end Zeta5LogCertificates
