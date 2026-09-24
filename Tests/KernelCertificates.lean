import LeanCert.Tactic.IntervalAuto.PointIneq

/-! Regression checks for the Lean 4.35 kernel-only certificate adapter. -/

set_option maxHeartbeats 0

/-- A transcendental bound must produce a kernel-checkable proof. -/
theorem kernel_log_two_positive : (0 : ℝ) < Real.log 2 := by
  interval_decide 15 (trust := kernel)

/-- A false certificate must fail rather than introduce a trusted assumption. -/
example : True := by
  fail_if_success
    have : Real.log 2 < (0 : ℝ) := by
      interval_decide 15 (trust := kernel)
  trivial

#print axioms kernel_log_two_positive
