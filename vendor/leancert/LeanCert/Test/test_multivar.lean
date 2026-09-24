import LeanCert.Tactic.IntervalAuto

-- Test: x + y ≤ 2 on [0,1] × [0,1]
theorem test_2d_sum_le : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1, x + y ≤ (2 : ℚ) := by
  multivariate_bound
