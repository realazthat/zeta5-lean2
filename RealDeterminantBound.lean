import RealDeterminantEnergyBridge
import PotentialFieldCertificate

noncomputable section
open scoped BigOperators Topology
open MeasureTheory Set Filter

namespace Zeta5Construction

lemma eventually_sourceEnergyBound (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, SourceEnergyBound paperRealCoefficient η n :=
  eventually_sourceEnergyBound_of_discrete η
    (Zeta5ArcsineMixture.eventually_discrete_energy_bound η hη)

/-- The real determinant estimate needed by the final irrationality argument.
Every analytic and numerical hypothesis has been discharged. -/
theorem actual_eventually_normalizedDeterminant_log_upper (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      Real.log ((normalizedDeterminant (3*n) (37*n)).eval₂ (Rat.castHom ℝ) zetaSeries) ≤
        (-(2733991/2000000:ℝ)+ε)*(40*n:ℝ)^2 := by
  filter_upwards [eventually_normalizedDeterminant_log_upper_of_energy
    eventually_sourceEnergyBound ε hε] with n hn
  exact hn.trans (mul_le_mul_of_nonneg_right (by linarith [paperRealCoefficient_lt]) (sq_nonneg _))

theorem actual_eventually_normalizedDeterminant_positive_log_upper (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      0 < (normalizedDeterminant (3*n) (37*n)).eval₂ (Rat.castHom ℝ) zetaSeries ∧
      Real.log ((normalizedDeterminant (3*n) (37*n)).eval₂ (Rat.castHom ℝ) zetaSeries) ≤
        (-(2733991/2000000:ℝ)+ε)*(40*n:ℝ)^2 := by
  filter_upwards [actual_eventually_normalizedDeterminant_log_upper ε hε] with n hn
  exact ⟨normalizedDeterminant_eval_pos (3*n) (37*n), hn⟩

#print axioms actual_eventually_normalizedDeterminant_log_upper

end Zeta5Construction

