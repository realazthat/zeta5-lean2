import GramUpperBound
import RealRemainder

noncomputable section
open scoped BigOperators Topology
open MeasureTheory Set Filter

namespace Zeta5Construction

/-- The energy estimate, specialized to the paper's N=3n, h=37n, K=40n. -/
def SourceEnergyBound (E η : ℝ) (n : ℕ) : Prop :=
  ∀ t : Fin (37*n) → ℝ, (∀ i, 0 < t i) → Function.Injective t →
    2*∑ i, ∑ j ∈ Finset.Ioi i, Real.log |t i-t j| -
      (40*n:ℝ)*∑ i, externalField (3/40) (t i)+∑ i, Real.sqrt (t i) ≤
        (E+2*(37/40)*η+(37/40)*Real.sqrt 2/(40*n))*(40*n:ℝ)^2+
          (37*n:ℝ)*Real.log ((40*n:ℝ)+1)

theorem log_normalizedDeterminant_upper_of_sourceEnergy {n : ℕ} (hn : 0 < n)
    {E η : ℝ} (henergy : SourceEnergyBound E η n) :
    Real.log ((normalizedDeterminant (3*n) (37*n)).eval₂ (Rat.castHom ℝ) zetaSeries) ≤
      (E+normalizationConstant (3/40) (37/40)+2*(37/40)*η+
        realDeterminantRemainder (40*n))*(40*n:ℝ)^2 := by
  have hnp : (0:ℝ)<n := by exact_mod_cast hn
  have hNr : ((3*n:ℕ):ℝ)/(40*n)=3/40 := by push_cast; field_simp
  have hbound := log_normalizedDeterminant_upper_of_energy
    (N := 3*n) (h := 37*n) (K := (40*n:ℝ)) (α := 3/40) (lam := 37/40)
    (by omega) (by omega) (by push_cast; ring)
    (by norm_num) (by norm_num) (by norm_num)
    (by push_cast; ring) (by push_cast; ring)
    (B := (E+2*(37/40)*η+(37/40)*Real.sqrt 2/(40*n))*(40*n:ℝ)^2+
      (37*n:ℝ)*Real.log ((40*n:ℝ)+1))
    (by
      intro t ht hinj
      rw [hNr]
      exact henergy t ht hinj)
  calc
    _ ≤ _ := hbound
    _ = _ := by
      unfold realDeterminantRemainder
      push_cast
      field_simp
      ring

/-- The real analytic reduction: arbitrarily small energy errors imply the
quadratic upper bound for the actual normalized determinants. -/
theorem eventually_normalizedDeterminant_log_upper_of_energy {E : ℝ}
    (henergy : ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, SourceEnergyBound E η n)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      Real.log ((normalizedDeterminant (3*n) (37*n)).eval₂ (Rat.castHom ℝ) zetaSeries) ≤
        (E+normalizationConstant (3/40) (37/40)+ε)*(40*n:ℝ)^2 := by
  have hr := realDeterminantRemainder_nat_tendsto.eventually_lt_const (half_pos hε)
  filter_upwards [henergy (ε/8) (by positivity), hr, eventually_ge_atTop 1] with n he hnR hn
  have hu := log_normalizedDeterminant_upper_of_sourceEnergy (by omega : 0<n) he
  apply hu.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  linarith

#print axioms eventually_normalizedDeterminant_log_upper_of_energy

end Zeta5Construction

