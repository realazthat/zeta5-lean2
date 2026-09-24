import FarUnitPowerSeries

namespace Zeta5Local
open Polynomial
open scoped PowerSeries.WithPiTopology
variable {p : ℕ} [Fact p.Prime]

/-- Split off the low-degree reduction of the numerator. Every coefficient
of the unrestricted higher-degree tail carries an additional p. -/
noncomputable def splitFarExpansion (A₀ A₁ V : Polynomial ℚ_[p]) (u : ℚ_[p]) :
    ℕ → Polynomial ℚ_[p]
  | 0 => farUnitExpansion A₀ V u 0
  | j + 1 => farUnitExpansion A₀ V u (j + 1) + farUnitExpansion A₁ V u j

lemma splitFarExpansion_integral (A₀ A₁ V : Polynomial ℚ_[p]) (u : ℚ_[p])
    (hA₀ : ∀ n, ‖A₀.coeff n‖ ≤ 1) (hA₁ : ∀ n, ‖A₁.coeff n‖ ≤ 1)
    (hV : ∀ n, ‖V.coeff n‖ ≤ 1) (hu : ‖u‖ = 1) (j n : ℕ) :
    ‖(splitFarExpansion A₀ A₁ V u j).coeff n‖ ≤ 1 := by
  cases j with
  | zero => exact farUnitExpansion_integral A₀ V u hA₀ hV hu 0 n
  | succ j =>
      exact integralCoeffs_add (farUnitExpansion_integral A₀ V u hA₀ hV hu (j+1))
        (farUnitExpansion_integral A₁ V u hA₁ hV hu j) n

lemma splitFarExpansion_zero_degree (A₀ A₁ V : Polynomial ℚ_[p]) (u : ℚ_[p]) :
    (splitFarExpansion A₀ A₁ V u 0).natDegree ≤ A₀.natDegree :=
  farUnitExpansion_zero_degree A₀ V u

lemma hasSum_split_sequence {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (f g h : ℕ → R) (c F G : R)
    (hz : h 0 = f 0) (hs : ∀ j, h (j+1) = f (j+1) + c*g j)
    (hf : HasSum f F) (hg : HasSum g G) : HasSum h (F+c*G) := by
  have hft : HasSum (fun j => f (j+1)) (F-f 0) := by
    simpa using (hasSum_nat_add_iff' 1).mpr hf
  apply (hasSum_nat_add_iff' 1).mp
  simp only [Finset.sum_range_one, hz]
  convert! hft.add (hg.mul_left c) using 1
  · funext j
    exact hs j
  · ring

/-- Exact coefficient-completion identity for the split expansion. -/
theorem splitFarExpansion_powerSeries (A₀ A₁ V : Polynomial ℚ_[p]) (u : ℚ_[p])
    (hA₀ : ∀ n, ‖A₀.coeff n‖ ≤ 1) (hA₁ : ∀ n, ‖A₁.coeff n‖ ≤ 1)
    (hV : ∀ n, ‖V.coeff n‖ ≤ 1) (hu : ‖u‖ = 1) :
    weightedPolynomialSeries (splitFarExpansion A₀ A₁ V u) =
      weightedPolynomialSeries (farUnitExpansion A₀ V u) +
      PowerSeries.C (p : ℚ_[p]) * weightedPolynomialSeries (farUnitExpansion A₁ V u) := by
  apply HasSum.tsum_eq
  apply hasSum_split_sequence
    (fun j => ((C ((p : ℚ_[p])^j)*farUnitExpansion A₀ V u j : Polynomial ℚ_[p]) : PowerSeries ℚ_[p]))
    (fun j => ((C ((p : ℚ_[p])^j)*farUnitExpansion A₁ V u j : Polynomial ℚ_[p]) : PowerSeries ℚ_[p]))
    _ (PowerSeries.C (p : ℚ_[p]))
  · rfl
  · intro j
    simp only [splitFarExpansion, mul_add, coe_add, coe_mul, coe_C, pow_succ, map_mul]
    ring
  · exact (weightedPolynomialSeries_summable _ (farUnitExpansion_integral A₀ V u hA₀ hV hu)).hasSum
  · exact (weightedPolynomialSeries_summable _ (farUnitExpansion_integral A₁ V u hA₁ hV hu)).hasSum

/-- Both the original numerator and denominator survive the completed
expansion exactly, despite the unrestricted degree of A₁. -/
theorem splitFarExpansion_identity (A₀ A₁ V : Polynomial ℚ_[p]) (u : ℚ_[p])
    (hA₀ : ∀ n, ‖A₀.coeff n‖ ≤ 1) (hA₁ : ∀ n, ‖A₁.coeff n‖ ≤ 1)
    (hV : ∀ n, ‖V.coeff n‖ ≤ 1) (hu : ‖u‖ = 1) :
    ((C u + C (p : ℚ_[p]) * V : Polynomial ℚ_[p]) : PowerSeries ℚ_[p]) *
      weightedPolynomialSeries (splitFarExpansion A₀ A₁ V u) =
      ((A₀ + C (p : ℚ_[p]) * A₁ : Polynomial ℚ_[p]) : PowerSeries ℚ_[p]) := by
  rw [splitFarExpansion_powerSeries A₀ A₁ V u hA₀ hA₁ hV hu, mul_add,
    farUnitExpansion_powerSeries_identity A₀ V u hA₀ hV hu]
  rw [mul_left_comm, farUnitExpansion_powerSeries_identity A₁ V u hA₁ hV hu]
  simp only [coe_add, coe_mul, coe_C]

/-- Values at every integral near root have the correct convergent sum. -/
theorem splitFarExpansion_hasSum (A₀ A₁ V : Polynomial ℚ_[p]) (u x : ℚ_[p])
    (hV : ∀ n, ‖V.coeff n‖ ≤ 1) (hu : ‖u‖ = 1) (hx : ‖x‖ ≤ 1) :
    HasSum (fun j => (p : ℚ_[p])^j * (splitFarExpansion A₀ A₁ V u j).eval x)
      ((A₀ + C (p : ℚ_[p]) * A₁).eval x / (u + p * V.eval x)) := by
  have hh := hasSum_split_sequence
    (fun j => (p : ℚ_[p])^j * (farUnitExpansion A₀ V u j).eval x)
    (fun j => (p : ℚ_[p])^j * (farUnitExpansion A₁ V u j).eval x)
    (fun j => (p : ℚ_[p])^j * (splitFarExpansion A₀ A₁ V u j).eval x)
    (p : ℚ_[p]) _ _ rfl (fun j => by simp only [splitFarExpansion, eval_add, pow_succ]; ring)
    (farUnitExpansion_hasSum A₀ V u x hV hu hx) (farUnitExpansion_hasSum A₁ V u x hV hu hx)
  convert! hh using 1
  simp only [eval_add, eval_mul, eval_C]
  ring

#print axioms splitFarExpansion_identity
#print axioms splitFarExpansion_hasSum
end Zeta5Local
