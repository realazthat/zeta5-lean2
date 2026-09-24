import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic

/-!
# The integral partial-fraction decomposition underlying Lemma3.1

Monic division preserves integral coefficients. Evaluation at integral roots,
and division by products of unit root differences, also preserve integrality.
These are unconditional results over the actual p-adic field.
-/
namespace Zeta5Local
open Polynomial IsUltrametricDist
variable {p : ℕ} [Fact p.Prime]

/-- Evaluation of an integral polynomial at an integral argument is integral. -/
theorem integral_polynomial_eval (P : Polynomial ℚ_[p]) (r : ℚ_[p])
    (hP : ∀ n, ‖P.coeff n‖ ≤ 1) (hr : ‖r‖ ≤ 1) : ‖P.eval r‖ ≤ 1 := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum]
  apply norm_sum_le_of_forall_le_of_nonneg (by norm_num)
  intro i hi
  rw [norm_mul, norm_pow]
  exact mul_le_one₀ (hP i) (by positivity) (pow_le_one₀ (norm_nonneg _) hr)

/-- The quotient and remainder in monic division have integral coefficients.
This is the non-expansion claim about polynomial division in Lemma3.1. -/
theorem integral_monic_division (P T : Polynomial ℚ_[p]) (hT : T.Monic)
    (hP : ∀ n, ‖P.coeff n‖ ≤ 1) (hTc : ∀ n, ‖T.coeff n‖ ≤ 1) :
    (∀ n, ‖(P /ₘ T).coeff n‖ ≤ 1) ∧
      (∀ n, ‖(P %ₘ T).coeff n‖ ≤ 1) := by
  let f := (PadicInt.subring p).subtype
  have liftP : P ∈ Polynomial.lifts f := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨P.coeff n, hP n⟩, rfl⟩
  have liftT : T ∈ Polynomial.lifts f := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨T.coeff n, hTc n⟩, rfl⟩
  obtain ⟨P', hP'⟩ := (Polynomial.mem_lifts P).mp liftP
  obtain ⟨T', hT'⟩ := (Polynomial.mem_lifts T).mp liftT
  have hTm : T'.Monic := Polynomial.monic_of_injective Subtype.val_injective
    (by rw [hT']; exact hT)
  constructor
  · intro n
    rw [← hP', ← hT', ← Polynomial.map_divByMonic f hTm, Polynomial.coeff_map]
    exact ((P' /ₘ T').coeff n).property
  · intro n
    rw [← hP', ← hT', ← Polynomial.map_modByMonic f hTm, Polynomial.coeff_map]
    exact ((P' %ₘ T').coeff n).property

/-- Polynomial division also preserves the initial degree restriction. -/
theorem monic_quotient_natDegree_le (P T : Polynomial ℚ_[p]) (hT : T.Monic) :
    (P /ₘ T).natDegree ≤ P.natDegree := by
  rw [Polynomial.natDegree_divByMonic P hT]
  omega

/-- The Lagrange residue `P(r_i)/T'(r_i)` is integral when the root
separations are p-adic units. -/
theorem integral_residue {ι : Type*} [DecidableEq ι] (s : Finset ι) (i : ι)
    (r : ι → ℚ_[p]) (P : Polynomial ℚ_[p])
    (hP : ∀ n, ‖P.coeff n‖ ≤ 1) (hr : ‖r i‖ ≤ 1)
    (hsep : ∀ j ∈ s.erase i, ‖r i - r j‖ = 1) :
    ‖P.eval (r i) / ∏ j ∈ s.erase i, (r i - r j)‖ ≤ 1 := by
  rw [norm_div, norm_prod]
  have hprod : ∏ j ∈ s.erase i, ‖r i - r j‖ = 1 :=
    Finset.prod_eq_one hsep
  rw [hprod, div_one]
  exact integral_polynomial_eval P (r i) hP hr

/-- Harmonic indices below `p` have integral fifth-order harmonic sums. -/
theorem harmonic5_padic_integral (n : ℕ) (hn : n < p) :
    ‖∑ i ∈ Finset.range n, (1 / (((i : ℚ) + 1) ^ 5) : ℚ_[p])‖ ≤ 1 := by
  apply norm_sum_le_of_forall_le_of_nonneg (by norm_num)
  intro i hi
  have hi' : i < n := Finset.mem_range.mp hi
  have hbase : ‖((1 / ((i + 1 : ℕ) : ℚ) : ℚ) : ℚ_[p])‖ ≤ 1 := by
    apply Padic.norm_rat_le_one
    rw [one_div, Rat.inv_natCast_den_of_pos (by omega)]
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hpw := pow_le_one₀ (norm_nonneg _) hbase (n := 5)
  simpa [norm_pow, ← inv_pow] using hpw

#print axioms integral_monic_division
#print axioms integral_residue
end Zeta5Local
