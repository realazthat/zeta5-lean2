import Construction
import PartialFractions

/-! Exact bridge from the paper's rational function to its defined quotient
and residue terms, also after evaluating rational coefficients in ℝ. -/
namespace Zeta5Construction
open Polynomial

/-- The actual construction has precisely the partial fractions used in
its rational functional, including the entire polynomial quotient. -/
theorem construction_partial_fraction_eval₂ {F : Type*} [Field F]
    (f : ℚ →+* F) (N h e : ℕ) (t : F)
    (ht : ∀ i : Fin h, t ≠ f (node N i)) :
    (numerator N e).eval₂ f t / (tailDenominator N h).eval₂ f t =
      (numerator N e / tailDenominator N h).eval₂ f t +
        ∑ i : Fin h, f (residue N e i) / (t - f (node N i)) := by
  simpa only [tailDenominator, Lagrange.nodal, residue, poleDenominator] using
    Zeta5Local.partial_fraction_eval₂ f (numerator N e) Finset.univ
      (node N : Fin h → ℚ) (node_injective N h).injOn t (fun i _ => ht i)

/-- All poles are strictly negative. -/
theorem node_neg (N : ℕ) {h : ℕ} (i : Fin h) : node N i < 0 := by
  have hp : (0 : ℚ) < (poleIndex N i : ℚ) := by exact_mod_cast poleIndex_pos N i
  unfold node
  exact neg_neg_of_pos (sq_pos_of_pos hp)

/-- Real integration at t=y² avoids every pole, including at y=0. -/
theorem construction_partial_fraction_at_square (N h e : ℕ) (y : ℝ) :
    (numerator N e).eval₂ (Rat.castHom ℝ) (y ^ 2) /
      (tailDenominator N h).eval₂ (Rat.castHom ℝ) (y ^ 2) =
      (numerator N e / tailDenominator N h).eval₂ (Rat.castHom ℝ) (y ^ 2) +
        ∑ i : Fin h, (residue N e i : ℝ) /
          (y ^ 2 + ((poleIndex N i : ℕ) : ℝ) ^ 2) := by
  have ht : ∀ i : Fin h, y ^ 2 ≠ (Rat.castHom ℝ) (node N i) := by
    intro i
    have hn : (node N i : ℝ) < 0 := by exact_mod_cast node_neg N i
    have hy := sq_nonneg y
    change y ^ 2 ≠ (node N i : ℝ)
    linarith
  have hpf := construction_partial_fraction_eval₂ (Rat.castHom ℝ) N h e (y ^ 2) ht
  simpa [node] using hpf

#print axioms construction_partial_fraction_at_square
end Zeta5Construction
