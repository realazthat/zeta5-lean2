import ScaledLocalBound
import ActualRationalDistribution

namespace Zeta5Local
open Polynomial
variable {p : ℕ} [Fact p.Prime]
variable {ι : Type*} [DecidableEq ι]

/-- The polynomial occurring in the canonical local bound evaluates to the
literal local term in the actual distribution formula. -/
theorem local_presentation_eval (P : Polynomial ℚ_[p])
    (s near : Finset ι) (hne : near ⊆ s) (w : ι → ℤ) (c : ι → ℚ_[p])
    (Y : Polynomial ℚ_[p]) (x : ℚ_[p])
    (hnear : ∀ i ∈ s, i ∈ near ↔ (p : ℤ) ∣ w i) :
    (C (tauPolynomial P + ∑ i ∈ s\near, c i*analyticPoleValue ((w i : ℚ_[p])/(p : ℚ_[p]))) +
      ∑ i ∈ near, C (c i)*(C (localHarmonic (poleIndex (w i/p)))-Y)).eval x =
      tauPolynomial P + ∑ i ∈ s, c i*residuePoleValue (Y.eval x) (w i) := by
  simp only [eval_add, eval_C, eval_finsetSum, eval_mul, eval_sub]
  have hn : (∑ i ∈ near, c i*(localHarmonic (poleIndex (w i/p))-Y.eval x)) =
      ∑ i ∈ near, c i*residuePoleValue (Y.eval x) (w i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [residuePoleValue_near _ _ ((hnear i (hne hi)).mp hi)]
  have hf : (∑ i ∈ s\near, c i*analyticPoleValue ((w i : ℚ_[p])/(p : ℚ_[p]))) =
      ∑ i ∈ s\near, c i*residuePoleValue (Y.eval x) (w i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [residuePoleValue_far _ _ (fun h => (Finset.mem_sdiff.mp hi).2
      ((hnear i (Finset.mem_sdiff.mp hi).1).mpr h))]
  rw [hn, hf, add_assoc, Finset.sum_sdiff hne]

/-- Extract a scalar integral bound from the coefficient bound without
losing a prime. This applies to x=0 and x=1 for affine coefficient recovery. -/
theorem normalized_disk_value_integral (P : Polynomial ℚ_[p])
    (s near : Finset ι) (hne : near ⊆ s) (w : ι → ℤ) (c : ι → ℚ_[p])
    (Y : Polynomial ℚ_[p]) (x k : ℚ_[p]) (hx : ‖x‖ ≤ 1)
    (hnear : ∀ i ∈ s, i ∈ near ↔ (p : ℤ) ∣ w i)
    (hbound : ∀ n, ‖(C k*(C (tauPolynomial P +
      ∑ i ∈ s\near, c i*analyticPoleValue ((w i : ℚ_[p])/(p : ℚ_[p]))) +
      ∑ i ∈ near, C (c i)*(C (localHarmonic (poleIndex (w i/p)))-Y))).coeff n‖ ≤ 1) :
    ‖k*(tauPolynomial P + ∑ i ∈ s, c i*residuePoleValue (Y.eval x) (w i))‖ ≤ 1 := by
  have hh := integral_polynomial_eval _ x hbound hx
  rw [eval_mul, eval_C, local_presentation_eval P s near hne w c Y x hnear] at hh
  exact hh

lemma tauPolynomial_affine_rat (P : ℚ[X]) (a b : ℚ) :
    tauPolynomial ((P.map (Rat.castHom ℚ_[p])).comp
      (C (a : ℚ_[p])+C (b : ℚ_[p])*X)) =
      (rationalTauFunctional (P.comp (C a+C b*X)) : ℚ_[p]) := by
  rw [← tauPolynomial_map_rat]
  simp only [Polynomial.map_comp, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_X, Rat.coe_castHom]

#print axioms normalized_disk_value_integral
end Zeta5Local
