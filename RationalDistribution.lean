import IntegerPoleDistribution

namespace Zeta5Local
open Polynomial
variable {p : ℕ} [Fact p.Prime]

lemma rationalTauFunctional_padic_distribution (P : ℚ[X]) :
    (rationalTauFunctional P : ℚ_[p]) = (p : ℚ_[p])⁻¹ ^ 4 *
      ∑ a ∈ Finset.range p,
        (rationalTauFunctional (P.comp (C (a : ℚ) + C (p : ℚ) * X)) : ℚ_[p]) := by
  have h := congrArg (fun q : ℚ => (q : ℚ_[p]))
    (rationalTauFunctional_distribution p (Fact.out : p.Prime).ne_zero P)
  push_cast at h
  simpa only [inv_pow, div_eq_mul_inv, mul_comm] using h

/-- Full distribution for a finite rational partial-fraction presentation.
The polynomial quotient is retained and every pole is evaluated by the actual
analytic or integer prescription. Exact partial-fraction theorems provide
such a presentation for all source rational functions. -/
theorem rationalPresentation_distribution {ι : Type*} (hp7 : 7 ≤ p)
    (P : ℚ[X]) (s : Finset ι) (r : ι → ℤ) (c : ι → ℚ_[p]) (x : ℚ_[p]) :
    (rationalTauFunctional P : ℚ_[p]) + ∑ i ∈ s, c i * integerPoleValue x (r i) =
    (p : ℚ_[p])⁻¹ ^ 4 * ∑ a ∈ Finset.range p,
      ((rationalTauFunctional (P.comp (C (a : ℚ) + C (p : ℚ) * X)) : ℚ_[p]) +
        ∑ i ∈ s, (c i / (p : ℚ_[p])) *
          residuePoleValue ((p : ℚ_[p]) ^ 5 * x + distributionConstant p) (r i - a)) := by
  rw [Finset.sum_add_distrib, mul_add, ← rationalTauFunctional_padic_distribution]
  congr 1
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have h := congrFun (integerPole_distribution hp7 x) (r i)
  rw [← h, distributedIntegerPole, ← Finset.mul_sum]
  simp only [div_eq_mul_inv, pow_succ]
  ring

#print axioms rationalPresentation_distribution
end Zeta5Local
