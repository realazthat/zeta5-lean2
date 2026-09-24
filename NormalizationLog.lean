import PaperParameters
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section
open scoped BigOperators
namespace Zeta5Normalization

lemma log_primeNormalizer (S : Finset ℕ) (L : ℕ→ℤ) (hS : ∀p∈S,p.Prime) :
    Real.log (primeNormalizer S L:ℝ) = -∑ p∈S, (L p:ℝ)*Real.log p := by
  unfold primeNormalizer
  push_cast
  rw [Real.log_prod (fun p hp => zpow_ne_zero _ (by exact_mod_cast (hS p hp).ne_zero))]
  simp only [Real.log_zpow, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]

end Zeta5Normalization
namespace Zeta5Parameters
lemma log_normalizer (n M : ℕ) :
    Real.log (normalizer n M:ℝ) =
      -∑p∈normalizationPrimes n, (localExponent n M p:ℝ)*Real.log p :=
  Zeta5Normalization.log_primeNormalizer _ _ (normalizationPrimes_prime n)

lemma eventually_admissible (M : ℕ) (hM : 40≤M) :
    ∀ᶠ n : ℕ in Filter.atTop, Admissible n M := by
  filter_upwards [Filter.eventually_ge_atTop (5*M^2)] with n hn
  exact ⟨hM, by unfold K; omega⟩

#print axioms log_normalizer
end Zeta5Parameters
