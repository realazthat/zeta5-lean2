import NumeratorFunctional

/-! Cancellation of any chosen subset of the actual simple poles. -/
noncomputable section
open scoped BigOperators
open Polynomial Finset
namespace Zeta5FunctionalCancellation
open Zeta5Construction Zeta5NumeratorFunctional Zeta5OuterMoments

def selectedTail (N : ℕ) {h : ℕ} (s : Finset (Fin h)) : ℚ[X] :=
  ∏ k ∈ s, (X-C (node N k))

def omittedTail (N : ℕ) {h : ℕ} (s : Finset (Fin h)) : ℚ[X] :=
  selectedTail N (univ \ s)

lemma selectedTail_monic (N : ℕ) {h : ℕ} (s : Finset (Fin h)) :
    (selectedTail N s).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_sub_C _)

lemma tail_split_selected (N : ℕ) {h : ℕ} (s : Finset (Fin h)) :
    tailDenominator N h = omittedTail N s * selectedTail N s := by
  exact (Finset.prod_sdiff (Finset.subset_univ s)).symm

lemma selectedTail_eval_zero (N : ℕ) {h : ℕ} (s : Finset (Fin h))
    (k : Fin h) (hk : k ∈ s) : (selectedTail N s).eval (node N k) = 0 := by
  simp only [selectedTail, eval_prod]
  exact Finset.prod_eq_zero hk (by simp)

lemma omittedTail_eval_ne_zero (N : ℕ) {h : ℕ} (s : Finset (Fin h))
    (k : Fin h) (hk : k ∈ s) : (omittedTail N s).eval (node N k) ≠ 0 := by
  simp only [omittedTail, selectedTail, eval_prod, eval_sub, eval_X, eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro l hl
  apply sub_ne_zero.mpr
  intro heq
  have hkl := node_injective N h heq
  exact (Finset.mem_sdiff.mp hl).2 (hkl ▸ hk)

lemma poleDenominator_split_selected (N : ℕ) {h : ℕ} (s : Finset (Fin h))
    (k : Fin h) (hk : k ∈ s) :
    poleDenominator N k = (omittedTail N s).eval (node N k) *
      (selectedTail N s).derivative.eval (node N k) := by
  rw [← tailDenominator_derivative_at_node, tail_split_selected N s, derivative_mul,
    eval_add, eval_mul, eval_mul, selectedTail_eval_zero N s k hk, mul_zero, zero_add]

/-- Canceling any pole subset preserves the paper's prescribed functional.
This includes the polynomial quotient, without a degree restriction. -/
theorem numeratorFunctional_cancel_subset (N : ℕ) {h : ℕ} (s : Finset (Fin h))
    (μ : ℚ[X] →ₗ[ℚ] ℚ) (P : ℚ[X]) :
    numeratorFunctional N h μ (omittedTail N s * P) =
      C (μ (P / selectedTail N s)) +
        ∑ k ∈ s, C (P.eval (node N k) /
          (selectedTail N s).derivative.eval (node N k)) * poleFunctional (poleIndex N k) := by
  rw [numeratorFunctional_apply, tail_split_selected N s,
    cancel_monic_quotient (omittedTail N s) P (selectedTail N s)
      (selectedTail_monic N (univ \ s)) (selectedTail_monic N s)]
  congr 1
  have hs : (∑ k : Fin h, C ((omittedTail N s * P).eval (node N k) / poleDenominator N k) *
      poleFunctional (poleIndex N k)) =
      ∑ k ∈ s, C ((omittedTail N s * P).eval (node N k) / poleDenominator N k) *
      poleFunctional (poleIndex N k) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ s)
    intro k hk hks
    have hz : (omittedTail N s).eval (node N k) = 0 := by
      apply selectedTail_eval_zero
      simp [hks]
    simp only [eval_mul, hz, zero_mul, zero_div, map_zero]
  rw [hs]
  apply Finset.sum_congr rfl
  intro k hk
  rw [eval_mul, poleDenominator_split_selected N s k hk,
    mul_div_mul_left _ _ (omittedTail_eval_ne_zero N s k hk)]

#print axioms numeratorFunctional_cancel_subset
end Zeta5FunctionalCancellation
