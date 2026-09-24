import BernoulliKernel
import AnalyticCompletion
import LocalDivision

/-!
# Lemma3.1: the local near-pole series is integral

The functional is defined using monic polynomial division and its Lagrange
residues. Integer poles are a special case of the integral, unit-separated
roots used here. The prescribed harmonic indices and parameter are integral.
-/
namespace Zeta5Local
open Polynomial IsUltrametricDist
variable {p : ℕ} [Fact p.Prime]

noncomputable def poleDenominator {ι : Type*} (s : Finset ι) (r : ι → ℚ_[p]) :
    Polynomial ℚ_[p] := ∏ i ∈ s, (X - C (r i))

lemma poleDenominator_monic {ι : Type*} (s : Finset ι) (r : ι → ℚ_[p]) :
    (poleDenominator s r).Monic :=
  Polynomial.monic_prod_of_monic s _ (fun i _ => Polynomial.monic_X_sub_C (r i))

lemma poleDenominator_integral {ι : Type*} (s : Finset ι) (r : ι → ℚ_[p])
    (hr : ∀ i, ‖r i‖ ≤ 1) (n : ℕ) :
    ‖(poleDenominator s r).coeff n‖ ≤ 1 := by
  let rr (i : ι) : PadicInt.subring p := ⟨r i, hr i⟩
  let T : Polynomial (PadicInt.subring p) := ∏ i ∈ s, (X - C (rr i))
  have hT : T.map (PadicInt.subring p).subtype = poleDenominator s r := by
    simp [T, rr, poleDenominator, Polynomial.map_prod]
  rw [← hT, Polynomial.coeff_map]
  exact (T.coeff n).property

noncomputable def localHarmonic (n : ℕ) : ℚ_[p] :=
  ∑ i ∈ Finset.range n, (1 / (((i : ℚ) + 1) ^ 5) : ℚ_[p])

lemma localHarmonic_norm (n : ℕ) (hn : n < p) : ‖(localHarmonic n : ℚ_[p])‖ ≤ 1 :=
  harmonic5_padic_integral n hn

noncomputable def nearPoleValue {ι : Type*} [DecidableEq ι]
    (U : Polynomial ℚ_[p]) (s : Finset ι) (r : ι → ℚ_[p])
    (d : ι → ℕ) (Y : ℚ_[p]) : ℚ_[p] :=
  tauPolynomial (U /ₘ poleDenominator s r) +
    ∑ i ∈ s, (U.eval (r i) / ∏ j ∈ s.erase i, (r i - r j)) * (localHarmonic (d i) - Y)

lemma principal_sum_integral {ι : Type*} [DecidableEq ι]
    (U : Polynomial ℚ_[p]) (s : Finset ι) (r : ι → ℚ_[p])
    (d : ι → ℕ) (Y : ℚ_[p])
    (hU : ∀ n, ‖U.coeff n‖ ≤ 1) (hr : ∀ i, ‖r i‖ ≤ 1)
    (hsep : ∀ i ∈ s, ∀ j ∈ s.erase i, ‖r i - r j‖ = 1)
    (hd : ∀ i ∈ s, d i < p) (hY : ‖Y‖ ≤ 1) :
    ‖∑ i ∈ s, (U.eval (r i) / ∏ j ∈ s.erase i, (r i - r j)) *
      (localHarmonic (d i) - Y)‖ ≤ 1 := by
  apply norm_sum_le_of_forall_le_of_nonneg (by norm_num)
  intro i hi
  rw [norm_mul]
  apply mul_le_one₀ (integral_residue s i r U hU (hr i) (hsep i hi)) (norm_nonneg _)
  exact (local_norm_sub_le_max _ _).trans (max_le (localHarmonic_norm _ (hd i hi)) hY)

/-- The entire rational functional has a one-prime loss, improved to
integrality under the numerator degree restriction. Both quotient and all
residue contributions are included in this statement. -/
theorem nearPoleValue_bounds {ι : Type*} [DecidableEq ι] (hp7 : 7 ≤ p)
    (U : Polynomial ℚ_[p]) (s : Finset ι) (r : ι → ℚ_[p])
    (d : ι → ℕ) (Y : ℚ_[p])
    (hU : ∀ n, ‖U.coeff n‖ ≤ 1) (hr : ∀ i, ‖r i‖ ≤ 1)
    (hsep : ∀ i ∈ s, ∀ j ∈ s.erase i, ‖r i - r j‖ = 1)
    (hd : ∀ i ∈ s, d i < p) (hY : ‖Y‖ ≤ 1) :
    ‖nearPoleValue U s r d Y‖ ≤ (p : ℝ) ∧
      (U.natDegree ≤ p + 1 → ‖nearPoleValue U s r d Y‖ ≤ 1) := by
  have hq := (integral_monic_division U (poleDenominator s r)
    (poleDenominator_monic s r) hU (poleDenominator_integral s r hr)).1
  have hs := principal_sum_integral U s r d Y hU hr hsep hd hY
  constructor
  · exact (norm_add_le_max _ _).trans (max_le
      (tauPolynomial_norm hp7 _ hq) (hs.trans (by exact_mod_cast (Fact.out : p.Prime).one_le)))
  · intro hdeg
    have hqdeg := (monic_quotient_natDegree_le U _ (poleDenominator_monic s r)).trans hdeg
    exact (norm_add_le_max _ _).trans (max_le (tauPolynomial_integral hp7 _ hq hqdeg) hs)

/-- Scalar form of Lemma3.1, including convergence of the functional series.
The initial numerator degree restriction absorbs the exceptional term; all
remaining possible denominator losses are absorbed by their `p^j` factors. -/
theorem nearPoleSeries_integral {ι : Type*} [DecidableEq ι] (hp7 : 7 ≤ p)
    (U : ℕ → Polynomial ℚ_[p]) (s : Finset ι) (r : ι → ℚ_[p])
    (d : ι → ℕ) (Y : ℚ_[p])
    (hU : ∀ j n, ‖(U j).coeff n‖ ≤ 1) (hr : ∀ i, ‖r i‖ ≤ 1)
    (hsep : ∀ i ∈ s, ∀ j ∈ s.erase i, ‖r i - r j‖ = 1)
    (hd : ∀ i ∈ s, d i < p) (hY : ‖Y‖ ≤ 1)
    (hdeg : (U 0).natDegree ≤ p + 1) :
    Summable (fun j => (p : ℚ_[p]) ^ j * nearPoleValue (U j) s r d Y) ∧
      ‖∑' j, (p : ℚ_[p]) ^ j * nearPoleValue (U j) s r d Y‖ ≤ 1 := by
  apply p_power_absorbs_loss
  · exact (nearPoleValue_bounds hp7 (U 0) s r d Y (hU 0) hr hsep hd hY).2 hdeg
  · intro j
    exact (nearPoleValue_bounds hp7 (U j) s r d Y (hU j) hr hsep hd hY).1

noncomputable def nearPoleResidueSum {ι : Type*} [DecidableEq ι]
    (U : Polynomial ℚ_[p]) (s : Finset ι) (r : ι → ℚ_[p]) : ℚ_[p] :=
  ∑ i ∈ s, U.eval (r i) / ∏ j ∈ s.erase i, (r i - r j)

lemma nearPoleResidueSum_integral {ι : Type*} [DecidableEq ι]
    (U : Polynomial ℚ_[p]) (s : Finset ι) (r : ι → ℚ_[p])
    (hU : ∀ n, ‖U.coeff n‖ ≤ 1) (hr : ∀ i, ‖r i‖ ≤ 1)
    (hsep : ∀ i ∈ s, ∀ j ∈ s.erase i, ‖r i - r j‖ = 1) :
    ‖nearPoleResidueSum U s r‖ ≤ 1 := by
  apply norm_sum_le_of_forall_le_of_nonneg (by norm_num)
  intro i hi
  exact integral_residue s i r U hU (hr i) (hsep i hi)

lemma nearPoleValue_affine {ι : Type*} [DecidableEq ι]
    (U : Polynomial ℚ_[p]) (s : Finset ι) (r : ι → ℚ_[p])
    (d : ι → ℕ) (Y : ℚ_[p]) :
    nearPoleValue U s r d Y = nearPoleValue U s r d 0 - nearPoleResidueSum U s r * Y := by
  simp [nearPoleValue, nearPoleResidueSum, mul_sub, Finset.sum_sub_distrib,
    Finset.sum_mul, add_sub_assoc]

/-- Coefficientwise extension with an indeterminate parameter, as required
in the paper. The dependence on `Y` is affine even when `Y` itself is a
polynomial, so two convergent scalar series define this polynomial. -/
noncomputable def nearPolePolynomialSeries {ι : Type*} [DecidableEq ι]
    (U : ℕ → Polynomial ℚ_[p]) (s : Finset ι) (r : ι → ℚ_[p])
    (d : ι → ℕ) (Y : Polynomial ℚ_[p]) : Polynomial ℚ_[p] :=
  C (∑' j, (p : ℚ_[p]) ^ j * nearPoleValue (U j) s r d 0) -
    C (∑' j, (p : ℚ_[p]) ^ j * nearPoleResidueSum (U j) s r) * Y

/-- Every coefficient of the extended local functional is integral.
This is the Q_p[X] conclusion in Lemma3.1, rather than merely a bound at
one chosen numeric value of the indeterminate. -/
theorem nearPolePolynomialSeries_integral {ι : Type*} [DecidableEq ι] (hp7 : 7 ≤ p)
    (U : ℕ → Polynomial ℚ_[p]) (s : Finset ι) (r : ι → ℚ_[p])
    (d : ι → ℕ) (Y : Polynomial ℚ_[p])
    (hU : ∀ j n, ‖(U j).coeff n‖ ≤ 1) (hr : ∀ i, ‖r i‖ ≤ 1)
    (hsep : ∀ i ∈ s, ∀ j ∈ s.erase i, ‖r i - r j‖ = 1)
    (hd : ∀ i ∈ s, d i < p) (hY : ∀ n, ‖Y.coeff n‖ ≤ 1)
    (hdeg : (U 0).natDegree ≤ p + 1) (n : ℕ) :
    ‖(nearPolePolynomialSeries U s r d Y).coeff n‖ ≤ 1 := by
  have hconst := (nearPoleSeries_integral hp7 U s r d 0 hU hr hsep hd
    (by norm_num) hdeg).2
  have hres : ∀ j, ‖nearPoleResidueSum (U j) s r‖ ≤ 1 :=
    fun j => nearPoleResidueSum_integral (U j) s r (hU j) hr hsep
  have hslope := (p_power_absorbs_loss (fun j => nearPoleResidueSum (U j) s r)
    (hres 0) (fun j => (hres j).trans
      (by exact_mod_cast (Fact.out : p.Prime).one_le))).2
  unfold nearPolePolynomialSeries
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  apply (local_norm_sub_le_max _ _).trans
  apply max_le
  · simp only [Polynomial.coeff_C]
    split_ifs
    · exact hconst
    · norm_num
  · rw [norm_mul]
    exact mul_le_one₀ hslope (norm_nonneg _) (hY n)

#print axioms nearPoleSeries_integral
#print axioms nearPolePolynomialSeries_integral
end Zeta5Local
