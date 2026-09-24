import Mathlib.Tactic

/-!
# Inner-range row allocation in Zenodo 22826419

This file checks the finite algebra behind Section 4.1 and the integrand in
equation (5.4). It does not assume the conclusion of the paper. It also does not
prove the p-adic functional bounds (4.2)--(4.3), or the prime number theorem
passage in Section 5: those are separate remaining obligations.

All valuations have been removed from the statements below: these are exact
inequalities and finite-sum identities over the rationals and reals.
-/

namespace Zeta5Inner

open Finset

/-- The limiting pole-count function in Section 5.1. -/
def poleCount (x z : ℚ) : ℤ := ⌊x - z⌋ + ⌊x + z⌋ + 1

/-- This is the assertion that all ordinary pole counts have two consecutive
possible values. It needs no restriction on z. -/
theorem poleCount_two_values (x z : ℚ) :
    poleCount x z = ⌊2 * x⌋ ∨ poleCount x z = ⌊2 * x⌋ + 1 := by
  have h₁ := Int.le_floor_add (x - z) (x + z)
  have h₂ := Int.le_floor_add_floor (x - z) (x + z)
  have hsum : x - z + (x + z) = 2 * x := by ring
  rw [hsum] at h₁ h₂
  unfold poleCount
  omega

/-- Consequently any two classes differ by at most one. -/
theorem poleCount_difference_bound (x z₁ z₂ : ℚ) :
    poleCount x z₂ ≤ poleCount x z₁ + 1 := by
  rcases poleCount_two_values x z₁ with h₁ | h₁ <;>
    rcases poleCount_two_values x z₂ with h₂ | h₂ <;> omega

/-- Half of the contribution from an ordinary pole class. -/
def ordinaryWeight (i b ell : ℚ) : ℚ := i + b - (ell + 4) / 2

/-- The least ordinary-source half-weight seen by a row from another block. -/
def ambientWeight (T ell : ℚ) (extra : Bool) : ℚ :=
  T + (if extra then 1 else 0) - (ell + 4) / 2

/-- The crucial cross-class inequality in the proof of Proposition 4.1.
The two possible pole counts differ by at most one. If just the row's own
block receives an extra dimension, the allocation rule puts its count first. -/
theorem ordinary_row_le_other_source
    (T b i ellA ellC : ℚ) (extraA extraC : Bool)
    (hrow : i ≤ T - b + (if extraA then 1 else 0) - 1)
    (hcounts : ellC ≤ ellA + 1)
    (horder : extraA = true → extraC = false → ellC ≤ ellA) :
    ordinaryWeight i b ellA ≤ ambientWeight T ellC extraC := by
  cases extraA <;> cases extraC <;>
    simp_all [ordinaryWeight, ambientWeight] <;> linarith

/-- A row's weight is bounded by the common maximal ordinary-source weight. -/
theorem ordinary_row_le_top
    (T b i ell : ℚ) (extra : Bool)
    (hrow : i ≤ T - b + (if extra then 1 else 0) - 1)
    (hell : 0 ≤ ell) :
    ordinaryWeight i b ell ≤ T - 2 := by
  cases extra <;> simp_all [ordinaryWeight] <;> linarith

/-- The coarse zero-source bound used in Proposition 4.1. -/
theorem zero_source_lower_bound
    (M mN mK : ℚ) (hmN : 0 ≤ mN) (hmK : mK ≤ M) :
    7 * M + 41 / 2 ≤ 2 * (4 * M + 10) + 6 * mN - mK + 1 / 2 := by
  linarith

/-- This proves that every ordinary weight is admissible at the zero source
using exactly the estimates on T and mK supplied by Section 4.1. -/
theorem ordinary_row_le_zero_source
    (M T b i ell mN mK : ℚ) (extra : Bool)
    (hM : 0 ≤ M) (hmN : 0 ≤ mN) (hmK : mK ≤ M)
    (hT : T < (23 / 10) * M)
    (hrow : i ≤ T - b + (if extra then 1 else 0) - 1)
    (hell : 0 ≤ ell) :
    ordinaryWeight i b ell ≤ 2 * (4 * M + 10) + 6 * mN - mK + 1 / 2 := by
  have h₁ := ordinary_row_le_top T b i ell extra hrow hell
  have h₂ := zero_source_lower_bound M mN mK hmN hmK
  linarith

/-- For a zero-block row, taking the minimum as in (4.7) certifies the
zero source and every ordinary source simultaneously. -/
theorem zero_block_weight_bounds
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (zeroSource : ℚ) (ordinarySources : ι → ℚ) :
    min zeroSource (univ.inf' univ_nonempty ordinarySources) ≤ zeroSource ∧
      ∀ c, min zeroSource (univ.inf' univ_nonempty ordinarySources) ≤
        ordinarySources c := by
  constructor
  · exact min_le_left _ _
  · intro c
    exact (min_le_right _ _).trans (inf'_le _ (mem_univ c))

/-- Two one-row source estimates combine to the full entry bound (4.2). -/
theorem ordinary_source_entry_bound
    (νi νj ellN ellK wi wj : ℚ)
    (hi : wi ≤ νi + 3 * ellN - (ellK + 4) / 2)
    (hj : wj ≤ νj + 3 * ellN - (ellK + 4) / 2) :
    wi + wj ≤ νi + νj + 6 * ellN - ellK - 4 := by
  linarith

/-- The analogous combination for the zero-source bound (4.3). -/
theorem zero_source_entry_bound
    (νi νj mN mK wi wj : ℚ)
    (hi : wi ≤ 2 * νi + 6 * mN - mK + 1 / 2)
    (hj : wj ≤ 2 * νj + 6 * mN - mK + 1 / 2) :
    wi + wj ≤ 2 * νi + 2 * νj + 12 * mN - 2 * mK + 1 := by
  linarith

/-- Exact contribution of one block to the doubled row-weight sum. -/
theorem block_weight_sum (L : ℕ) (b ell : ℚ) :
    2 * ∑ i ∈ range L, ordinaryWeight i b ell =
      (L : ℚ) * ((L : ℚ) + 2 * b - ell - 5) := by
  induction L with
  | zero => simp [ordinaryWeight]
  | succ L ih =>
      rw [sum_range_succ]
      push_cast
      simp only [ordinaryWeight] at *
      nlinarith [ih]

/-- Substituting L = T - b gives the first integrand in (5.4). -/
theorem base_block_cost (L : ℕ) (T b ell : ℚ) (hL : (L : ℚ) = T - b) :
    2 * ∑ i ∈ range L, ordinaryWeight i b ell =
      (T - b) * (T + b - ell - 5) := by
  rw [block_weight_sum, hL]
  ring

/-- An additional row in a class changes its cost by 2T - ell - 4. -/
theorem extra_row_cost (L : ℕ) (T b ell : ℚ) (hL : (L : ℚ) = T - b) :
    2 * (∑ i ∈ range (L + 1), ordinaryWeight i b ell) -
      2 * (∑ i ∈ range L, ordinaryWeight i b ell) =
        2 * T - ell - 4 := by
  rw [sum_range_succ]
  simp only [ordinaryWeight, hL]
  ring

/-- Preferentially allocate extras to the nPlus classes having count q + 1.
The remaining classes have count q. This yields the last terms of (5.4). -/
theorem greedy_extra_cost
    (s nPlus T q : ℚ) :
    min s nPlus * (2 * T - q - 5) +
      max (s - nPlus) 0 * (2 * T - q - 4) =
        s * (2 * T - q - 5) + max (s - nPlus) 0 := by
  rcases le_total s nPlus with h | h
  · rw [min_eq_left h, max_eq_right (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, max_eq_left (sub_nonneg.mpr h)]
    ring

/-- Filling every extra row agrees exactly with raising the base allocation
T by one. This is the transition identity invoked to make (5.7) uniform. -/
theorem base_allocation_transition (T b ell : ℚ) :
    (T - b) * (T + b - ell - 5) + (2 * T - ell - 4) =
      (T + 1 - b) * (T + 1 + b - ell - 5) := by
  ring

/-- The lower bound on T in the paper guarantees strictly positive ordinary
block dimensions. In particular no clipping of the allocation is needed. -/
theorem ordinary_dimension_positive
    (x T b : ℚ) (hx : 3 ≤ x)
    (hT : (23 / 10) * x - 21 / 20 < T)
    (hb : b ≤ (9 / 20) * x + 3) :
    3 / 2 < T - b := by
  linarith

/-- The possibly negative contribution of the two allocation fractions in
the numerator of (5.13) lies between -1/4 and zero. -/
theorem allocation_fraction_bounds
    (τ σ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    -(1 / 4) ≤ τ * (τ - σ) - max (τ - σ) 0 ∧
      τ * (τ - σ) - max (τ - σ) 0 ≤ 0 := by
  rcases le_total τ σ with h | h
  · rw [max_eq_right (sub_nonpos.mpr h)]
    constructor
    · nlinarith [sq_nonneg (τ - 1 / 2), mul_nonneg hτ0 (sub_nonneg.mpr hσ1)]
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos hτ0 (sub_nonpos.mpr h)]
  · rw [max_eq_left (sub_nonneg.mpr h)]
    constructor
    · nlinarith [sq_nonneg (τ - 1 / 2),
        mul_nonneg hσ0 (sub_nonneg.mpr hτ1)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hτ1) (sub_nonneg.mpr h)]

/-- An exact verification of the numerator bounds used in (5.14). -/
theorem fractional_numerator_bounds
    (τ σ η : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    -(1 / 4) ≤ τ * (τ - σ) - max (τ - σ) 0 + η * (1 - η) ∧
      τ * (τ - σ) - max (τ - σ) 0 + η * (1 - η) ≤ 1 / 4 := by
  obtain ⟨hl, hu⟩ := allocation_fraction_bounds τ σ hτ0 hτ1 hσ0 hσ1
  constructor
  · nlinarith [mul_nonneg hη0 (sub_nonneg.mpr hη1)]
  · nlinarith [sq_nonneg (η - 1 / 2)]

/-- The integral defining Γ after the mean-zero identities for A and B
have been applied. BB and AB denote the two remaining integrals. -/
noncomputable def gammaFromMoments (x τ σ BB AB : ℝ) : ℝ :=
  let T := (23 / 10) * x - τ
  T ^ 2 / 2 - T * x - 5 * T / 2 -
    18 * (3 / 40) ^ 2 * x ^ 2 - 9 * BB +
    6 * (3 / 40) * x ^ 2 + 3 * AB + 15 * (3 / 40) * x +
    τ / 2 * (2 * T - (2 * x - σ) - 5) + max (τ - σ) 0 / 2

/-- The scalar normalization term (5.5) written in terms of the fractional
parts f = {x}, g = {αx}, η = {2λx}. -/
noncomputable def normalizationFromFractions (x f g η : ℝ) : ℝ :=
  let m := 2 * (37 / 40) * x - η
  2 * (37 / 40) * x * (x - f) -
    12 * (37 / 40) * x * ((3 / 40) * x - g) -
    2 * (m * (37 / 40) * x - m * (m + 1) / 4)

/-- The full algebraic cancellation leading to (5.12)--(5.13).
In particular the quadratic x term cancels exactly. -/
theorem remainder_decomposition (x f g τ σ η BB AB : ℝ) :
    -gammaFromMoments x τ σ BB AB - normalizationFromFractions x f g η =
      x * (4 * (37 / 40) + 2 * (37 / 40) * f - 12 * (37 / 40) * g) +
        (τ * (τ - σ) - max (τ - σ) 0 + η * (1 - η)) / 2 +
        9 * BB - 3 * AB := by
  unfold gammaFromMoments normalizationFromFractions
  ring

/-- Once the squared and mixed integrals have their stated bounds, this
derives the full remainder estimate (5.14), including both constants. -/
theorem remainder_bounds
    (τ σ η BB AB : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hBB0 : 0 ≤ BB) (hBB1 : BB ≤ 1 / 8)
    (hAB0 : -(1 / 8) ≤ AB) (hAB1 : AB ≤ 1 / 8) :
    -(1 / 2) ≤
      (τ * (τ - σ) - max (τ - σ) 0 + η * (1 - η)) / 2 + 9 * BB - 3 * AB ∧
    (τ * (τ - σ) - max (τ - σ) 0 + η * (1 - η)) / 2 + 9 * BB - 3 * AB ≤
      13 / 8 := by
  obtain ⟨hl, hu⟩ := fractional_numerator_bounds τ σ η hτ0 hτ1 hσ0 hσ1 hη0 hη1
  constructor <;> linarith

/-- Exact evaluation of the upper tail expression at T = 20 in (5.16). -/
theorem tail_at_twenty_constant :
    -(37 / 40 : ℚ) / 20 - (37 / 2) / 20 ^ 2 + (2923 / 240) / 20 ^ 2 +
      32 / 20 ^ 3 + (13 / 8) / (2 * 20 ^ 2) = -(2689 / 48000) := by
  norm_num

#print axioms ordinary_row_le_other_source
#print axioms poleCount_two_values
#print axioms ordinary_row_le_zero_source
#print axioms block_weight_sum
#print axioms greedy_extra_cost
#print axioms base_allocation_transition
#print axioms remainder_bounds
#print axioms remainder_decomposition

end Zeta5Inner
