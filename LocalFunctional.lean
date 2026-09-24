import Mathlib.Tactic

/-!
# Exact algebra in Section 3 of Fauzan's ζ(5) manuscript

This file proves the pole identities used to extend the rational functional.
It does not assume or establish the p-adic estimates or the irrationality result.
No `sorry` or nonstandard axioms are used.
-/

namespace Zeta5Local

open Polynomial

/-- The finite fifth-order harmonic sum from (2.3). -/
def harmonic5 (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, 1 / ((i : ℚ) + 1) ^ 5

@[simp] theorem harmonic5_zero : harmonic5 0 = 0 := by
  simp [harmonic5]

theorem harmonic5_succ (n : ℕ) :
    harmonic5 (n + 1) = harmonic5 n + 1 / ((n : ℚ) + 1) ^ 5 := by
  simp [harmonic5, Finset.sum_range_succ]

/-- The pole index `d` in Section 3, including the negative poles. -/
def poleIndex (r : ℤ) : ℕ :=
  if 0 ≤ r then r.toNat else (-r - 1).toNat

@[simp] theorem poleIndex_natCast (n : ℕ) : poleIndex (n : ℤ) = n := by
  simp [poleIndex]

@[simp] theorem poleIndex_negSucc (n : ℕ) :
    poleIndex (-((n : ℤ) + 1)) = n := by
  simp only [poleIndex]
  split_ifs with h
  · omega
  · omega

/-- Reflection preserves the harmonic index. -/
theorem poleIndex_reflect (r : ℤ) : poleIndex (-1 - r) = poleIndex r := by
  unfold poleIndex
  split_ifs <;> omega

/-- The assigned value of `1/(x-r)`, as a polynomial in the indeterminate. -/
noncomputable def poleValue (r : ℤ) : ℚ[X] := C (harmonic5 (poleIndex r)) - X

@[simp] theorem poleValue_zero : poleValue 0 = -X := by
  simp [poleValue, poleIndex]

/-- Equality of the two pole values whose rational functions differ by
reflection and a minus sign, as required by (3.2). -/
theorem poleValue_reflect (r : ℤ) : poleValue (-1 - r) = poleValue r := by
  simp [poleValue, poleIndex_reflect]

/-- The harmonic increment determines successive nonnegative poles. -/
theorem poleValue_succ (n : ℕ) :
    poleValue ((n : ℤ) + 1) - poleValue (n : ℤ) =
      C (1 / ((n : ℚ) + 1) ^ 5) := by
  have hn : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by omega
  have hi : poleIndex ((n : ℤ) + 1) = n + 1 := by rw [hn, poleIndex_natCast]
  simp only [poleValue, hi, poleIndex_natCast, harmonic5_succ, map_add]
  ring

/-- The value of every integer pole is forced by its value at zero,
reflection, and the positive harmonic increments. This isolates the uniqueness
argument at the end of Lemma 3.2 from its analytic existence claims. -/
theorem poleValue_unique (f : ℤ → ℚ[X])
    (hzero : f 0 = -X)
    (hreflect : ∀ r : ℤ, f (-1 - r) = f r)
    (hsucc : ∀ n : ℕ, f ((n : ℤ) + 1) - f (n : ℤ) =
      C (1 / ((n : ℚ) + 1) ^ 5)) :
    f = poleValue := by
  have hnat : ∀ n : ℕ, f (n : ℤ) = poleValue (n : ℤ) := by
    intro n
    induction n with
    | zero => simpa using hzero
    | succ n ih =>
      have h := hsucc n
      have h' := poleValue_succ n
      push_cast
      rw [ih] at h
      linear_combination h - h'
  funext r
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg r
  · exact hnat n
  · cases n with
    | zero => simpa using hnat 0
    | succ n =>
      have hn : -((n + 1 : ℕ) : ℤ) = -1 - (n : ℤ) := by omega
      rw [hn, hreflect, poleValue_reflect]
      exact hnat n

/-- The rational partial-fraction identity used in proving (3.1).
The assumptions are exactly exclusion of its two poles. -/
theorem pole_pullback_partial_fraction (x j : ℚ)
    (hm : x - j ≠ 0) (hp : x + j ≠ 0) :
    x ^ 5 / (j ^ 2 - x ^ 2) =
      -x ^ 3 - j ^ 2 * x - j ^ 4 / 2 * (1 / (x - j) + 1 / (x + j)) := by
  have hd : j ^ 2 - x ^ 2 ≠ 0 := by
    have h : (x - j) * (x + j) ≠ 0 := mul_ne_zero hm hp
    intro he
    apply h
    nlinarith
  field_simp
  ring

/-- The complete affine polynomial obtained by applying τ to the right side
of the preceding partial fractions. The harmonic increment supplies precisely
the `1/(2j)` correction in (2.3), so the constant term is checked too. -/
theorem pole_pullback_value (n : ℕ) :
    -C (1 / 4 : ℚ) - C (((n : ℚ) + 1) ^ 4 / 2) *
      (poleValue ((n : ℤ) + 1) + poleValue (-((n : ℤ) + 1))) =
    C (((n : ℚ) + 1) ^ 4) * (X - C (harmonic5 (n + 1))) -
      C (1 / 4 : ℚ) + C (1 / (2 * ((n : ℚ) + 1))) := by
  have hn : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by omega
  have hq : (n : ℚ) + 1 ≠ 0 := by positivity
  have hpos : poleIndex ((n : ℤ) + 1) = n + 1 := by
    rw [hn, poleIndex_natCast]
  have hneg : poleIndex (-((n : ℤ) + 1)) = n := poleIndex_negSucc n
  simp only [poleValue, hpos, hneg]
  apply Polynomial.funext
  intro x
  simp only [eval_sub, eval_add, eval_neg, eval_mul, eval_C, eval_X,
    harmonic5_succ]
  field_simp
  ring

#print axioms poleValue_unique
#print axioms pole_pullback_value

end Zeta5Local
