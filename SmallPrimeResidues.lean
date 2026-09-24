import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-!
# The factorial residue bound in Lemma 3.3

This verifies the factorial estimate used for every small prime. It is an
unconditional valuation theorem, not an assumed part of the paper's estimates.
-/
namespace Zeta5Local

/-- At any prime-power level, the two shifted factorial floor counts
exceed twice the unshifted count by at most one. -/
theorem factorial_floor_discrepancy (K r q : ℕ) (hr : r ≤ K) :
    (K + r) / q + (K - r) / q ≤ 2 * (K / q) + 1 := by
  by_cases hq : q = 0
  · simp [hq]
  have hsum := Nat.add_div_le_add_div (K + r) (K - r) q
  have hid : K + r + (K - r) = K + K := by omega
  rw [hid] at hsum
  have hd : (K + K) / q ≤ 2 * (K / q) + 1 := by
    rw [Nat.add_div (Nat.pos_of_ne_zero hq)]
    split_ifs <;> omega
  exact hsum.trans hd

/-- Legendre's formula summed over all prime powers proves the logarithmic
loss claimed for the residues in Lemma 3.3. -/
theorem factorial_valuation_discrepancy (p K r : ℕ) [Fact p.Prime]
    (hr : r ≤ K) :
    padicValNat p (K + r).factorial + padicValNat p (K - r).factorial ≤
      2 * padicValNat p K.factorial + Nat.log p (2 * K) := by
  let L := Nat.log p (2 * K)
  have h1 : Nat.log p (K + r) < L + 1 := by
    exact Nat.lt_succ_of_le (Nat.log_mono_right (by omega))
  have h2 : Nat.log p (K - r) < L + 1 := by
    exact Nat.lt_succ_of_le (Nat.log_mono_right (by omega))
  have h3 : Nat.log p K < L + 1 := by
    exact Nat.lt_succ_of_le (Nat.log_mono_right (by omega))
  rw [padicValNat_factorial h1, padicValNat_factorial h2,
    padicValNat_factorial h3, ← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.Ico 1 (L + 1), (2 * (K / p ^ i) + 1) :=
      Finset.sum_le_sum (fun i _ => factorial_floor_discrepancy K r (p ^ i) hr)
    _ = 2 * ∑ i ∈ Finset.Ico 1 (L + 1), K / p ^ i + L := by
      simp [Finset.sum_add_distrib, Finset.mul_sum]

/-- The rational factorial quotient multiplying `r A(r)` in each residue
has p-adic valuation at least `-⌊log_p(2K)⌋`. -/
theorem factorial_ratio_valuation (p K r : ℕ) [Fact p.Prime]
    (hr : r ≤ K) :
    -(Nat.log p (2 * K) : ℤ) ≤
      padicValRat p (((K.factorial : ℚ) ^ 2) /
        ((K + r).factorial * (K - r).factorial)) := by
  have hk : (K.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero K
  have hp : ((K + r).factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (K + r)
  have hm : ((K - r).factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (K - r)
  rw [padicValRat.div (pow_ne_zero _ hk) (mul_ne_zero hp hm),
    padicValRat.pow (K.factorial : ℚ), padicValRat.mul hp hm]
  simp only [padicValRat.of_nat]
  have h := factorial_valuation_discrepancy p K r hr
  omega

/-- The bound on the actual unsigned residue. The only property of the
polynomial used here is integrality of its value `a = A(r)` at the pole.
The zero-residue case is handled explicitly, since `padicValRat 0 = 0`
in mathlib rather than infinity. -/
theorem residue_valuation (p K r : ℕ) [Fact p.Prime] (hr : r ≤ K)
    (a : ℚ) (ha : 0 ≤ padicValRat p a) :
    -(Nat.log p (2 * K) : ℤ) ≤
      padicValRat p ((((K.factorial : ℚ) ^ 2) /
        ((K + r).factorial * (K - r).factorial)) * r * a) := by
  by_cases ha0 : a = 0
  · simp [ha0]
  by_cases hr0 : r = 0
  · simp [hr0]
  have hrq : (r : ℚ) ≠ 0 := by exact_mod_cast hr0
  have hquot : ((K.factorial : ℚ) ^ 2) /
      ((K + r).factorial * (K - r).factorial) ≠ 0 := by
    apply div_ne_zero
    · exact pow_ne_zero _ (by exact_mod_cast Nat.factorial_ne_zero K)
    · apply mul_ne_zero
      · exact_mod_cast Nat.factorial_ne_zero (K + r)
      · exact_mod_cast Nat.factorial_ne_zero (K - r)
  rw [padicValRat.mul (mul_ne_zero hquot hrq) ha0,
    padicValRat.mul hquot hrq]
  have hf := factorial_ratio_valuation p K r hr
  have hri : 0 ≤ padicValRat p (r : ℚ) := zero_le_padicValRat_of_nat r
  omega

#print axioms factorial_ratio_valuation
#print axioms residue_valuation
end Zeta5Local
