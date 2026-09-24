import LocalFunctional
import Mathlib.NumberTheory.Padics.PadicNumbers

namespace Zeta5Local
variable {K : Type*} [Field K] [CharZero K]

/-- Scalar specialization of the integer-pole prescription. -/
noncomputable def integerPoleValue (Y : K) (r : ℤ) : K :=
  (harmonic5 (poleIndex r) : K) - Y

@[simp] lemma integerPoleValue_zero (Y : K) : integerPoleValue Y 0 = -Y := by
  simp [integerPoleValue, poleIndex]

@[simp] lemma integerPoleValue_neg_one (Y : K) : integerPoleValue Y (-1) = -Y := by
  simp [integerPoleValue, poleIndex]

lemma integerPoleValue_increment (Y : K) (r : ℤ) (hr : r ≠ 0) :
    integerPoleValue Y r - integerPoleValue Y (r - 1) = (r : K)⁻¹ ^ 5 := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg r
  · cases n with
    | zero => simp at hr
    | succ n =>
      have he : ((n + 1 : ℕ) : ℤ) - 1 = n := by omega
      rw [integerPoleValue, integerPoleValue, poleIndex_natCast, he, poleIndex_natCast,
        harmonic5_succ]
      push_cast
      simp only [one_div, inv_pow]
      ring
  · cases n with
    | zero => simp at hr
    | succ n =>
      have he : -((n + 1 : ℕ) : ℤ) = -((n : ℤ) + 1) := by omega
      have he' : -((n + 1 : ℕ) : ℤ) - 1 = -(((n + 1 : ℕ) : ℤ) + 1) := by omega
      rw [integerPoleValue, integerPoleValue, he', he, poleIndex_negSucc,
        poleIndex_negSucc, harmonic5_succ]
      push_cast
      have hn0 : (n : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      field_simp
      ring

/-- Values at the two central poles and all nonzero increments determine
an integer-pole functional; no analytic reflection argument is needed. -/
lemma integerPoleValue_unique (Y : K) (f : ℤ → K)
    (hzero : f 0 = -Y) (hnegone : f (-1) = -Y)
    (hinc : ∀ r : ℤ, r ≠ 0 → f r - f (r - 1) = (r : K)⁻¹ ^ 5) :
    f = integerPoleValue Y := by
  funext r
  induction r using Int.induction_on with
  | zero => simpa using hzero
  | succ n ih =>
    have h := hinc ((n : ℤ) + 1) (by omega)
    have hp := integerPoleValue_increment Y ((n : ℤ) + 1) (by omega)
    simp only [add_sub_cancel_right] at h hp
    rw [ih] at h
    linear_combination h - hp
  | pred n ih =>
    by_cases hn : n = 0
    · subst n
      simpa using hnegone
    · have h := hinc (-(n : ℤ)) (by exact neg_ne_zero.mpr (by exact_mod_cast hn))
      have hp := integerPoleValue_increment Y (-(n : ℤ))
        (by exact neg_ne_zero.mpr (by exact_mod_cast hn))
      rw [ih] at h
      linear_combination hp - h

#print axioms integerPoleValue_unique
end Zeta5Local
