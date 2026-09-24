import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic

/-!
# Prime valuations and integer polynomial normalization

Algebraic part of Section 5 of https://zenodo.org/records/22826419.
The local estimates themselves are separate proof obligations.
Lean 4.19.0 / mathlib v4.19.0.
-/

namespace Zeta5Normalization

theorem denominator_eq_one_of_nonnegative_valuations (q : ℚ)
    (hq : ∀ p : ℕ, p.Prime → 0 ≤ padicValRat p q) : q.den = 1 := by
  by_contra hden
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hden
  letI : Fact p.Prime := ⟨hp⟩
  have hpn : ¬p ∣ q.num.natAbs := by
    intro h
    have hd := Nat.dvd_gcd h hpd
    rw [q.reduced.gcd_eq_one] at hd
    exact hp.not_dvd_one hd
  have hn := padicValNat.eq_zero_of_not_dvd hpn
  have hd := one_le_padicValNat_of_dvd (ne_of_gt q.den_pos) hpd
  have h := hq p hp
  simp only [padicValRat, padicValInt, hn, Nat.cast_zero, zero_sub] at h
  omega

theorem integer_iff_nonnegative_valuations (q : ℚ) :
    (∃ z : ℤ, (z : ℚ) = q) ↔ ∀ p : ℕ, p.Prime → 0 ≤ padicValRat p q := by
  constructor
  · rintro ⟨z, rfl⟩ p _
    simp only [padicValRat.of_int]
    exact Nat.cast_nonneg _
  · intro h
    exact ⟨q.num, (Rat.den_eq_one_iff q).mp
      (denominator_eq_one_of_nonnegative_valuations q h)⟩

/-- Rational coefficients integral at every prime are integer coefficients. -/
theorem polynomial_integer_of_nonnegative_valuations (F : Polynomial ℚ)
    (hF : ∀ p : ℕ, p.Prime → ∀ i : ℕ, 0 ≤ padicValRat p (F.coeff i)) :
    ∃ Q : Polynomial ℤ, Q.map (Int.castRingHom ℚ) = F := by
  classical
  let Q : Polynomial ℤ := ∑ i ∈ F.support, Polynomial.monomial i (F.coeff i).num
  refine ⟨Q, ?_⟩
  calc
    Q.map (Int.castRingHom ℚ) =
        ∑ i ∈ F.support, Polynomial.monomial i ((F.coeff i).num : ℚ) := by
      simp only [Q, Polynomial.map_sum, Polynomial.map_monomial,
        Int.coe_castRingHom]
    _ = ∑ i ∈ F.support, Polynomial.monomial i (F.coeff i) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      exact (Rat.den_eq_one_iff _).mp
        (denominator_eq_one_of_nonnegative_valuations _ (fun p hp => hF p hp i))
    _ = F := Polynomial.sum_monomial_eq F

theorem valuation_zpow {p : ℕ} [Fact p.Prime] {q : ℚ}
    (hq : q ≠ 0) (e : ℤ) : padicValRat p (q ^ e) = e * padicValRat p q := by
  cases e with
  | ofNat n =>
    simpa only [Int.ofNat_eq_natCast, zpow_natCast] using (padicValRat.pow (p := p) (k := n) q)
  | negSucc n =>
    change padicValRat p (q ^ (-((n + 1 : ℕ) : ℤ))) =
      -((n + 1 : ℕ) : ℤ) * padicValRat p q
    rw [zpow_neg, zpow_natCast, padicValRat.inv, padicValRat.pow q]
    ring

theorem valuation_prod {ι : Type*} {p : ℕ} [Fact p.Prime]
    (S : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ S, f i ≠ 0) :
    padicValRat p (∏ i ∈ S, f i) = ∑ i ∈ S, padicValRat p (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hfS : ∀ i ∈ S, f i ≠ 0 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, padicValRat.mul (hf a (Finset.mem_insert_self _ _))
      (Finset.prod_ne_zero_iff.mpr hfS), ih hfS, Finset.sum_insert ha]

/-- Signed prime exponents are retained: positive bounds permit division. -/
def primeNormalizer (S : Finset ℕ) (L : ℕ → ℤ) : ℚ :=
  ∏ p ∈ S, (p : ℚ) ^ (-L p)

theorem primeNormalizer_pos (S : Finset ℕ) (L : ℕ → ℤ)
    (hS : ∀ p ∈ S, p.Prime) : 0 < primeNormalizer S L := by
  apply Finset.prod_pos
  intro p hp
  exact zpow_pos (by exact_mod_cast (hS p hp).pos) _

theorem valuation_primeNormalizer (S : Finset ℕ) (L : ℕ → ℤ)
    (hS : ∀ p ∈ S, p.Prime) (p : ℕ) (hp : p.Prime) :
    padicValRat p (primeNormalizer S L) = if p ∈ S then -L p else 0 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  unfold primeNormalizer
  rw [valuation_prod S _ (by
    intro q hq
    exact zpow_ne_zero _ (by exact_mod_cast (hS q hq).ne_zero))]
  have hterm : ∀ q ∈ S, padicValRat p ((q : ℚ) ^ (-L q)) =
      if q = p then -L p else 0 := by
    intro q hq
    have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (hS q hq).ne_zero
    rw [valuation_zpow hq0]
    by_cases hqp : q = p
    · subst q
      simp [padicValRat.self hp.one_lt]
    · letI : Fact q.Prime := ⟨hS q hq⟩
      rw [padicValRat.of_nat, padicValNat_primes (Ne.symm hqp)]
      simp [hqp]
  rw [Finset.sum_congr rfl hterm]
  simp

/-- The algebraic normalization step of Proposition 5.1, with all local
valuation bounds left explicit. Zero coefficients require no valuation bound. -/
theorem normalized_polynomial_is_integer (F : Polynomial ℚ)
    (S : Finset ℕ) (L : ℕ → ℤ) (hS : ∀ p ∈ S, p.Prime)
    (hlocal : ∀ p ∈ S, ∀ i : ℕ, F.coeff i ≠ 0 → L p ≤ padicValRat p (F.coeff i))
    (houtside : ∀ p : ℕ, p.Prime → p ∉ S → ∀ i : ℕ,
      F.coeff i ≠ 0 → 0 ≤ padicValRat p (F.coeff i)) :
    ∃ Q : Polynomial ℤ,
      Q.map (Int.castRingHom ℚ) = Polynomial.C (primeNormalizer S L) * F := by
  apply polynomial_integer_of_nonnegative_valuations
  intro p hp i
  letI : Fact p.Prime := ⟨hp⟩
  rw [Polynomial.coeff_C_mul]
  by_cases hi : F.coeff i = 0
  · simp [hi]
  · rw [padicValRat.mul (ne_of_gt (primeNormalizer_pos S L hS)) hi,
      valuation_primeNormalizer S L hS p hp]
    by_cases hpS : p ∈ S
    · simp only [if_pos hpS]
      linarith [hlocal p hpS i hi]
    · simp only [if_neg hpS, zero_add]
      exact houtside p hp hpS i hi

#print axioms denominator_eq_one_of_nonnegative_valuations
#print axioms polynomial_integer_of_nonnegative_valuations
#print axioms normalized_polynomial_is_integer

end Zeta5Normalization
