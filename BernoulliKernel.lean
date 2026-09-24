import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Tactic

/-!
# Bernoulli bounds for the local functional

Requires mathlib v4.32.2, whose von Staudt–Clausen theorem is used explicitly.
-/
namespace Zeta5Local
open IsUltrametricDist
variable {p : ℕ} [Fact p.Prime]

lemma local_norm_sub_le_max (x y : ℚ_[p]) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  simpa only [sub_eq_add_neg, norm_neg] using norm_add_le_max x (-y)

lemma prime_reciprocal_integral (q : ℕ) (hq : q.Prime) (hne : p ≠ q) :
    ‖((1 / (q : ℚ) : ℚ) : ℚ_[p])‖ ≤ 1 := by
  apply Padic.norm_rat_le_one
  rw [one_div, Rat.inv_natCast_den_of_pos hq.pos]
  exact fun h => hne ((Nat.prime_dvd_prime_iff_eq Fact.out hq).mp h)

lemma prime_reciprocal_norm (q : ℕ) (hq : q.Prime) :
    ‖((1 / (q : ℚ) : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) := by
  by_cases h : p = q
  · subst q
    simp [Padic.norm_p]
  · exact (prime_reciprocal_integral q hq h).trans
      (by exact_mod_cast (Fact.out : p.Prime).one_le)

/-- A direct corollary of von Staudt–Clausen: every even Bernoulli number
loses at most one power of a prime. -/
theorem bernoulli_even_norm (k : ℕ) :
    ‖(bernoulli (2 * k) : ℚ_[p])‖ ≤ (p : ℝ) := by
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
  have hid : (bernoulli (2 * k) : ℚ_[p]) = (z : ℚ_[p]) -
      ∑ q ∈ (Finset.range (2 * k + 2)).filter
        (fun q => q.Prime ∧ (q - 1) ∣ 2 * k), ((1 / (q : ℚ) : ℚ) : ℚ_[p]) := by
    have hc := congrArg (fun x : ℚ => (x : ℚ_[p])) hz
    push_cast at hc ⊢
    linear_combination -hc
  rw [hid]
  apply (local_norm_sub_le_max _ _).trans
  apply max_le
  · exact (Padic.norm_int_le_one z).trans
      (by exact_mod_cast (Fact.out : p.Prime).one_le)
  · apply norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro q hq
    exact prime_reciprocal_norm q (Finset.mem_filter.mp hq).2.1

/-- Below degree `p-1`, no prime in the Staudt correction can equal `p`. -/
theorem bernoulli_even_integral (k : ℕ) (hk : 2 * k + 1 < p) :
    ‖(bernoulli (2 * k) : ℚ_[p])‖ ≤ 1 := by
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
  have hid : (bernoulli (2 * k) : ℚ_[p]) = (z : ℚ_[p]) -
      ∑ q ∈ (Finset.range (2 * k + 2)).filter
        (fun q => q.Prime ∧ (q - 1) ∣ 2 * k), ((1 / (q : ℚ) : ℚ) : ℚ_[p]) := by
    have hc := congrArg (fun x : ℚ => (x : ℚ_[p])) hz
    push_cast at hc ⊢
    linear_combination -hc
  rw [hid]
  apply (local_norm_sub_le_max _ _).trans
  refine max_le (Padic.norm_int_le_one z) ?_
  apply norm_sum_le_of_forall_le_of_nonneg (by norm_num)
  intro q hq
  have hmem := Finset.mem_filter.mp hq
  have hqle := Finset.mem_range.mp hmem.1
  exact prime_reciprocal_integral q hmem.2.1 (by omega)

/-- Staudt also gives integrality whenever the exceptional divisibility
condition fails. This sharper version is used for the μ moments. -/
theorem bernoulli_even_integral_of_not_dvd (k : ℕ) (hk : ¬ (p - 1) ∣ 2 * k) :
    ‖(bernoulli (2 * k) : ℚ_[p])‖ ≤ 1 := by
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
  have hid : (bernoulli (2 * k) : ℚ_[p]) = (z : ℚ_[p]) -
      ∑ q ∈ (Finset.range (2 * k + 2)).filter
        (fun q => q.Prime ∧ (q - 1) ∣ 2 * k), ((1 / (q : ℚ) : ℚ) : ℚ_[p]) := by
    have hc := congrArg (fun x : ℚ => (x : ℚ_[p])) hz
    push_cast at hc ⊢
    linear_combination -hc
  rw [hid]
  apply (local_norm_sub_le_max _ _).trans
  refine max_le (Padic.norm_int_le_one z) ?_
  apply norm_sum_le_of_forall_le_of_nonneg (by norm_num)
  intro q hq
  have hmem := Finset.mem_filter.mp hq
  apply prime_reciprocal_integral q hmem.2.1
  intro hpq
  exact hk (hpq ▸ hmem.2.2)

/-- Multiplication by p always clears the possible p-denominator of B₂ₖ. -/
theorem p_mul_bernoulli_even_integral (k : ℕ) :
    ‖(p : ℚ_[p]) * (bernoulli (2 * k) : ℚ_[p])‖ ≤ 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [norm_mul, Padic.norm_p]
  exact (mul_le_mul_of_nonneg_left (bernoulli_even_norm k) (by positivity)).trans_eq
    (inv_mul_cancel₀ hp0.ne')

/-- Uniform moment denominator bound, including the exceptional `B₁`. -/
theorem bernoulli_norm (hp7 : 7 ≤ p) (n : ℕ) :
    ‖(bernoulli n : ℚ_[p])‖ ≤ (p : ℝ) := by
  by_cases hn : n = 1
  · subst n
    simpa using prime_reciprocal_norm (p := p) 2 Nat.prime_two
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨k, hk⟩ := he
    have hnk : n = 2 * k := by omega
    rw [hnk]
    exact bernoulli_even_norm k
  · have hpos := ho.pos
    rw [bernoulli_eq_zero_of_odd ho (by omega)]
    simp

/-- The stronger initial-degree integrality used by Lemma 3.1. -/
theorem bernoulli_integral_below (hp7 : 7 ≤ p) (n : ℕ) (hn : n + 1 < p) :
    ‖(bernoulli n : ℚ_[p])‖ ≤ 1 := by
  by_cases hn1 : n = 1
  · subst n
    simpa using prime_reciprocal_integral (p := p) 2 Nat.prime_two (by omega)
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨k, hk⟩ := he
    have hnk : n = 2 * k := by omega
    rw [hnk]
    exact bernoulli_even_integral k (by omega)
  · have hpos := ho.pos
    rw [bernoulli_eq_zero_of_odd ho (by omega)]
    simp

/-- The rational moments κ_d from Section 3.1. The same formula is zero
for d=0,1,2, so no separate cases are needed in the definition. -/
def rationalTauMoment (d : ℕ) : ℚ :=
  (d : ℚ) * ((d : ℚ) - 1) * ((d : ℚ) - 2) * bernoulli (d - 3) / 24

lemma inv_twentyfour_integral (hp7 : 7 ≤ p) :
    ‖((1 / 24 : ℚ) : ℚ_[p])‖ ≤ 1 := by
  apply Padic.norm_rat_le_one
  norm_num
  intro h
  have hp : p.Prime := Fact.out
  have hb : p ≤ 24 := Nat.le_of_dvd (by norm_num) h
  interval_cases p <;> norm_num at *

lemma tau_coefficient_norm (hp7 : 7 ≤ p) (d : ℕ) :
    ‖(((d : ℚ) * ((d : ℚ) - 1) * ((d : ℚ) - 2) / 24 : ℚ) : ℚ_[p])‖ ≤ 1 := by
  have hi : ‖(((d : ℤ) * ((d : ℤ) - 1) * ((d : ℤ) - 2) : ℤ) : ℚ_[p])‖ ≤ 1 :=
    Padic.norm_int_le_one _
  have h24 := inv_twentyfour_integral (p := p) hp7
  have hh := mul_le_mul hi h24 (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have heq : (((d : ℚ) * ((d : ℚ) - 1) * ((d : ℚ) - 2) / 24 : ℚ) : ℚ_[p]) =
      (((d : ℤ) * ((d : ℤ) - 1) * ((d : ℤ) - 2) : ℤ) : ℚ_[p]) *
        ((1 / 24 : ℚ) : ℚ_[p]) := by
    push_cast
    ring
  rw [heq, norm_mul]
  simpa using hh

/-- The uniform bound v_p(κ_d) ≥ -1 in norm form, proved using Staudt. -/
theorem rationalTauMoment_norm (hp7 : 7 ≤ p) (d : ℕ) :
    ‖(rationalTauMoment d : ℚ_[p])‖ ≤ (p : ℝ) := by
  have hid : rationalTauMoment d =
      ((d : ℚ) * ((d : ℚ) - 1) * ((d : ℚ) - 2) / 24) * bernoulli (d - 3) := by
    unfold rationalTauMoment
    ring
  rw [hid, Rat.cast_mul, norm_mul]
  exact (mul_le_mul (tau_coefficient_norm hp7 d)
    (bernoulli_norm hp7 (d - 3)) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

/-- The initial-degree improvement κ_d∈Z_p for d≤p+1, required by Lemma3.1. -/
theorem rationalTauMoment_integral (hp7 : 7 ≤ p) (d : ℕ) (hd : d ≤ p + 1) :
    ‖(rationalTauMoment d : ℚ_[p])‖ ≤ 1 := by
  by_cases hd3 : 3 ≤ d
  · have hid : rationalTauMoment d =
        ((d : ℚ) * ((d : ℚ) - 1) * ((d : ℚ) - 2) / 24) * bernoulli (d - 3) := by
      unfold rationalTauMoment
      ring
    rw [hid, Rat.cast_mul, norm_mul]
    exact (mul_le_mul (tau_coefficient_norm hp7 d)
      (bernoulli_integral_below hp7 (d - 3) (by omega))
      (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  · interval_cases d <;> norm_num [rationalTauMoment]

/-- The local polynomial functional, with values in Q_p. -/
noncomputable def tauPolynomial (P : Polynomial ℚ_[p]) : ℚ_[p] :=
  ∑ i ∈ P.support, P.coeff i * (rationalTauMoment i : ℚ_[p])

/-- An integral polynomial loses at most one p-adic power under τ. -/
theorem tauPolynomial_norm (hp7 : 7 ≤ p) (P : Polynomial ℚ_[p])
    (hP : ∀ i, ‖P.coeff i‖ ≤ 1) :
    ‖tauPolynomial P‖ ≤ (p : ℝ) := by
  unfold tauPolynomial
  apply norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro i hi
  rw [norm_mul]
  exact (mul_le_mul (hP i) (rationalTauMoment_norm hp7 i)
    (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

/-- The degree restriction in Lemma3.1 removes that loss in the first term. -/
theorem tauPolynomial_integral (hp7 : 7 ≤ p) (P : Polynomial ℚ_[p])
    (hP : ∀ i, ‖P.coeff i‖ ≤ 1) (hdeg : P.natDegree ≤ p + 1) :
    ‖tauPolynomial P‖ ≤ 1 := by
  unfold tauPolynomial
  apply norm_sum_le_of_forall_le_of_nonneg (by norm_num)
  intro i hi
  have hi' : i ≤ P.natDegree := Polynomial.le_natDegree_of_ne_zero
    (Polynomial.mem_support_iff.mp hi)
  rw [norm_mul]
  exact (mul_le_mul (hP i) (rationalTauMoment_integral hp7 i (hi'.trans hdeg))
    (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

#print axioms rationalTauMoment_norm
#print axioms rationalTauMoment_integral

end Zeta5Local
