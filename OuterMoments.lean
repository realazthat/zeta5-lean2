import BernoulliKernel
import OuterValuation
import Construction

/-!
# Actual polynomial moment bounds for Section 4.2

This file proves the bound and the initial-degree integrality assertion for
formula (2.2), using the kernel-checked von Staudt–Clausen theorem through
`BernoulliKernel`. Requires Lean/mathlib 4.32.2.
-/

noncomputable section

namespace Zeta5OuterMoments
open Zeta5Local

variable {p : ℕ} [Fact p.Prime]

/-- Formula (2.2), definitionally the same as `Zeta5Construction.moment`. -/
def outerMoment (e : ℕ) : ℚ :=
  (-1)^e * bernoulli (2*e+2) * (2*e+3) * (2*e+4) * (2*e+5) / 24

lemma signed_integer_over_24_integral (hp : 7 ≤ p) (e t : ℕ) :
    ‖(((-1 : ℚ)^e * (t : ℚ) / 24 : ℚ) : ℚ_[p])‖ ≤ 1 := by
  have hi : ‖(((-1 : ℤ)^e * (t : ℤ) : ℤ) : ℚ_[p])‖ ≤ 1 := Padic.norm_int_le_one _
  have h24 := inv_twentyfour_integral (p := p) hp
  have hh := mul_le_mul hi h24 (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have heq : (((-1 : ℚ)^e * (t : ℚ) / 24 : ℚ) : ℚ_[p]) =
      (((-1 : ℤ)^e * (t : ℤ) : ℤ) : ℚ_[p]) * ((1/24 : ℚ) : ℚ_[p]) := by
    push_cast
    ring
  rw [heq, norm_mul]
  simpa using hh

lemma moment_factorization (e : ℕ) :
    outerMoment e =
      ((-1 : ℚ)^e * (((2*e+3)*(2*e+4)*(2*e+5) : ℕ) : ℚ) / 24) * bernoulli (2*(e+1)) := by
  unfold outerMoment
  rw [show 2*(e+1) = 2*e+2 by omega]
  push_cast
  ring

/-- Every polynomial moment loses at most one power of `p`. -/
theorem p_mul_outerMoment_integral (hp : 7 ≤ p) (e : ℕ) :
    ‖((p : ℚ_[p]) * (outerMoment e : ℚ_[p]))‖ ≤ 1 := by
  rw [moment_factorization]
  have heq : (p : ℚ_[p]) *
      ((((-1 : ℚ)^e * (((2*e+3)*(2*e+4)*(2*e+5) : ℕ) : ℚ) / 24) *
        bernoulli (2*(e+1)) : ℚ) : ℚ_[p]) =
      (((-1 : ℚ)^e * (((2*e+3)*(2*e+4)*(2*e+5) : ℕ) : ℚ) / 24 : ℚ) : ℚ_[p]) *
        ((p : ℚ_[p]) * (bernoulli (2*(e+1)) : ℚ_[p])) := by
    push_cast
    ring
  rw [heq, norm_mul]
  exact (mul_le_mul (signed_integer_over_24_integral hp e _)
    (p_mul_bernoulli_even_integral (p := p) (e+1)) (norm_nonneg _) (by norm_num)).trans_eq
      (one_mul _)

/-- The first three possible multiples of `p-1` are canceled by the three
successive factors in (2.2). This is the arithmetic behind the threshold `2p-3`. -/
theorem first_three_multiples_cancel (p e : ℕ) (hp : 7 ≤ p)
    (he : e < 2*p-3) (hdiv : (p-1) ∣ 2*e+2) :
    p ∣ (2*e+3)*(2*e+4)*(2*e+5) := by
  obtain ⟨k, hk⟩ := hdiv
  have hp1 : 0 < p-1 := by omega
  have hkpos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    simp [hk0] at hk
  have hklt : k < 4 := by
    by_contra h
    have hk4 : 4 ≤ k := by omega
    have hp' : p-1+1 = p := by omega
    have he' : 2*e+2 < 4*(p-1) := by omega
    nlinarith
  interval_cases k
  · have h : 2*e+3 = p := by omega
    rw [h]
    exact dvd_mul_of_dvd_left (dvd_mul_right p (2*e+4)) (2*e+5)
  · have h : 2*e+4 = 2*p := by omega
    rw [h]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_mul_left p 2) (2*e+3)) (2*e+5)
  · have h : 2*e+5 = 3*p := by omega
    rw [h]
    exact dvd_mul_of_dvd_right (dvd_mul_left p 3) _

/-- The actual polynomial moments are integral for `e < 2p-3`, as claimed
at the beginning of Section 4.2. -/
theorem outerMoment_integral_below (hp : 7 ≤ p) (e : ℕ) (he : e < 2*p-3) :
    ‖(outerMoment e : ℚ_[p])‖ ≤ 1 := by
  by_cases hdiv : (p-1) ∣ 2*(e+1)
  · have hd := first_three_multiples_cancel p e hp he (by simpa [Nat.mul_add] using hdiv)
    obtain ⟨t, ht⟩ := hd
    have hid : outerMoment e = ((-1 : ℚ)^e*(t : ℚ)/24) * ((p : ℚ)*bernoulli (2*(e+1))) := by
      rw [moment_factorization, ht]
      push_cast
      ring
    rw [hid, Rat.cast_mul, Rat.cast_mul, norm_mul]
    exact (mul_le_mul (signed_integer_over_24_integral hp e t)
      (p_mul_bernoulli_even_integral (p := p) (e+1)) (norm_nonneg _) (by norm_num)).trans_eq
        (one_mul _)
  · rw [moment_factorization, Rat.cast_mul, norm_mul]
    exact (mul_le_mul (signed_integer_over_24_integral hp e _)
      (bernoulli_even_integral_of_not_dvd (p := p) (e+1) hdiv)
      (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

/-- Integer-valued `padicValRat` version of the initial-degree result. -/
theorem outerMoment_padicVal_nonneg (hp : 7 ≤ p) (e : ℕ) (he : e < 2*p-3) :
    0 ≤ padicValRat p (outerMoment e) := by
  have h := (Padic.norm_le_one_iff_val_nonneg (outerMoment e : ℚ_[p])).mp
    (outerMoment_integral_below hp e he)
  simpa only [Padic.valuation_ratCast] using h

/-- The global valuation bound, guarded because `padicValRat p 0` defaults to zero. -/
theorem outerMoment_padicVal_lower (hp : 7 ≤ p) (e : ℕ) :
    -1 ≤ padicValRat p (outerMoment e) := by
  by_cases he : outerMoment e = 0
  · simp [he]
  have h := (Padic.norm_le_one_iff_val_nonneg
    (((p : ℚ)*outerMoment e : ℚ) : ℚ_[p])).mp (by simpa using p_mul_outerMoment_integral hp e)
  rw [Padic.valuation_ratCast, padicValRat.mul (by exact_mod_cast (Fact.out : p.Prime).ne_zero) he,
    padicValRat.self (Fact.out : p.Prime).one_lt] at h
  omega

/-- A convenient allowed choice in Section4.2: retain integral low moments,
and replace every remaining polynomial moment by zero. -/
def correctedMoment (p e : ℕ) : ℚ := if e < 2*p-3 then outerMoment e else 0

/-- For the discarded moments choose the exact rational integral lift `p·μ_e`.
It has the required residue, so no residue representative must be selected. -/
def correctionMoment (p e : ℕ) : ℚ := if e < 2*p-3 then 0 else (p : ℚ)*outerMoment e

theorem correctedMoment_integral (hp : 7 ≤ p) (e : ℕ) :
    ‖(correctedMoment p e : ℚ_[p])‖ ≤ 1 := by
  unfold correctedMoment
  split_ifs with h
  · exact outerMoment_integral_below hp e h
  · simp

theorem correctionMoment_integral (hp : 7 ≤ p) (e : ℕ) :
    ‖(correctionMoment p e : ℚ_[p])‖ ≤ 1 := by
  unfold correctionMoment
  split_ifs
  · simp
  · simpa using p_mul_outerMoment_integral hp e

theorem outerMoment_eq_corrected_add (e : ℕ) :
    outerMoment e = correctedMoment p e + (p : ℚ)⁻¹*correctionMoment p e := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  unfold correctedMoment correctionMoment
  split_ifs <;> simp [hp0]

def fullPolynomialMoment (P : Polynomial ℚ) : ℚ :=
  ∑ e ∈ P.support, P.coeff e * outerMoment e

def correctedPolynomialMoment (p : ℕ) (P : Polynomial ℚ) : ℚ :=
  ∑ e ∈ P.support, P.coeff e * correctedMoment p e

def correctionPolynomialMoment (p : ℕ) (P : Polynomial ℚ) : ℚ :=
  ∑ e ∈ P.support, P.coeff e * correctionMoment p e

/-- The correction decomposition is an exact rational identity. -/
theorem polynomialMoment_eq_corrected_add (P : Polynomial ℚ) :
    fullPolynomialMoment P = correctedPolynomialMoment p P +
      (p : ℚ)⁻¹*correctionPolynomialMoment p P := by
  unfold fullPolynomialMoment correctedPolynomialMoment correctionPolynomialMoment
  simp_rw [outerMoment_eq_corrected_add (p := p), mul_add]
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem correctedPolynomialMoment_integral (hp : 7 ≤ p) (P : Polynomial ℚ)
    (hP : ∀ n, ‖(P.coeff n : ℚ_[p])‖ ≤ 1) :
    ‖(correctedPolynomialMoment p P : ℚ_[p])‖ ≤ 1 := by
  unfold correctedPolynomialMoment
  push_cast
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by norm_num)
  intro e he
  rw [norm_mul]
  exact (mul_le_mul (hP e) (correctedMoment_integral hp e) (norm_nonneg _) (by norm_num)).trans_eq
    (one_mul _)

theorem correctionPolynomialMoment_integral (hp : 7 ≤ p) (P : Polynomial ℚ)
    (hP : ∀ n, ‖(P.coeff n : ℚ_[p])‖ ≤ 1) :
    ‖(correctionPolynomialMoment p P : ℚ_[p])‖ ≤ 1 := by
  unfold correctionPolynomialMoment
  push_cast
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by norm_num)
  intro e he
  rw [norm_mul]
  exact (mul_le_mul (hP e) (correctionMoment_integral hp e) (norm_nonneg _) (by norm_num)).trans_eq
    (one_mul _)

/-- The correction vanishes identically for every polynomial of low degree. -/
theorem correctionPolynomialMoment_eq_zero (P : Polynomial ℚ)
    (hdeg : P.natDegree < 2*p-3) : correctionPolynomialMoment p P = 0 := by
  unfold correctionPolynomialMoment
  apply Finset.sum_eq_zero
  intro e he
  have he' : e ≤ P.natDegree := Polynomial.le_natDegree_of_ne_zero
    (Polynomial.mem_support_iff.mp he)
  simp [correctionMoment, lt_of_le_of_lt he' hdeg]

/-- The actual correction matrix has the source's rank bound whenever its
polynomial quotients satisfy their elementary degree bounds. -/
theorem polynomial_correction_matrix_rank (K N h : ℕ) (hp : 7 ≤ p)
    (hsize : K = N+h) (Q : Matrix (Fin h) (Fin h) (Polynomial ℚ))
    (hdeg : ∀ i j, (Q i j).natDegree ≤ 5*N+i.val+j.val-h) :
    Matrix.rank (fun i j => correctionPolynomialMoment p (Q i j) : Matrix (Fin h) (Fin h) ℚ) ≤
      K+4*N+2-2*p := by
  apply Zeta5Outer.correction_rank_bound K N p h hsize
  intro i j hij
  apply correctionPolynomialMoment_eq_zero
  have hd := hdeg i j
  omega


section ActualConstruction
open Polynomial Zeta5Construction

lemma construction_moment_eq (e : ℕ) : Zeta5Construction.moment e = outerMoment e := rfl

lemma construction_denominator_monic (N : ℕ) : (denominator N).Monic := by
  unfold denominator
  exact Polynomial.monic_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_add_C _)

lemma construction_denominator_natDegree (N : ℕ) : (denominator N).natDegree = N := by
  unfold denominator
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_add_C _)]
  simp only [Polynomial.natDegree_X_add_C, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rfl

lemma construction_tail_monic (N h : ℕ) : (tailDenominator N h).Monic := by
  unfold tailDenominator
  exact Polynomial.monic_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_sub_C _)

lemma construction_tail_natDegree (N h : ℕ) : (tailDenominator N h).natDegree = h := by
  unfold tailDenominator
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_sub_C _)]
  simp

lemma construction_numerator_natDegree (N e : ℕ) : (numerator N e).natDegree = 5*N+e := by
  unfold numerator
  rw [((construction_denominator_monic N).pow 5).natDegree_mul (Polynomial.monic_X.pow e),
    (construction_denominator_monic N).natDegree_pow, construction_denominator_natDegree]
  simp

lemma construction_quotient_natDegree (N h e : ℕ) :
    (numerator N e / tailDenominator N h).natDegree = 5*N+e-h := by
  rw [← Polynomial.divByMonic_eq_div _ (construction_tail_monic N h),
    Polynomial.natDegree_divByMonic _ (construction_tail_monic N h),
    construction_numerator_natDegree, construction_tail_natDegree]

/-- The exact polynomial correction in the original monomial basis. -/
def actualCorrectionMatrix (N h p : ℕ) : Matrix (Fin h) (Fin h) ℚ :=
  fun i j => correctionPolynomialMoment p (numerator N (i.val+j.val) / tailDenominator N h)

/-- The rank estimate (4.10) for the paper's actual quotient matrix. -/
theorem actualCorrectionMatrix_rank (hp : 7 ≤ p) (N h : ℕ) :
    (actualCorrectionMatrix N h p).rank ≤ (N+h)+4*N+2-2*p := by
  apply polynomial_correction_matrix_rank (N+h) N h hp rfl
  intro i j
  rw [construction_quotient_natDegree]
  omega

/-- Integer models for the construction's monic numerator and denominator. -/
def integerDenominator (N : ℕ) : Polynomial ℤ :=
  ∏ k ∈ Finset.range N, (X+C (((k+1 : ℕ) : ℤ)^2))

def integerTailDenominator (N h : ℕ) : Polynomial ℤ :=
  ∏ i : Fin h, (X+C (((N+1+i.val : ℕ) : ℤ)^2))

def integerNumerator (N e : ℕ) : Polynomial ℤ := integerDenominator N ^ 5 * X^e

lemma integerTailDenominator_monic (N h : ℕ) : (integerTailDenominator N h).Monic := by
  unfold integerTailDenominator
  exact Polynomial.monic_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_add_C _)

lemma map_integerDenominator (N : ℕ) :
    (integerDenominator N).map (Int.castRingHom ℚ) = denominator N := by
  simp [integerDenominator, denominator, Polynomial.map_prod]

lemma map_integerTailDenominator (N h : ℕ) :
    (integerTailDenominator N h).map (Int.castRingHom ℚ) = tailDenominator N h := by
  simp [integerTailDenominator, tailDenominator, node, poleIndex, sub_neg_eq_add, Polynomial.map_prod]

lemma map_integerNumerator (N e : ℕ) :
    (integerNumerator N e).map (Int.castRingHom ℚ) = numerator N e := by
  simp [integerNumerator, numerator, map_integerDenominator]

/-- The quotient in the actual rational functional has integer coefficients. -/
theorem construction_quotient_integer_model (N h e : ℕ) :
    (integerNumerator N e /ₘ integerTailDenominator N h).map (Int.castRingHom ℚ) =
      numerator N e / tailDenominator N h := by
  rw [Polynomial.map_divByMonic _ (integerTailDenominator_monic N h),
    map_integerNumerator, map_integerTailDenominator,
    Polynomial.divByMonic_eq_div _ (construction_tail_monic N h)]

theorem construction_quotient_coeff_integral (N h e k : ℕ) :
    ‖((numerator N e / tailDenominator N h).coeff k : ℚ_[p])‖ ≤ 1 := by
  rw [← construction_quotient_integer_model, Polynomial.coeff_map]
  simpa using Padic.norm_int_le_one (p := p)
    ((integerNumerator N e /ₘ integerTailDenominator N h).coeff k)

/-- The correction matrix in (4.10) is integral, for the actual quotients. -/
theorem actualCorrectionMatrix_integral (hp : 7 ≤ p) (N h : ℕ) (i j : Fin h) :
    ‖(actualCorrectionMatrix N h p i j : ℚ_[p])‖ ≤ 1 := by
  apply correctionPolynomialMoment_integral hp
  exact construction_quotient_coeff_integral N h (i.val+j.val)

/-- The corrected polynomial contribution is integral as well. -/
theorem actualCorrectedQuotientMoment_integral (hp : 7 ≤ p) (N h e : ℕ) :
    ‖(correctedPolynomialMoment p (numerator N e / tailDenominator N h) : ℚ_[p])‖ ≤ 1 := by
  apply correctedPolynomialMoment_integral hp
  exact construction_quotient_coeff_integral N h e

lemma construction_polynomialFunctional_eq (P : Polynomial ℚ) :
    Zeta5Construction.polynomialFunctional P = fullPolynomialMoment P := by
  change (∑ e ∈ P.support, Zeta5Construction.moment e * P.coeff e) =
    ∑ e ∈ P.support, P.coeff e * outerMoment e
  simp only [construction_moment_eq, mul_comm]

def actualCorrectedConstantMatrix (N h p : ℕ) : Matrix (Fin h) (Fin h) ℚ := fun i j =>
  correctedPolynomialMoment p (numerator N (i.val+j.val) / tailDenominator N h) +
    ∑ k : Fin h, residue N (i.val+j.val) k * poleConstant (poleIndex N k)

def actualCorrectedHankel (N h p : ℕ) : Matrix (Fin h) (Fin h) (Polynomial ℚ) :=
  (X : Polynomial ℚ) • (coefficientMatrix N h).map C + (actualCorrectedConstantMatrix N h p).map C

/-- Equation (4.10) for the paper's actual Hankel matrix, exactly over the rationals.
`actualCorrectionMatrix_rank` and `actualCorrectionMatrix_integral` prove the
rank and integrality conditions for this same correction, without hypotheses. -/
theorem actual_hankel_correction_decomposition (N h : ℕ) :
    hankelMatrix N h = actualCorrectedHankel N h p +
      (((p : ℚ)⁻¹ • actualCorrectionMatrix N h p).map C) := by
  ext i j
  simp only [hankelMatrix, actualCorrectedHankel, actualCorrectedConstantMatrix,
    constantMatrix, quotientMoment, actualCorrectionMatrix, Matrix.add_apply,
    Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  rw [construction_polynomialFunctional_eq, polynomialMoment_eq_corrected_add (p := p)]
  simp only [map_add, map_mul]
  ring

end ActualConstruction

#print axioms outerMoment_integral_below
#print axioms outerMoment_padicVal_nonneg
#print axioms outerMoment_padicVal_lower

#print axioms polynomial_correction_matrix_rank
#print axioms actualCorrectionMatrix_rank
#print axioms actualCorrectionMatrix_integral
#print axioms actual_hankel_correction_decomposition

end Zeta5OuterMoments
