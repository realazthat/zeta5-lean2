import Mathlib.NumberTheory.BernoulliPolynomials
import BernoulliKernel
import Mathlib.Tactic

/-! Polynomial translation and distribution identities underlying Lemma3.2. -/
namespace Zeta5Local
open Polynomial

noncomputable def bernoulliFunctional : ℚ[X] →ₗ[ℚ] ℚ :=
  Polynomial.lsum fun n => (_root_.bernoulli n) • LinearMap.id

@[simp] theorem bernoulliFunctional_monomial (n : ℕ) (a : ℚ) :
    bernoulliFunctional (monomial n a) = a * _root_.bernoulli n := by
  simp [bernoulliFunctional, Polynomial.lsum_apply, mul_comm]

@[simp] theorem bernoulliFunctional_X_pow (n : ℕ) :
    bernoulliFunctional (X ^ n) = _root_.bernoulli n := by
  simpa only [Polynomial.monomial_one_right_eq_X_pow, one_mul] using
    bernoulliFunctional_monomial n 1

lemma bernoulliFunctional_power_difference (n : ℕ) :
    bernoulliFunctional ((1 + X) ^ n - X ^ n) = if n = 1 then 1 else 0 := by
  rw [Polynomial.one_add_X_pow_sub_X_pow, map_sum]
  simp only [← Nat.cast_smul_eq_nsmul ℚ, map_smul, bernoulliFunctional_X_pow, smul_eq_mul]
  exact _root_.sum_bernoulli n

/-- The Bernoulli functional has the exact translation difference of (3.3)
before the three differentiations defining τ. -/
theorem bernoulliFunctional_translation (P : ℚ[X]) :
    bernoulliFunctional (P.comp (1 + X) - P) = P.coeff 1 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      rw [Polynomial.add_comp]
      have heq : (P.comp (1 + X) + Q.comp (1 + X)) - (P + Q) =
          (P.comp (1 + X) - P) + (Q.comp (1 + X) - Q) := by ring
      rw [heq, map_add, hP, hQ, Polynomial.coeff_add]
  | monomial n a =>
      rw [← Polynomial.smul_X_eq_monomial, Polynomial.smul_comp,
        ← smul_sub, map_smul, Polynomial.coeff_smul]
      rw [Polynomial.X_pow_comp, bernoulliFunctional_power_difference]
      simp [Polynomial.coeff_X_pow, eq_comm]

/-- Translation differences span all polynomials in characteristic zero,
as witnessed explicitly by Bernoulli polynomials. -/
theorem functional_unique_of_translation (F G : ℚ[X] →ₗ[ℚ] ℚ)
    (h : ∀ P : ℚ[X], F (P.comp (1 + X) - P) = G (P.comp (1 + X) - P)) :
    F = G := by
  apply Polynomial.lhom_ext'
  intro n
  apply LinearMap.ext
  intro a
  have hn : (n + 1 : ℚ) ≠ 0 := by positivity
  have hP := h (Polynomial.bernoulli (n + 1))
  rw [Polynomial.bernoulli_comp_one_add_X, add_sub_cancel_left] at hP
  simp only [Nat.add_sub_cancel, ← Nat.cast_smul_eq_nsmul ℚ, map_smul,
    smul_eq_mul, Nat.cast_add, Nat.cast_one] at hP
  have hpow : F (X ^ n) = G (X ^ n) := mul_left_cancel₀ hn hP
  simp only [LinearMap.comp_apply, ← Polynomial.smul_X_eq_monomial,
    map_smul, hpow]

noncomputable def affineSubstitution (a b : ℚ) : ℚ[X] →ₗ[ℚ] ℚ[X] where
  toFun P := P.comp (C a + C b * X)
  map_add' P Q := Polynomial.add_comp
  map_smul' c P := by simp [Polynomial.smul_comp]

@[simp] theorem affineSubstitution_apply (a b : ℚ) (P : ℚ[X]) :
    affineSubstitution a b P = P.comp (C a + C b * X) := rfl

noncomputable def residueAverage (m : ℕ) : ℚ[X] →ₗ[ℚ] ℚ :=
  (m : ℚ)⁻¹ • ∑ a ∈ Finset.range m,
    bernoulliFunctional.comp (affineSubstitution (a : ℚ) (m : ℚ))

lemma residueAverage_apply (m : ℕ) (P : ℚ[X]) :
    residueAverage m P = (m : ℚ)⁻¹ *
      ∑ a ∈ Finset.range m, bernoulliFunctional (P.comp (C (a : ℚ) + C (m : ℚ) * X)) := by
  simp [residueAverage, LinearMap.sum_apply, LinearMap.smul_apply]

lemma shifted_affine_comp (P : ℚ[X]) (a b : ℚ) :
    (P.comp (1 + X)).comp (C a + C b * X) =
      P.comp (C (a + 1) + C b * X) := by
  rw [Polynomial.comp_assoc]
  congr 1
  simp only [Polynomial.add_comp, Polynomial.one_comp, Polynomial.X_comp, map_add, map_one]
  ring

/-- Translation of the residue-class average telescopes exactly. -/
lemma residueAverage_translation (m : ℕ) (hm : m ≠ 0) (P : ℚ[X]) :
    residueAverage m (P.comp (1 + X) - P) = P.coeff 1 := by
  rw [residueAverage_apply]
  have hs : (∑ a ∈ Finset.range m,
      bernoulliFunctional ((P.comp (1 + X) - P).comp (C (a : ℚ) + C (m : ℚ) * X))) =
      bernoulliFunctional (P.comp (C (m : ℚ) + C (m : ℚ) * X)) -
        bernoulliFunctional (P.comp (C 0 + C (m : ℚ) * X)) := by
    calc
      _ = ∑ a ∈ Finset.range m,
          (bernoulliFunctional (P.comp (C ((a + 1 : ℕ) : ℚ) + C (m : ℚ) * X)) -
            bernoulliFunctional (P.comp (C (a : ℚ) + C (m : ℚ) * X))) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Polynomial.sub_comp, map_sub, shifted_affine_comp]
        simp only [Nat.cast_add, Nat.cast_one]
      _ = _ := by
        simpa only [Nat.cast_zero] using Finset.sum_range_sub (fun a : ℕ =>
          bernoulliFunctional (P.comp (C (a : ℚ) + C (m : ℚ) * X))) m

  rw [hs]
  have hb : bernoulliFunctional (P.comp (C (m : ℚ) + C (m : ℚ) * X)) -
      bernoulliFunctional (P.comp (C 0 + C (m : ℚ) * X)) =
      bernoulliFunctional ((P.comp (C (m : ℚ) * X)).comp (1 + X) -
        P.comp (C (m : ℚ) * X)) := by
    rw [map_sub, Polynomial.comp_assoc]
    congr 2
    · simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp]
      ring
    · simp
  rw [hb, bernoulliFunctional_translation, Polynomial.comp_C_mul_X_coeff, pow_one]
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  field_simp

/-- Bernoulli multiplication/distribution, derived from translation
uniqueness rather than assumed as an extra identity. -/
theorem bernoulliFunctional_distribution (m : ℕ) (hm : m ≠ 0) (P : ℚ[X]) :
    bernoulliFunctional P = (m : ℚ)⁻¹ *
      ∑ a ∈ Finset.range m, bernoulliFunctional (P.comp (C (a : ℚ) + C (m : ℚ) * X)) := by
  have h : residueAverage m = bernoulliFunctional := by
    apply functional_unique_of_translation
    intro Q
    rw [residueAverage_translation m hm Q, bernoulliFunctional_translation]
  rw [← residueAverage_apply, h]

/-- The rational polynomial functional τ=L∘D³/24 of Section3. -/
noncomputable def rationalTauFunctional : ℚ[X] →ₗ[ℚ] ℚ :=
  (1 / 24 : ℚ) • bernoulliFunctional.comp
    (Polynomial.derivative.comp (Polynomial.derivative.comp Polynomial.derivative))

lemma rationalTauFunctional_apply (P : ℚ[X]) :
    rationalTauFunctional P = bernoulliFunctional P.derivative.derivative.derivative / 24 := by
  simp [rationalTauFunctional, div_eq_mul_inv, mul_comm]

lemma third_derivative_affine_comp (P : ℚ[X]) (a b : ℚ) :
    (P.comp (C a + C b * X)).derivative.derivative.derivative =
      C (b ^ 3) * P.derivative.derivative.derivative.comp (C a + C b * X) := by
  simp only [Polynomial.derivative_comp, Polynomial.derivative_add,
    Polynomial.derivative_mul, Polynomial.derivative_C, Polynomial.derivative_X,
    zero_add, zero_mul, mul_one]
  rw [map_pow]
  ring

/-- Equation3.3 on the entire polynomial part. -/
theorem rationalTauFunctional_translation (P : ℚ[X]) :
    rationalTauFunctional (P.comp (1 + X) - P) =
      P.derivative.derivative.derivative.derivative.eval 0 / 24 := by
  rw [rationalTauFunctional_apply]
  have hderiv : (P.comp (1 + X) - P).derivative.derivative.derivative =
      P.derivative.derivative.derivative.comp (1 + X) - P.derivative.derivative.derivative := by
    simp [Polynomial.derivative_comp]
  rw [hderiv, bernoulliFunctional_translation]
  simp [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]

/-- The p^-4 distribution factor in Lemma3.2, proved for the full
polynomial part and every nonzero natural modulus. -/
theorem rationalTauFunctional_distribution (m : ℕ) (hm : m ≠ 0) (P : ℚ[X]) :
    rationalTauFunctional P =
      (∑ a ∈ Finset.range m, rationalTauFunctional
        (P.comp (C (a : ℚ) + C (m : ℚ) * X))) / (m : ℚ) ^ 4 := by
  have hs : (∑ a ∈ Finset.range m, rationalTauFunctional
      (P.comp (C (a : ℚ) + C (m : ℚ) * X))) =
      (m : ℚ) ^ 3 / 24 * ∑ a ∈ Finset.range m,
        bernoulliFunctional (P.derivative.derivative.derivative.comp
          (C (a : ℚ) + C (m : ℚ) * X)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [rationalTauFunctional_apply, third_derivative_affine_comp,
      ← Polynomial.smul_eq_C_mul, map_smul]
    simp only [smul_eq_mul]
    ring
  rw [hs, rationalTauFunctional_apply, bernoulliFunctional_distribution m hm]
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  field_simp

/-- Exact agreement between the derivative definition of τ and the κ_d
coefficient kernel used in the p-adic completion. -/
theorem rationalTauFunctional_monomial (n : ℕ) (a : ℚ) :
    rationalTauFunctional (monomial n a) = a * rationalTauMoment n := by
  rw [rationalTauFunctional_apply]
  simp only [Polynomial.derivative_monomial, bernoulliFunctional_monomial,
    Nat.sub_sub]
  by_cases hn : 3 ≤ n
  · have hn1 : 1 ≤ n := by omega
    have hn2 : 2 ≤ n := by omega
    unfold rationalTauMoment
    push_cast [Nat.cast_sub hn1, Nat.cast_sub hn2]
    ring
  · interval_cases n <;> norm_num [rationalTauMoment]

theorem rationalTauFunctional_eq_sum (P : ℚ[X]) :
    rationalTauFunctional P = ∑ n ∈ P.support, P.coeff n * rationalTauMoment n := by
  conv_lhs => rw [← Polynomial.sum_monomial_eq P]
  simp only [Polynomial.sum_def, map_sum, rationalTauFunctional_monomial]

/-- Compatibility of the rational functional with its p-adic coefficient
extension; this connects the distribution theorem to the local norm bounds. -/
theorem tauPolynomial_map_rat {p : ℕ} [Fact p.Prime] (P : ℚ[X]) :
    tauPolynomial (P.map (Rat.castHom ℚ_[p])) = (rationalTauFunctional P : ℚ_[p]) := by
  rw [rationalTauFunctional_eq_sum]
  unfold tauPolynomial
  rw [Polynomial.support_map_of_injective P (Rat.castHom ℚ_[p]).injective]
  simp only [Polynomial.coeff_map, Rat.cast_sum, Rat.cast_mul]
  rfl

#print axioms bernoulliFunctional_distribution
#print axioms rationalTauFunctional_distribution

end Zeta5Local
