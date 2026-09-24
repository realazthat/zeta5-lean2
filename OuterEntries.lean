import OuterBasis
import NumeratorFunctional

/-! Exact class cancellation and the off-class entry estimates. -/
noncomputable section
open scoped BigOperators
open Polynomial Finset

namespace Zeta5OuterEntries
open Zeta5Construction Zeta5OuterMoments Zeta5OuterBasis Zeta5NumeratorFunctional Zeta5Outer

lemma complements_product {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (Q : ι → R) (a b : ι) (hab : a ≠ b) :
    (∏ c ∈ univ.erase a, Q c) * (∏ c ∈ univ.erase b, Q c) =
      (∏ c, Q c) * ∏ c ∈ (univ.erase a).erase b, Q c := by
  have hb : b ∈ (univ : Finset ι).erase a := by simp [hab.symm]
  have ha : a ∈ (univ : Finset ι).erase b := by simp [hab]
  have h1 := Finset.mul_prod_erase (univ.erase a) Q hb
  have h2 := Finset.mul_prod_erase (univ.erase b) Q ha
  have herase : ((univ : Finset ι).erase b).erase a = (univ.erase a).erase b := by
    ext c
    simp only [mem_erase, mem_univ, and_true]
    exact and_comm
  rw [herase] at h2
  have ht := Finset.mul_prod_erase (univ : Finset ι) Q (mem_univ a)
  rw [← ht, ← h1, ← h2]
  ring

def globalRow (p m N h : ℕ) (hp : p = 2*m+1) (a : Fin (m+1))
    (i : Fin (classDimension p m N h hp a)) : ℤ[X] :=
  (∏ c ∈ univ.erase a, classFactor p m N h hp c) * localRow p m N h hp a i

def crossClassQuotient (p m N h : ℕ) (hp : p = 2*m+1) (a b : Fin (m+1))
    (i : Fin (classDimension p m N h hp a))
    (j : Fin (classDimension p m N h hp b)) : ℤ[X] :=
  integerDenominator N ^ 5 * (∏ c ∈ (univ.erase a).erase b, classFactor p m N h hp c) *
    localRow p m N h hp a i * localRow p m N h hp b j

/-- Off-class rows cancel the entire surviving denominator over the integers. -/
theorem cross_class_exact_cancellation (p m N h : ℕ) (hp : p = 2*m+1)
    (a b : Fin (m+1)) (hab : a ≠ b)
    (i : Fin (classDimension p m N h hp a))
    (j : Fin (classDimension p m N h hp b)) :
    integerDenominator N ^ 5 * (globalRow p m N h hp a i * globalRow p m N h hp b j) =
      integerTailDenominator N h * crossClassQuotient p m N h hp a b i j := by
  unfold globalRow crossClassQuotient
  have hh := complements_product (classFactor p m N h hp) a b hab
  rw [classFactors_product] at hh
  calc
    _ = integerDenominator N ^ 5 *
        ((∏ c ∈ univ.erase a, classFactor p m N h hp c) *
         (∏ c ∈ univ.erase b, classFactor p m N h hp c)) *
        localRow p m N h hp a i * localRow p m N h hp b j := by ring
    _ = _ := by rw [hh]; ring

lemma mapped_integer_coeff_integral (p : ℕ) [Fact p.Prime] (P : ℤ[X]) (n : ℕ) :
    ‖((P.map (Int.castRingHom ℚ)).coeff n : ℚ_[p])‖ ≤ 1 := by
  rw [coeff_map]
  change ‖((P.coeff n : ℚ) : ℚ_[p])‖ ≤ 1
  rw [Rat.cast_intCast]
  exact Padic.norm_int_le_one _

lemma corrected_integer_moment_integral (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (P : ℤ[X]) :
    (0 : WithTop ℚ) ≤ rationalPadicValuation p
      (correctedMomentLinearMap p (P.map (Int.castRingHom ℚ))) := by
  rw [correctedMomentLinearMap_apply]
  apply (rationalPadicValuation_lower_iff p _ 0).mpr
  right
  have hh := (Padic.norm_le_one_iff_val_nonneg
    (correctedPolynomialMoment p (P.map (Int.castRingHom ℚ)) : ℚ_[p])).mp
    (correctedPolynomialMoment_integral hp _ (mapped_integer_coeff_integral p P))
  rw [Padic.valuation_ratCast] at hh
  exact_mod_cast hh

/-- Actual corrected off-class functional entries have integral coefficients.
This is the complete off-class case in the proof of Proposition 4.3. -/
theorem corrected_cross_class_entry_integral (p m N h : ℕ) [Fact p.Prime]
    (hp : p = 2*m+1) (hp7 : 7 ≤ p) (a b : Fin (m+1)) (hab : a ≠ b)
    (i : Fin (classDimension p m N h hp a))
    (j : Fin (classDimension p m N h hp b)) :
    CoeffLower (rationalPadicValuation p)
      (numeratorFunctional N h (correctedMomentLinearMap p)
        (denominator N ^ 5 *
          ((globalRow p m N h hp a i).map (Int.castRingHom ℚ) *
           (globalRow p m N h hp b j).map (Int.castRingHom ℚ)))) 0 := by
  have hh := congrArg (Polynomial.map (Int.castRingHom ℚ))
    (cross_class_exact_cancellation p m N h hp a b hab i j)
  simp only [Polynomial.map_mul, Polynomial.map_pow,
    map_integerDenominator, map_integerTailDenominator] at hh
  rw [hh, numeratorFunctional_cancel_all]
  exact coeffLower_C _ _ _ (corrected_integer_moment_integral p hp7 _)

#print axioms corrected_cross_class_entry_integral
end Zeta5OuterEntries
