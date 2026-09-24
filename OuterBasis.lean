import ClassBasis
import OuterMoments

/-!
# The actual class basis for the outer-prime range

Class factors contain the surviving integer-square poles. The local rows
use the factors above p first, exactly as in equation (4.11).
-/
noncomputable section
open scoped BigOperators
open Polynomial Finset

namespace Zeta5OuterBasis
open Zeta5Construction Zeta5ClassBasis

/-- Canonical ordinary/zero square-class representative, in [0,(p-1)/2]. -/
def poleClass (p m j : ℕ) (hp : p = 2*m+1) : Fin (m+1) :=
  ⟨min (j%p) (p-j%p), by
    have hpos : 0 < p := by omega
    have hr := Nat.mod_lt j hpos
    by_cases h : j%p ≤ m
    · exact lt_of_le_of_lt (min_le_left _ _) (by omega)
    · exact lt_of_le_of_lt (min_le_right _ _) (by omega)⟩

lemma poleClass_square (p m j : ℕ) [Fact p.Prime] (hp : p = 2*m+1) :
    ((poleClass p m j hp).val : ZMod p)^2 = (j : ZMod p)^2 := by
  have hpos : 0 < p := by omega
  have hr := Nat.mod_lt j hpos
  by_cases h : j%p ≤ p-j%p
  · simp [poleClass, min_eq_left h]
  · simp only [poleClass, min_eq_right (le_of_not_ge h)]
    rw [Nat.cast_sub hr.le, ZMod.natCast_self, zero_sub, neg_sq]
    simp

def classMembers (p m N h : ℕ) (hp : p = 2*m+1) (a : Fin (m+1)) : Finset (Fin h) :=
  univ.filter fun i => poleClass p m (poleIndex N i) hp = a

def classDimension (p m N h : ℕ) (hp : p = 2*m+1) (a : Fin (m+1)) : ℕ :=
  (classMembers p m N h hp a).card

def classFactor (p m N h : ℕ) (hp : p = 2*m+1) (a : Fin (m+1)) : Polynomial ℤ :=
  ∏ i ∈ classMembers p m N h hp a, (X+C ((poleIndex N i : ℤ)^2))

def farFactor (p m N h : ℕ) (hp : p = 2*m+1) (a : Fin (m+1)) : Polynomial ℤ :=
  ∏ i ∈ (classMembers p m N h hp a).filter (fun i => p < poleIndex N i),
    (X+C ((poleIndex N i : ℤ)^2))

lemma classDimension_sum (p m N h : ℕ) (hp : p = 2*m+1) :
    (∑ a : Fin (m+1), classDimension p m N h hp a) = h := by
  have hh := Finset.card_eq_sum_card_fiberwise
    (s := (univ : Finset (Fin h))) (t := (univ : Finset (Fin (m+1))))
    (f := fun i => poleClass p m (poleIndex N i) hp) (by simp)
  simpa [classDimension, classMembers] using hh.symm

lemma classFactor_monic (p m N h : ℕ) (hp : p = 2*m+1) (a : Fin (m+1)) :
    (classFactor p m N h hp a).Monic := by
  unfold classFactor
  exact Polynomial.monic_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_add_C _)

lemma farFactor_monic (p m N h : ℕ) (hp : p = 2*m+1) (a : Fin (m+1)) :
    (farFactor p m N h hp a).Monic := by
  unfold farFactor
  exact Polynomial.monic_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_add_C _)

lemma classFactor_natDegree (p m N h : ℕ) (hp : p = 2*m+1) (a : Fin (m+1)) :
    (classFactor p m N h hp a).natDegree = classDimension p m N h hp a := by
  unfold classFactor classDimension
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_add_C _)]
  simp only [Polynomial.natDegree_X_add_C, Finset.sum_const, nsmul_eq_mul, mul_one]
  rfl

lemma classFactor_map (p m N h : ℕ) [Fact p.Prime] (hp : p = 2*m+1) (a : Fin (m+1)) :
    (classFactor p m N h hp a).map (Int.castRingHom (ZMod p)) =
      ((X : Polynomial (ZMod p))+C ((a.val : ZMod p)^2)) ^ classDimension p m N h hp a := by
  unfold classFactor
  rw [Polynomial.map_prod]
  calc
    (∏ i ∈ classMembers p m N h hp a,
        (X+C ((poleIndex N i : ℤ)^2)).map (Int.castRingHom (ZMod p))) =
      ∏ _i ∈ classMembers p m N h hp a, ((X : Polynomial (ZMod p))+C ((a.val : ZMod p)^2)) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hi' := (mem_filter.mp hi).2
        have hs := poleClass_square p m (poleIndex N i) hp
        rw [hi'] at hs
        have hv : (Int.castRingHom (ZMod p)) ((poleIndex N i : ℤ)^2) = (a.val : ZMod p)^2 := by
          simpa only [map_pow, map_natCast] using hs.symm
        simp only [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C, hv]
    _ = _ := by simp [classDimension]

lemma classFactor_coprime (p m N h : ℕ) [Fact p.Prime] (hp : p = 2*m+1) :
    Pairwise fun a b : Fin (m+1) => IsCoprime
      ((classFactor p m N h hp a).map (Int.castRingHom (ZMod p)))
      ((classFactor p m N h hp b).map (Int.castRingHom (ZMod p))) := by
  intro a b hab
  rw [classFactor_map, classFactor_map]
  have hc := pairwise_coprime_X_sub_C (square_class_injective p m (by omega)) hab
  have hh := hc.pow (m := classDimension p m N h hp a) (n := classDimension p m N h hp b)
  simpa only [map_neg, sub_neg_eq_add] using hh

/-- The class factors partition the original surviving denominator exactly. -/
theorem classFactors_product (p m N h : ℕ) (hp : p = 2*m+1) :
    (∏ a : Fin (m+1), classFactor p m N h hp a) =
      Zeta5OuterMoments.integerTailDenominator N h := by
  unfold classFactor classMembers Zeta5OuterMoments.integerTailDenominator
  simpa only [poleIndex] using Finset.prod_fiberwise
    (univ : Finset (Fin h)) (fun i => poleClass p m (poleIndex N i) hp)
    (fun i => (X+C ((poleIndex N i : ℤ)^2) : Polynomial ℤ))

lemma farFactor_dvd_classFactor (p m N h : ℕ) (hp : p = 2*m+1) (a : Fin (m+1)) :
    farFactor p m N h hp a ∣ classFactor p m N h hp a := by
  unfold farFactor classFactor
  apply Finset.prod_dvd_prod_of_subset
  exact Finset.filter_subset _ _

/-- Equation (4.11), with the switch expressed by the actual far-factor degree.
The zero class uses rows `1, X+p²` (and their monic continuation). -/
def localRow (p m N h : ℕ) (hp : p = 2*m+1) (a : Fin (m+1))
    (i : Fin (classDimension p m N h hp a)) : Polynomial ℤ :=
  if a.val = 0 then (X+C ((p : ℤ)^2))^i.val else
  if i.val < (farFactor p m N h hp a).natDegree then (X+C ((a.val : ℤ)^2))^i.val else
    farFactor p m N h hp a *
      (X+C ((a.val : ℤ)^2))^(i.val-(farFactor p m N h hp a).natDegree)

lemma localRow_monic (p m N h : ℕ) (hp : p = 2*m+1) (a : Fin (m+1))
    (i : Fin (classDimension p m N h hp a)) : (localRow p m N h hp a i).Monic := by
  unfold localRow
  split_ifs
  · exact (Polynomial.monic_X_add_C _).pow _
  · exact (Polynomial.monic_X_add_C _).pow _
  · exact (farFactor_monic p m N h hp a).mul ((Polynomial.monic_X_add_C _).pow _)

lemma localRow_natDegree (p m N h : ℕ) (hp : p = 2*m+1) (a : Fin (m+1))
    (i : Fin (classDimension p m N h hp a)) : (localRow p m N h hp a i).natDegree = i.val := by
  unfold localRow
  split_ifs with ha hi
  · rw [(Polynomial.monic_X_add_C _).natDegree_pow, Polynomial.natDegree_X_add_C, mul_one]
  · rw [(Polynomial.monic_X_add_C _).natDegree_pow, Polynomial.natDegree_X_add_C, mul_one]
  · rw [(farFactor_monic p m N h hp a).natDegree_mul ((Polynomial.monic_X_add_C _).pow _),
      (Polynomial.monic_X_add_C _).natDegree_pow, Polynomial.natDegree_X_add_C, mul_one]
    omega

/-- Every high-index ordinary row cancels all the poles above `p` in its class. -/
theorem farFactor_dvd_high_localRow (p m N h : ℕ) (hp : p = 2*m+1) (a : Fin (m+1))
    (i : Fin (classDimension p m N h hp a)) (ha : a.val ≠ 0)
    (hi : (farFactor p m N h hp a).natDegree ≤ i.val) :
    farFactor p m N h hp a ∣ localRow p m N h hp a i := by
  simp only [localRow, if_neg ha, if_neg (not_lt_of_ge hi)]
  exact dvd_mul_right _ _

/-- A coefficient-index enumeration, with its size equality proved from the actual pole partition. -/
def classIndexEquiv (p m N h : ℕ) (hp : p = 2*m+1) :
    (Σ a : Fin (m+1), Fin (classDimension p m N h hp a)) ≃
      Fin (∑ a, classDimension p m N h hp a) := Fintype.equivOfCardEq (by simp)

def basisMatrix (p m N h : ℕ) (hp : p = 2*m+1) :
    Matrix (Σ a : Fin (m+1), Fin (classDimension p m N h hp a))
      (Σ a : Fin (m+1), Fin (classDimension p m N h hp a)) ℤ := fun i j =>
  ((∏ a ∈ univ.erase i.1, classFactor p m N h hp a) * localRow p m N h hp i.1 i.2).coeff
    (classIndexEquiv p m N h hp j).val

/-- The actual outer basis is p-unimodular. No coprimality or degree hypotheses
are left for the caller: they follow from its explicit square-class factors. -/
theorem basisMatrix_det_not_dvd (p m N h : ℕ) [Fact p.Prime] (hp : p = 2*m+1) :
    ¬ (p : ℤ) ∣ (basisMatrix p m N h hp).det := by
  apply integer_class_det_unit p
    (classFactor p m N h hp) (classDimension p m N h hp) (localRow p m N h hp)
    (classFactor_coprime p m N h hp) (classFactor_monic p m N h hp)
  · intro a
    rw [Polynomial.degree_eq_natDegree (classFactor_monic p m N h hp a).ne_zero,
      classFactor_natDegree]
  · exact localRow_monic p m N h hp
  · intro a i
    rw [Polynomial.degree_eq_natDegree (localRow_monic p m N h hp a i).ne_zero,
      localRow_natDegree]

/-- The outer basis change has zero p-adic determinant valuation. -/
theorem basisMatrix_det_valuation (p m N h : ℕ) [Fact p.Prime] (hp : p = 2*m+1) :
    padicValInt p (basisMatrix p m N h hp).det = 0 :=
  padicValInt.eq_zero_of_not_dvd (basisMatrix_det_not_dvd p m N h hp)

#print axioms basisMatrix_det_not_dvd
#print axioms basisMatrix_det_valuation

end Zeta5OuterBasis
