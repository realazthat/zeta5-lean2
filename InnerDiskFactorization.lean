import InnerRowFactors
import Mathlib.Algebra.Polynomial.Inductions

noncomputable section
open scoped BigOperators
open Polynomial
namespace Zeta5InnerDisk
open Zeta5ResidueFactorization Zeta5InnerFactorization

def shift (p : ℕ) (c : ℤ) : ℤ[X] := C (p:ℤ)*X+C c

def DiskFactor (p : ℕ) (c : ℤ) (P : ℤ[X]) (e : ℕ) (A B : ℤ[X]) : Prop :=
  P.comp (shift p c) = C ((p:ℤ)^e)*A*B.comp (C (p:ℤ)*X)

lemma DiskFactor.mul {p : ℕ} {c : ℤ} {P Q A B A' B' : ℤ[X]} {e f : ℕ}
    (hP : DiskFactor p c P e A B) (hQ : DiskFactor p c Q f A' B') :
    DiskFactor p c (P*Q) (e+f) (A*A') (B*B') := by
  unfold DiskFactor at *
  rw [mul_comp, hP, hQ, mul_comp, pow_add, map_mul]
  ring

lemma DiskFactor.pow {p : ℕ} {c : ℤ} {P A B : ℤ[X]} {e : ℕ}
    (hP : DiskFactor p c P e A B) (k : ℕ) :
    DiskFactor p c (P^k) (e*k) (A^k) (B^k) := by
  unfold DiskFactor at *
  rw [pow_comp, hP, pow_comp, pow_mul]
  simp only [map_pow]
  ring

lemma DiskFactor.const_mul {p : ℕ} {c : ℤ} {P A B : ℤ[X]} {e : ℕ}
    (hP : DiskFactor p c P e A B) (a : ℤ) :
    DiskFactor p c (C a*P) e A (C a*B) := by
  unfold DiskFactor at *
  rw [mul_comp, C_comp, hP, mul_comp, C_comp]
  ring

lemma translated_product_comp {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (r : ι → ℤ) (p : ℕ) (c : ℤ) :
    DiskFactor p c (∏ i ∈ s, (X-C (r i)))
      (nearIndices s r p c).card (nearPolynomial s r p c) (farPolynomial s r p c) := by
  unfold DiskFactor
  rw [Polynomial.prod_comp]
  have he : (∏ i ∈ s, (X-C (r i)).comp (shift p c)) =
      ∏ i ∈ s, (C (p:ℤ)*X+C (c-r i)) := by
    apply Finset.prod_congr rfl
    intro i hi
    simp only [sub_comp, X_comp, C_comp, shift, map_sub]
    ring
  rw [he]
  exact translated_product_factorization s r p c

lemma translated_weighted_product_comp {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (r : ι → ℤ) (w : ι → ℕ) (p : ℕ) (c : ℤ) :
    DiskFactor p c (∏ i ∈ s, (X-C (r i))^w i)
      (∑ i ∈ nearIndices s r p c, w i)
      (nearWeightedPolynomial s r w p c) (farWeightedPolynomial s r w p c) := by
  unfold DiskFactor
  rw [Polynomial.prod_comp]
  have he : (∏ i ∈ s, ((X-C (r i))^w i).comp (shift p c)) =
      ∏ i ∈ s, (C (p:ℤ)*X+C (c-r i))^w i := by
    apply Finset.prod_congr rfl
    intro i hi
    simp only [pow_comp, sub_comp, X_comp, C_comp, shift, map_sub]
    congr 1
    ring
  rw [he]
  exact translated_weighted_product_factorization s r w p c

def denPullback (A : ℕ) : ℤ[X] := (integerDenominator A).comp (-(X^2))
def denExponent (A p : ℕ) (c : ℤ) : ℕ := (nearIndices (signedIndices A) signedRoot p c).card
def denNear (A p : ℕ) (c : ℤ) : ℤ[X] := nearPolynomial (signedIndices A) signedRoot p c
def denFar (A p : ℕ) (c : ℤ) : ℤ[X] :=
  C ((-1:ℤ)^A)*farPolynomial (signedIndices A) signedRoot p c

lemma denPullback_signed (A : ℕ) : denPullback A = C ((-1:ℤ)^A)*signedProduct A := by
  rw [signedProduct_pullback]
  rw [← mul_assoc, ← map_mul, ← mul_pow]
  norm_num [denPullback]

lemma den_diskFactor (A p : ℕ) (c : ℤ) :
    DiskFactor p c (denPullback A) (denExponent A p c) (denNear A p c) (denFar A p c) := by
  rw [denPullback_signed]
  exact (translated_product_comp (signedIndices A) signedRoot p c).const_mul ((-1:ℤ)^A)

def rowPullback (m : ℕ) (ν : Fin (m+1) → ℕ) : ℤ[X] :=
  (Zeta5InnerRowFactors.rowPolynomial m ν).comp (-(X^2))
def rowExponent (m : ℕ) (ν : Fin (m+1) → ℕ) (p : ℕ) (c : ℤ) : ℕ :=
  ∑ i ∈ nearIndices Finset.univ (Zeta5InnerRowFactors.root m) p c, Zeta5InnerRowFactors.weight m ν i
def rowNear (m : ℕ) (ν : Fin (m+1) → ℕ) (p : ℕ) (c : ℤ) : ℤ[X] :=
  nearWeightedPolynomial Finset.univ (Zeta5InnerRowFactors.root m)
    (Zeta5InnerRowFactors.weight m ν) p c
def rowFar (m : ℕ) (ν : Fin (m+1) → ℕ) (p : ℕ) (c : ℤ) : ℤ[X] :=
  C ((-1:ℤ)^(∑ a,ν a))*farWeightedPolynomial Finset.univ
    (Zeta5InnerRowFactors.root m) (Zeta5InnerRowFactors.weight m ν) p c

lemma rowPullback_signed (m : ℕ) (ν : Fin (m+1) → ℕ) :
    rowPullback m ν = C ((-1:ℤ)^(∑ a,ν a))*
      ∏ i : Fin (m+1)×Bool, (X-C (Zeta5InnerRowFactors.root m i))^Zeta5InnerRowFactors.weight m ν i := by
  rw [Zeta5InnerRowFactors.row_pullback]
  rw [← mul_assoc, ← map_mul, ← mul_pow]
  norm_num [rowPullback]

lemma row_diskFactor (m : ℕ) (ν : Fin (m+1) → ℕ) (p : ℕ) (c : ℤ) :
    DiskFactor p c (rowPullback m ν) (rowExponent m ν p c) (rowNear m ν p c) (rowFar m ν p c) := by
  rw [rowPullback_signed]
  exact (translated_weighted_product_comp Finset.univ (Zeta5InnerRowFactors.root m)
    (Zeta5InnerRowFactors.weight m ν) p c).const_mul ((-1:ℤ)^(∑ a,ν a))

def xExponent (p : ℕ) (c : ℤ) : ℕ := if (p:ℤ)∣c then 5 else 0
def xNear (p : ℕ) (c : ℤ) : ℤ[X] := if (p:ℤ)∣c then (X+C (c/(p:ℤ)))^5 else 1
def xFar (p : ℕ) (c : ℤ) : ℤ[X] := if (p:ℤ)∣c then 1 else (X+C c)^5

lemma x_diskFactor (p : ℕ) (c : ℤ) :
    DiskFactor p c (X^5) (xExponent p c) (xNear p c) (xFar p c) := by
  unfold DiskFactor xExponent xNear xFar shift
  by_cases hc : (p:ℤ)∣c
  · simp only [hc, if_true, pow_comp, X_comp, one_comp, mul_one]
    have he := near_factor p c 0 (by simpa using hc)
    simp only [sub_zero] at he
    rw [he, mul_pow, map_pow]
  · simp only [hc, if_false, pow_zero, map_one, one_mul, pow_comp, X_comp,
      add_comp, C_comp]

def numeratorPullback (N m : ℕ) (ν κ : Fin (m+1) → ℕ) : ℤ[X] :=
  X^5*(denPullback N)^6*rowPullback m ν*rowPullback m κ
def numeratorExponent (N m p : ℕ) (c : ℤ) (ν κ : Fin (m+1) → ℕ) : ℕ :=
  xExponent p c+denExponent N p c*6+rowExponent m ν p c+rowExponent m κ p c
def numeratorNear (N m p : ℕ) (c : ℤ) (ν κ : Fin (m+1) → ℕ) : ℤ[X] :=
  xNear p c*(denNear N p c)^6*rowNear m ν p c*rowNear m κ p c
def numeratorFar (N m p : ℕ) (c : ℤ) (ν κ : Fin (m+1) → ℕ) : ℤ[X] :=
  xFar p c*(denFar N p c)^6*rowFar m ν p c*rowFar m κ p c

theorem numerator_diskFactor (N m p : ℕ) (c : ℤ) (ν κ : Fin (m+1) → ℕ) :
    DiskFactor p c (numeratorPullback N m ν κ) (numeratorExponent N m p c ν κ)
      (numeratorNear N m p c ν κ) (numeratorFar N m p c ν κ) :=
  (((x_diskFactor p c).mul ((den_diskFactor N p c).pow 6)).mul (row_diskFactor m ν p c)).mul
    (row_diskFactor m κ p c)

def farRemainder (p : ℕ) (B : ℤ[X]) : ℤ[X] := X*B.divX.comp (C (p:ℤ)*X)

lemma farPolynomial_split (p : ℕ) (B : ℤ[X]) :
    B.comp (C (p:ℤ)*X) = C (B.coeff 0)+C (p:ℤ)*farRemainder p B := by
  have he := congrArg (fun P : ℤ[X] => P.comp (C (p:ℤ)*X)) (X_mul_divX_add B)
  simp only [add_comp, mul_comp, X_comp, C_comp] at he
  unfold farRemainder
  rw [← he]
  ring

def leadingNumerator (A B : ℤ[X]) : ℤ[X] := C (B.coeff 0)*A
def higherNumerator (p : ℕ) (A B : ℤ[X]) : ℤ[X] := A*farRemainder p B

lemma numerator_split (p : ℕ) (A B : ℤ[X]) :
    A*B.comp (C (p:ℤ)*X) = leadingNumerator A B+C (p:ℤ)*higherNumerator p A B := by
  rw [farPolynomial_split]
  unfold leadingNumerator higherNumerator
  ring

lemma leadingNumerator_degree_le (A B : ℤ[X]) :
    (leadingNumerator A B).natDegree ≤ A.natDegree := by
  exact natDegree_C_mul_le _ _

theorem numerator_disk_split (N m p : ℕ) (c : ℤ) (ν κ : Fin (m+1) → ℕ) :
    (numeratorPullback N m ν κ).comp (shift p c) =
      C ((p:ℤ)^(numeratorExponent N m p c ν κ))*
        (leadingNumerator (numeratorNear N m p c ν κ) (numeratorFar N m p c ν κ)+
          C (p:ℤ)*higherNumerator p (numeratorNear N m p c ν κ) (numeratorFar N m p c ν κ)) := by
  rw [← numerator_split, ← mul_assoc]
  exact numerator_diskFactor N m p c ν κ

theorem denominator_disk_split (K p : ℕ) (c : ℤ) :
    (denPullback K).comp (shift p c) =
      C ((p:ℤ)^denExponent K p c)*denNear K p c*
        (C ((denFar K p c).coeff 0)+C (p:ℤ)*farRemainder p (denFar K p c)) := by
  rw [← farPolynomial_split]
  exact den_diskFactor K p c

theorem denominator_constant_unit (K p : ℕ) [Fact p.Prime] (c : ℤ) :
    ¬ (p:ℤ)∣(denFar K p c).coeff 0 := by
  have hf := farPolynomial_constant_unit (signedIndices K) signedRoot p c
  simp only [denFar, coeff_C_mul]
  intro hd
  rcases neg_one_pow_eq_or ℤ K with hs | hs
  · simp only [hs, one_mul] at hd
    exact hf hd
  · simp only [hs, neg_one_mul, dvd_neg] at hd
    exact hf hd

#print axioms numerator_disk_split
#print axioms denominator_disk_split
#print axioms denominator_constant_unit
end Zeta5InnerDisk

