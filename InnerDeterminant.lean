import InnerAssignedWeights
import NumeratorFunctional
import BasisTransfer

noncomputable section
open scoped BigOperators
open Polynomial Matrix
namespace Zeta5InnerDeterminant
open Zeta5Parameters Zeta5InnerBasis Zeta5InnerAssignedWeights
open Zeta5Construction Zeta5NumeratorFunctional Zeta5BasisTransfer Zeta5Outer

abbrev RowIndex (n M p : ℕ) := Σ a, Fin (dimension n M p a)

def classMatrix (n M p : ℕ) : Matrix (RowIndex n M p) (RowIndex n M p) ℚ[X] :=
  fun i j => numeratorFunctional (N n) (Zeta5Parameters.h n) polynomialFunctional
    (denominator (N n)^5*((row n M p i).map (Int.castRingHom ℚ)*
      (row n M p j).map (Int.castRingHom ℚ)))

def rowWeight (n M p : ℕ) (i : RowIndex n M p) : ℚ := (twiceWeight n M p i:ℚ)/2

lemma weight_sum (n M p : ℕ) : 2*(∑ i, rowWeight n M p i)=(innerExponent n M p:ℚ) := by
  unfold rowWeight
  rw [←Finset.sum_div, mul_div_cancel₀ _ (by norm_num : (2:ℚ)≠0), ←Int.cast_sum, sum_twiceWeight]

lemma basis_det_not_dvd (n M p : ℕ) [Fact p.Prime] (hodd : p%2=1) :
    ¬(p:ℤ)∣(basisMatrix n M p).det := by
  apply Zeta5ClassBasis.integer_class_det_unit p
    (fun a : Fin ((p-1)/2+1) => ((X:ℤ[X])+C ((a.val:ℤ)^2))^dimension n M p a)
    (dimension n M p)
    (fun a k => ((X:ℤ[X])+C ((a.val:ℤ)^2))^k.val)
  · simpa only [map_pow] using Zeta5ClassBasis.inner_class_factors_coprime p ((p-1)/2)
      (by omega) (dimension n M p)
  · intro a; exact (monic_X_add_C _).pow _
  · intro a; rw [degree_pow, degree_X_add_C]; simp
  · intro a k; exact (monic_X_add_C _).pow _
  · intro a k; rw [degree_pow, degree_X_add_C]; simp

lemma row_degree_lt (n M p : ℕ) (ha : Admissible n M) (hp : 3≤p)
    (hodd : p%2=1) (hinner : 3*p≤K n) (i : RowIndex n M p) :
    (row n M p i).natDegree<Zeta5Parameters.h n := by
  rw [row_natDegree, dimension_sum n M p ha hp hodd hinner]
  have hd : dimension n M p i.1≤Zeta5Parameters.h n := by
    rw [←dimension_sum n M p ha hp hodd hinner]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i.1)
  have hi := i.2.isLt
  omega

def rowEquiv (n M p : ℕ) (ha : Admissible n M) (hp : 3≤p)
    (hodd : p%2=1) (hinner : 3*p≤K n) : RowIndex n M p ≃ Fin (Zeta5Parameters.h n) :=
  (indexEquiv n M p).trans (finCongr (dimension_sum n M p ha hp hodd hinner))

def rationalBasis (n M p : ℕ) := (basisMatrix n M p).map (Int.castRingHom ℚ)

def rowMonomials (n M p : ℕ) (ha : Admissible n M) (hp : 3≤p)
    (hodd : p%2=1) (hinner : 3*p≤K n) : RowIndex n M p → ℚ[X] :=
  fun i => X^(rowEquiv n M p ha hp hodd hinner i).val

lemma rationalBasis_rows (n M p : ℕ) (ha : Admissible n M) (hp : 3≤p)
    (hodd : p%2=1) (hinner : 3*p≤K n) :
    basisRows (rationalBasis n M p) (rowMonomials n M p ha hp hodd hinner)=
      fun i => (row n M p i).map (Int.castRingHom ℚ) := by
  funext i
  let P := (row n M p i).map (Int.castRingHom ℚ)
  have hdeg : P.natDegree<Zeta5Parameters.h n :=
    Polynomial.natDegree_map_le.trans_lt (row_degree_lt n M p ha hp hodd hinner i)
  have hs := P.as_sum_range_C_mul_X_pow' hdeg
  rw [←Fin.sum_univ_eq_sum_range (fun k => C (P.coeff k)*X^k) (Zeta5Parameters.h n)] at hs
  have he := Equiv.sum_comp (rowEquiv n M p ha hp hodd hinner)
    (fun k : Fin (Zeta5Parameters.h n) => C (P.coeff k.val)*X^k.val)
  calc
    _ = ∑ j : RowIndex n M p, C (P.coeff (rowEquiv n M p ha hp hodd hinner j).val)*
        X^(rowEquiv n M p ha hp hodd hinner j).val := by
      simp only [basisRows, rationalBasis, rowMonomials, Matrix.map_apply, basisMatrix,
        smul_eq_C_mul, P, coeff_map]
      rfl
    _ = _ := he.trans hs.symm

def weightedFunctional (n : ℕ) : ℚ[X] →ₗ[ℚ] ℚ[X] :=
  (numeratorFunctional (N n) (Zeta5Parameters.h n) polynomialFunctional).comp
    (LinearMap.mulLeft ℚ (denominator (N n)^5))

attribute [local irreducible] rowEquiv

lemma classMatrix_congruence (n M p : ℕ) (ha : Admissible n M) (hp : 3≤p)
    (hodd : p%2=1) (hinner : 3*p≤K n) :
    classMatrix n M p = congruence
      ((hankelMatrix (N n) (Zeta5Parameters.h n)).submatrix (rowEquiv n M p ha hp hodd hinner)
        (rowEquiv n M p ha hp hodd hinner)) (rationalBasis n M p) := by
  have hg : gram (weightedFunctional n) (rowMonomials n M p ha hp hodd hinner) =
      (hankelMatrix (N n) (Zeta5Parameters.h n)).submatrix
        (rowEquiv n M p ha hp hodd hinner) (rowEquiv n M p ha hp hodd hinner) := by
    apply Matrix.ext
    intro i j
    simp only [gram, weightedFunctional, rowMonomials, LinearMap.comp_apply,
      LinearMap.mulLeft_apply, Matrix.submatrix_apply]
    rw [hankelMatrix_as_functional]

  rw [←hg, ←gram_basisRows, rationalBasis_rows]
  rfl

/-- Final determinant transfer. The local entry hypothesis is explicit here
and is discharged separately by the residue-disk functional estimates. -/
theorem determinant_bound_of_entries (n M p : ℕ) [Fact p.Prime]
    (ha : Admissible n M) (hp : 3≤p) (hodd : p%2=1) (hinner : 3*p≤K n)
    (hentries : ∀ i j, CoeffLower (rationalPadicValuation p) (classMatrix n M p i j)
      (rowWeight n M p i+rowWeight n M p j)) :
    CoeffLower (rationalPadicValuation p) (determinant (N n) (Zeta5Parameters.h n))
      (innerExponent n M p) := by
  have hd := weighted_det_bound (rationalPadicValuation p) (classMatrix n M p) (rowWeight n M p) hentries
  rw [weight_sum, classMatrix_congruence n M p ha hp hodd hinner] at hd
  have hu : rationalPadicValuation p (rationalBasis n M p).det=0 :=
    integer_det_valuation_zero p (basisMatrix n M p) (basis_det_not_dvd n M p hodd)
  have hh := (congruence_preserves_coeffLower (rationalPadicValuation p)
    ((hankelMatrix (N n) (Zeta5Parameters.h n)).submatrix
      (rowEquiv n M p ha hp hodd hinner) (rowEquiv n M p ha hp hodd hinner))
    (rationalBasis n M p) hu _).mp hd
  rw [Matrix.det_submatrix_equiv_self] at hh
  exact hh

#print axioms determinant_bound_of_entries
end Zeta5InnerDeterminant
