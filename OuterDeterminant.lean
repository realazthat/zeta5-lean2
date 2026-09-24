import OuterZero
import BasisTransfer

/-! Assembly of the actual outer entries and determinant rank correction. -/
noncomputable section
open scoped BigOperators
open Polynomial Finset Matrix
namespace Zeta5OuterDeterminant
open Zeta5Construction Zeta5OuterMoments Zeta5OuterBasis Zeta5OuterNear Zeta5OuterArithmetic
open Zeta5Outer Zeta5OuterEntries Zeta5NumeratorFunctional Zeta5FunctionalCancellation
open Zeta5OuterLow Zeta5OuterZero Zeta5BasisTransfer

abbrev RowIndex (p m N h : ℕ) (hp : p = 2*m+1) :=
  Σ a : Fin (m+1), Fin (classDimension p m N h hp a)

def rowWeight (p m N h : ℕ) (hp : p = 2*m+1) (i : RowIndex p m N h hp) : ℚ :=
  if i.1.val = 0 then zeroWeight p m N h hp i.1 i.2 else ordinaryWeight p m N h hp i.1 i.2

lemma rowWeight_nonpos (p m N h : ℕ) (hp : p = 2*m+1) (hK : N+h < 3*p)
    (i : RowIndex p m N h hp) : rowWeight p m N h hp i ≤ 0 := by
  unfold rowWeight
  split_ifs with ha
  · exact zeroWeight_nonpos p m N h hp hK i.1 ha i.2
  · exact ordinaryWeight_nonpos p m N h hp i.1 i.2

def correctedClassMatrix (p m N h : ℕ) (hp : p = 2*m+1) :
    Matrix (RowIndex p m N h hp) (RowIndex p m N h hp) ℚ[X] := fun i j =>
  numeratorFunctional N h (correctedMomentLinearMap p)
    (denominator N ^ 5 * ((globalRow p m N h hp i.1 i.2).map (Int.castRingHom ℚ) *
      (globalRow p m N h hp j.1 j.2).map (Int.castRingHom ℚ)))

/-- Every entry estimate for the actual outer class matrix is proved here. -/
theorem correctedClassMatrix_weighted (p m N h : ℕ) [Fact p.Prime]
    (hp : p = 2*m+1) (hp7 : 7 ≤ p) (hK : N+h < 3*p) (hK2 : 2*(N+h) < p^2)
    (hNp : 2*N < p) (hKp : p ≤ N+h) (i j : RowIndex p m N h hp) :
    CoeffLower (rationalPadicValuation p) (correctedClassMatrix p m N h hp i j)
      (rowWeight p m N h hp i + rowWeight p m N h hp j) := by
  rcases i with ⟨a,i⟩
  rcases j with ⟨b,j⟩
  by_cases hab : a = b
  · subst b
    by_cases ha : a.val = 0
    · simpa only [correctedClassMatrix, rowWeight, if_pos ha] using
        zero_entry_weighted_bound p m N h hp hp7 hK hK2 a ha i j
    · simpa only [correctedClassMatrix, rowWeight, if_neg ha] using
        ordinary_entry_weighted_bound p m N h hp hp7 hK2 hNp hKp a (by omega) i j
  · apply coeffLower_mono _ (corrected_cross_class_entry_integral p m N h hp hp7 a b hab i j)
    exact add_nonpos (rowWeight_nonpos p m N h hp hK ⟨a,i⟩)
      (rowWeight_nonpos p m N h hp hK ⟨b,j⟩)

section CoarseRank
variable {F ι : Type*} [Field F] [Infinite F] [Fintype ι] [DecidableEq ι]

lemma coarse_permutation_bound (w : ι → ℚ) (hw : ∀ i, w i ≤ 0)
    (s : Finset ι) (σ : Equiv.Perm ι) (r : ℕ) (hs : s.card ≤ r) :
    2*(∑ i, w i) - r ≤ ∑ i, if i ∈ s then (-1 : ℚ) else w i+w (σ i) := by
  have hh : (∑ i, (w i+w (σ i)-(if i ∈ s then 1 else 0))) ≤
      ∑ i, if i ∈ s then (-1 : ℚ) else w i+w (σ i) := by
    apply Finset.sum_le_sum
    intro i hi
    by_cases his : i ∈ s
    · simp only [if_pos his]
      have hi := hw i
      have hj := hw (σ i)
      linarith
    · simp only [if_neg his, sub_zero, le_refl]
  have hcard : (∑ i : ι, if i ∈ s then (1 : ℚ) else 0) = s.card := by simp
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Equiv.sum_comp σ w, hcard] at hh
  have hsr : (s.card : ℚ) ≤ r := by exact_mod_cast hs
  linarith

/-- The coarser rank correction, allowing arbitrary nonpositive rational weights.
Its loss is r, which avoids counting zero-weight rows in the final normalization. -/
theorem polynomial_det_coarse_rank_correction (v : AddValuation F (WithTop ℚ))
    (A : Matrix ι ι F[X]) (B : Matrix ι ι F) (w : ι → ℚ) (r : ℕ)
    (hw : ∀ i, w i ≤ 0) (hA : ∀ i j, CoeffLower v (A i j) (w i+w j))
    (hB : ∀ i j, (-1 : WithTop ℚ) ≤ v (B i j)) (hrank : B.rank ≤ r) :
    CoeffLower v (A+B.map C).det (2*(∑ i, w i)-r) := by
  have hexpand : (B.map C+A).det =
      ∑ s : Finset ι, Matrix.det (s.piecewise (B.map C) A) :=
    Matrix.detRowAlternating.toMultilinearMap.map_add_univ _ A
  rw [add_comm A (B.map C), hexpand]
  apply coeffLower_sum
  intro s hs
  by_cases hsr : s.card ≤ r
  · apply polynomial_det_lower_of_permutation_bounds v
      (s.piecewise (B.map C) A) (fun i j => if i ∈ s then -1 else w i+w j)
    · intro i j
      by_cases hi : i ∈ s
      · simpa [hi, Finset.piecewise, Matrix.map_apply] using coeffLower_C v (B i j) (-1) (hB i j)
      · simpa [hi, Finset.piecewise] using hA i j
    · intro σ
      exact coarse_permutation_bound w hw s σ r hsr
  · rw [mixed_polynomial_det_eq_zero_of_rank_lt A B s
      (lt_of_le_of_lt hrank (Nat.lt_of_not_ge hsr))]
    exact coeffLower_zero v _

end CoarseRank
#print axioms correctedClassMatrix_weighted
#print axioms polynomial_det_coarse_rank_correction
def rowEquiv (p m N h : ℕ) (hp : p = 2*m+1) : RowIndex p m N h hp ≃ Fin h :=
  (classIndexEquiv p m N h hp).trans (finCongr (classDimension_sum p m N h hp))

lemma rowEquiv_val (p m N h : ℕ) (hp : p = 2*m+1) (i : RowIndex p m N h hp) :
    (rowEquiv p m N h hp i).val = (classIndexEquiv p m N h hp i).val := rfl

lemma globalRow_natDegree_lt (p m N h : ℕ) (hp : p = 2*m+1) (i : RowIndex p m N h hp) :
    (globalRow p m N h hp i.1 i.2).natDegree < h := by
  have hm : (∏ c ∈ univ.erase i.1, classFactor p m N h hp c).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun c _ => classFactor_monic p m N h hp c)
  rw [globalRow, hm.natDegree_mul (localRow_monic p m N h hp i.1 i.2),
    localRow_natDegree, Polynomial.natDegree_prod_of_monic _ _ (fun c _ => classFactor_monic p m N h hp c)]
  simp only [classFactor_natDegree]
  have hs := Finset.sum_erase_add univ (classDimension p m N h hp) (mem_univ i.1)
  rw [classDimension_sum] at hs
  have hi := i.2.isLt
  omega

def rationalBasis (p m N h : ℕ) (hp : p = 2*m+1) :
    Matrix (RowIndex p m N h hp) (RowIndex p m N h hp) ℚ :=
  (basisMatrix p m N h hp).map (Int.castRingHom ℚ)

def rowMonomials (p m N h : ℕ) (hp : p = 2*m+1) : RowIndex p m N h hp → ℚ[X] :=
  fun i => X^(rowEquiv p m N h hp i).val

lemma rationalBasis_rows (p m N h : ℕ) (hp : p = 2*m+1) :
    basisRows (rationalBasis p m N h hp) (rowMonomials p m N h hp) =
      fun i => (globalRow p m N h hp i.1 i.2).map (Int.castRingHom ℚ) := by
  funext i
  let P := (globalRow p m N h hp i.1 i.2).map (Int.castRingHom ℚ)
  have hdeg : P.natDegree < h :=
    lt_of_le_of_lt Polynomial.natDegree_map_le (globalRow_natDegree_lt p m N h hp i)
  have hs := P.as_sum_range_C_mul_X_pow' hdeg
  rw [← Fin.sum_univ_eq_sum_range (fun k => C (P.coeff k)*X^k) h] at hs
  have he := Equiv.sum_comp (rowEquiv p m N h hp) (fun k : Fin h => C (P.coeff k.val)*X^k.val)
  calc
    _ = ∑ j : RowIndex p m N h hp, C (P.coeff (rowEquiv p m N h hp j).val) *
      X^(rowEquiv p m N h hp j).val := by
      simp only [basisRows, rationalBasis, rowMonomials, Matrix.map_apply, basisMatrix,
        smul_eq_C_mul, P, coeff_map, rowEquiv_val, globalRow]
    _ = _ := he.trans hs.symm

/-- The source numerator functional after multiplication by D_N^5. -/
def weightedFunctional (N h : ℕ) (μ : ℚ[X] →ₗ[ℚ] ℚ) : ℚ[X] →ₗ[ℚ] ℚ[X] :=
  (numeratorFunctional N h μ).comp (LinearMap.mulLeft ℚ (denominator N ^ 5))

lemma correctedClassMatrix_congruence (p m N h : ℕ) (hp : p = 2*m+1) :
    correctedClassMatrix p m N h hp =
      congruence ((actualCorrectedHankel N h p).submatrix (rowEquiv p m N h hp)
        (rowEquiv p m N h hp)) (rationalBasis p m N h hp) := by
  have hg : gram (weightedFunctional N h (correctedMomentLinearMap p)) (rowMonomials p m N h hp) =
      (actualCorrectedHankel N h p).submatrix (rowEquiv p m N h hp) (rowEquiv p m N h hp) := by
    apply Matrix.ext
    intro i j
    exact (actualCorrectedHankel_as_functional N h p _ _).symm
  rw [← hg, ← gram_basisRows, rationalBasis_rows]
  rfl

#print axioms correctedClassMatrix_congruence
section IntegralMatrices
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]

lemma integral_matrix_mul (v : AddValuation F (WithTop ℚ)) (A B : Matrix ι ι F)
    (hA : ∀ i j, (0 : WithTop ℚ) ≤ v (A i j))
    (hB : ∀ i j, (0 : WithTop ℚ) ≤ v (B i j)) :
    ∀ i j, (0 : WithTop ℚ) ≤ v ((A*B) i j) := by
  intro i j
  rw [Matrix.mul_apply]
  apply v.map_le_sum
  intro k hk
  rw [AddValuation.map_mul]
  simpa only [zero_add] using add_le_add (hA i k) (hB k j)

lemma congruence_add_constant (A : Matrix ι ι F[X]) (L B : Matrix ι ι F) (c : F) :
    congruence (A+(c • L).map C) B =
      congruence A B + (c • (B*L*Bᵀ)).map C := by
  unfold congruence
  rw [Matrix.mul_add, Matrix.add_mul]
  congr 1
  rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]
  congr 1
  rw [Matrix.mul_smul, Matrix.smul_mul]

end IntegralMatrices

def classCorrectionMatrix (p m N h : ℕ) (hp : p = 2*m+1) :
    Matrix (RowIndex p m N h hp) (RowIndex p m N h hp) ℚ :=
  rationalBasis p m N h hp *
    (actualCorrectionMatrix N h p).submatrix (rowEquiv p m N h hp) (rowEquiv p m N h hp) *
      (rationalBasis p m N h hp)ᵀ

lemma rationalBasis_integral (p m N h : ℕ) [Fact p.Prime] (hp : p = 2*m+1)
    (i j : RowIndex p m N h hp) :
    (0 : WithTop ℚ) ≤ rationalPadicValuation p (rationalBasis p m N h hp i j) :=
  rationalPadicValuation_int_nonneg p (basisMatrix p m N h hp i j)

lemma classCorrectionMatrix_integral (p m N h : ℕ) [Fact p.Prime]
    (hp : p = 2*m+1) (hp7 : 7 ≤ p) (i j : RowIndex p m N h hp) :
    (0 : WithTop ℚ) ≤ rationalPadicValuation p (classCorrectionMatrix p m N h hp i j) := by
  apply integral_matrix_mul (rationalPadicValuation p)
  · apply integral_matrix_mul (rationalPadicValuation p)
    · exact rationalBasis_integral p m N h hp
    · intro a b
      apply (rationalPadicValuation_lower_iff p _ 0).mpr
      right
      have hh := (Padic.norm_le_one_iff_val_nonneg
        (actualCorrectionMatrix N h p (rowEquiv p m N h hp a) (rowEquiv p m N h hp b) : ℚ_[p])).mp
        (actualCorrectionMatrix_integral hp7 N h _ _)
      rw [Padic.valuation_ratCast] at hh
      exact_mod_cast hh
  · intro a b
    exact rationalBasis_integral p m N h hp b a

lemma classCorrectionMatrix_rank (p m N h : ℕ) [Fact p.Prime]
    (hp : p = 2*m+1) (hp7 : 7 ≤ p) :
    (classCorrectionMatrix p m N h hp).rank ≤ (N+h)+4*N+2-2*p := by
  unfold classCorrectionMatrix
  apply (Matrix.rank_mul_le_left _ _).trans
  apply (Matrix.rank_mul_le_right _ _).trans
  rw [Matrix.rank_submatrix]
  exact actualCorrectionMatrix_rank hp7 N h

/-- The source correction identity survives the actual p-unimodular class change. -/
theorem actual_class_correction_decomposition (p m N h : ℕ) [Fact p.Prime]
    (hp : p = 2*m+1) :
    congruence ((hankelMatrix N h).submatrix (rowEquiv p m N h hp) (rowEquiv p m N h hp))
      (rationalBasis p m N h hp) = correctedClassMatrix p m N h hp +
        (((p : ℚ)⁻¹ • classCorrectionMatrix p m N h hp).map C) := by
  have heq : (hankelMatrix N h).submatrix (rowEquiv p m N h hp) (rowEquiv p m N h hp) =
      (actualCorrectedHankel N h p).submatrix (rowEquiv p m N h hp) (rowEquiv p m N h hp) +
        (((p : ℚ)⁻¹ • (actualCorrectionMatrix N h p).submatrix
          (rowEquiv p m N h hp) (rowEquiv p m N h hp)).map C) := by
    apply Matrix.ext
    intro i j
    exact congrArg (fun A => A (rowEquiv p m N h hp i) (rowEquiv p m N h hp j))
      (actual_hankel_correction_decomposition (p := p) N h)
  rw [heq, congruence_add_constant, ← correctedClassMatrix_congruence]
  rfl

#print axioms classCorrectionMatrix_integral
#print axioms classCorrectionMatrix_rank
#print axioms actual_class_correction_decomposition
/-- An unconditional source-specific outer determinant estimate in terms of
its explicit row weights. Every entry bound, basis change, and rank hypothesis
has been discharged; only finite weight aggregation remains to identify (4.14). -/
theorem actual_outer_determinant_coeffLower (p m N h : ℕ) [Fact p.Prime]
    (hp : p = 2*m+1) (hp7 : 7 ≤ p) (hK : N+h < 3*p) (hK2 : 2*(N+h) < p^2)
    (hNp : 2*N < p) (hKp : p ≤ N+h) :
    CoeffLower (rationalPadicValuation p) (determinant N h)
      (2*(∑ i : RowIndex p m N h hp, rowWeight p m N h hp i)-
        (((N+h)+4*N+2-2*p : ℕ) : ℚ)) := by
  have hpv : (-1 : WithTop ℚ) ≤ rationalPadicValuation p (p : ℚ)⁻¹ := by
    apply (rationalPadicValuation_lower_iff p _ (-1)).mpr
    right
    rw [padicValRat.inv, padicValRat.self (Fact.out : p.Prime).one_lt]
    norm_num
  have hB : ∀ i j : RowIndex p m N h hp,
      (-1 : WithTop ℚ) ≤ rationalPadicValuation p
        (((p : ℚ)⁻¹ • classCorrectionMatrix p m N h hp) i j) := by
    intro i j
    rw [Matrix.smul_apply, smul_eq_mul, AddValuation.map_mul]
    simpa only [add_zero] using add_le_add hpv (classCorrectionMatrix_integral p m N h hp hp7 i j)
  have hr : (((p : ℚ)⁻¹ • classCorrectionMatrix p m N h hp)).rank ≤ (N+h)+4*N+2-2*p := by
    have he : (p : ℚ)⁻¹ • classCorrectionMatrix p m N h hp =
        Matrix.diagonal (fun _ : RowIndex p m N h hp => (p : ℚ)⁻¹) * classCorrectionMatrix p m N h hp := by
      ext i j
      simp [Matrix.diagonal_mul]
    rw [he]
    exact (Matrix.rank_mul_le_right _ _).trans (classCorrectionMatrix_rank p m N h hp hp7)
  have hd := polynomial_det_coarse_rank_correction (rationalPadicValuation p)
    (correctedClassMatrix p m N h hp) ((p : ℚ)⁻¹ • classCorrectionMatrix p m N h hp)
    (rowWeight p m N h hp) ((N+h)+4*N+2-2*p) (rowWeight_nonpos p m N h hp hK)
    (correctedClassMatrix_weighted p m N h hp hp7 hK hK2 hNp hKp) hB hr
  rw [← actual_class_correction_decomposition] at hd
  have hu : rationalPadicValuation p (rationalBasis p m N h hp).det = 0 :=
    integer_det_valuation_zero p (basisMatrix p m N h hp) (basisMatrix_det_not_dvd p m N h hp)
  have hh := (congruence_preserves_coeffLower (rationalPadicValuation p)
    ((hankelMatrix N h).submatrix (rowEquiv p m N h hp) (rowEquiv p m N h hp))
    (rationalBasis p m N h hp) hu _).mp hd
  rw [Matrix.det_submatrix_equiv_self] at hh
  exact hh

/-- The same actual estimate in the guarded integer-valued API used by normalization. -/
theorem actual_outer_determinant_bound (p m N h : ℕ) [Fact p.Prime]
    (hp : p = 2*m+1) (hp7 : 7 ≤ p) (hK : N+h < 3*p) (hK2 : 2*(N+h) < p^2)
    (hNp : 2*N < p) (hKp : p ≤ N+h) (k : ℕ) (hk : (determinant N h).coeff k ≠ 0) :
    2*(∑ i : RowIndex p m N h hp, rowWeight p m N h hp i)-
      (((N+h)+4*N+2-2*p : ℕ) : ℚ) ≤ (padicValRat p ((determinant N h).coeff k) : ℚ) := by
  exact ((rationalPadicValuation_lower_iff p _ _).mp
    (actual_outer_determinant_coeffLower p m N h hp hp7 hK hK2 hNp hKp k)).resolve_left hk

#print axioms actual_outer_determinant_bound
end Zeta5OuterDeterminant
