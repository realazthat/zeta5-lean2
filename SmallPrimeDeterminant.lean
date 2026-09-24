import SmallPrimeBasis
import BasisTransfer
import NumeratorFunctional

noncomputable section
open scoped BigOperators
open Polynomial Matrix
namespace Zeta5SmallPrimeDeterminant
open Zeta5Local Zeta5Construction Zeta5NumeratorFunctional Zeta5BasisTransfer

def qBasisMatrix (h : ℕ) : Matrix (Fin h) (Fin h) ℚ :=
  fun i j => (smallPrimeQ i.val).coeff j.val

def qFunctional (N h : ℕ) : ℚ[X] →ₗ[ℚ] ℚ[X] :=
  (numeratorFunctional N h polynomialFunctional).comp
    (LinearMap.mulLeft ℚ (denominator N^5))

def entryScalar (N h : ℕ) : ℚ := ((N+h).factorial:ℚ)^2/(N.factorial:ℚ)^12

def smallPrimeMatrix (N h : ℕ) : Matrix (Fin h) (Fin h) ℚ[X] :=
  C (entryScalar N h) • gram (qFunctional N h) (fun i => smallPrimeQ i.val)

lemma qBasisMatrix_rows (h : ℕ) :
    basisRows (qBasisMatrix h) (fun i : Fin h => X^i.val) =
      fun i => smallPrimeQ i.val := by
  funext i
  have hd : (smallPrimeQ i.val).natDegree<h := by rw [smallPrimeQ_natDegree]; exact i.isLt
  have hs := (smallPrimeQ i.val).as_sum_range_C_mul_X_pow' hd
  rw [← Fin.sum_univ_eq_sum_range (fun k => C ((smallPrimeQ i.val).coeff k)*X^k) h] at hs
  simpa only [basisRows,qBasisMatrix,smul_eq_C_mul] using hs.symm

lemma qGram_congruence (N h : ℕ) :
    gram (qFunctional N h) (fun i : Fin h => smallPrimeQ i.val) =
      congruence (hankelMatrix N h) (qBasisMatrix h) := by
  rw [← qBasisMatrix_rows, gram_basisRows]
  congr 1
  apply Matrix.ext
  intro i j
  simp only [gram,qFunctional,LinearMap.comp_apply,LinearMap.mulLeft_apply]
  exact (hankelMatrix_as_functional N h i j).symm

lemma qBasisMatrix_det (h : ℕ) :
    (qBasisMatrix h).det = ∏i : Fin h, (smallPrimeQ i.val).leadingCoeff := by
  rw [← Matrix.det_transpose]
  change (Matrix.of (fun i j : Fin h => (smallPrimeQ j.val).coeff i.val)).det = _
  rw [Matrix.det_of_upperTriangular
    (Matrix.matrixOfPolynomials_blockTriangular (fun i : Fin h => smallPrimeQ i.val)
      (fun i => (smallPrimeQ_natDegree i.val).le))]
  apply Finset.prod_congr rfl
  intro i _
  change (smallPrimeQ i.val).coeff i.val = _
  simpa only [smallPrimeQ_natDegree] using (coeff_natDegree (p := smallPrimeQ i.val))

lemma smallPrimeQ_leadingCoeff_sq (n : ℕ) :
    (smallPrimeQ (n+1)).leadingCoeff^2 = 4/((2*(n+1)).factorial:ℚ)^2 := by
  rw [smallPrimeQ_leadingCoeff, div_pow, mul_pow]
  have h : ((-1:ℚ)^(n+1))^2=1 := by rw [←pow_mul,mul_comm _ 2,pow_mul]; norm_num
  rw [h]
  norm_num

lemma qBasisMatrix_det_sq (h : ℕ) (hh : 0<h) :
    (qBasisMatrix h).det^2 = 4^(h-1)/
      ∏i∈Finset.range (h-1), ((2*(i+1)).factorial:ℚ)^2 := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hh)
  rw [qBasisMatrix_det, ←Finset.prod_pow, Fin.prod_univ_succ]
  simp only [Fin.val_zero,smallPrimeQ_leadingCoeff_zero,one_pow,one_mul,Fin.val_succ,
    smallPrimeQ_leadingCoeff_sq,Nat.succ_sub_one]
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  congr 1
  exact Fin.prod_univ_eq_prod_range (fun i => ((2*(i+1)).factorial:ℚ)^2) r

lemma entryScalar_normalization (N h : ℕ) (hh : 0<h) :
    entryScalar N h^h*(qBasisMatrix h).det^2 = normalizingScalar N h := by
  rw [qBasisMatrix_det_sq h hh]
  simp only [entryScalar,normalizingScalar,div_pow,pow_mul]
  ring

/-- The triangular binomial basis gives the paper's exact normalization (3.11). -/
theorem smallPrimeMatrix_det (N h : ℕ) (hh : 0<h) :
    (smallPrimeMatrix N h).det = normalizedDeterminant N h := by
  rw [smallPrimeMatrix,Matrix.det_smul,qGram_congruence,congruence_det]
  simp only [Fintype.card_fin, ←map_pow, ←mul_assoc, ←map_mul,
    entryScalar_normalization N h hh,normalizedDeterminant,determinant]

#print axioms smallPrimeMatrix_det
end Zeta5SmallPrimeDeterminant
