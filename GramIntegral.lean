import Andreief
import MatrixIntegral

noncomputable section
open scoped BigOperators
open MeasureTheory Set Polynomial Matrix

namespace Zeta5Construction

def gramWeight (N h : ℕ) (y : ℝ) : ℝ :=
  (realDenominator N).eval (y^2)^6 / (realDenominator (N+h)).eval (y^2) * integralWeight y

def gramFunctions (h : ℕ) (i : Fin h) (y : ℝ) : ℝ := (y^2)^i.val

def weightedGramFunctions (N h : ℕ) (i : Fin h) (y : ℝ) : ℝ :=
  gramFunctions h i y * gramWeight N h y

lemma gramFunctions_pair_eq (N h : ℕ) (i j : Fin h) (y : ℝ) :
    gramFunctions h i y*weightedGramFunctions N h j y =
      rationalMomentIntegrand N h (i.val+j.val) y := by
  rw [rationalMomentIntegrand_eq]
  unfold weightedGramFunctions gramFunctions gramWeight
  rw [pow_add]
  ring

lemma gramFunctions_pair_integrable (N h : ℕ) (i j : Fin h) :
    IntegrableOn (fun y => gramFunctions h i y*weightedGramFunctions N h j y) (Ioi 0) := by
  simp_rw [gramFunctions_pair_eq]
  exact rationalMomentIntegrand_integrable N h _

lemma gramMomentMatrix_eq (N h : ℕ) :
    Zeta5Andreief.momentMatrix (volume.restrict (Ioi 0))
      (gramFunctions h) (weightedGramFunctions N h) = realHankelMatrix N h := by
  ext i j
  simp only [Zeta5Andreief.momentMatrix, gramFunctions_pair_eq, realHankelMatrix_entry]

lemma gramEvaluationMatrix_eq (h : ℕ) (y : Fin h → ℝ) :
    Zeta5Andreief.evaluationMatrix (gramFunctions h) y =
      (Matrix.vandermonde (fun i : Fin h => (y i)^2))ᵀ := by
  ext i j
  rfl

lemma weightedGramEvaluationMatrix_det (N h : ℕ) (y : Fin h → ℝ) :
    (Zeta5Andreief.evaluationMatrix (weightedGramFunctions N h) y).det =
      (∏ i : Fin h, gramWeight N h (y i)) *
        (Zeta5Andreief.evaluationMatrix (gramFunctions h) y).det := by
  have he : Zeta5Andreief.evaluationMatrix (weightedGramFunctions N h) y =
      Matrix.of (fun i j => gramWeight N h (y j) *
        Zeta5Andreief.evaluationMatrix (gramFunctions h) y i j) := by
    ext i j
    simp only [Zeta5Andreief.evaluationMatrix, weightedGramFunctions, Matrix.of_apply]
    ring
  rw [he, Matrix.det_mul_row]

/-- The squared Vandermonde factor in the source's multiple integral. -/
def vandermondeSquare (h : ℕ) (y : Fin h → ℝ) : ℝ :=
  ∏ i : Fin h, ∏ j ∈ Finset.Ioi i, ((y i)^2-(y j)^2)^2

lemma vandermonde_det_sq (h : ℕ) (y : Fin h → ℝ) :
    (Matrix.vandermonde (fun i : Fin h => (y i)^2)).det^2 = vandermondeSquare h y := by
  rw [Matrix.det_vandermonde]
  simp only [← Finset.prod_pow]
  unfold vandermondeSquare
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro j hj
  ring

def gramIntegrand (N h : ℕ) (y : Fin h → ℝ) : ℝ :=
  vandermondeSquare h y * ∏ i : Fin h, gramWeight N h (y i)

lemma gramDeterminantProduct_eq (N h : ℕ) (y : Fin h → ℝ) :
    (Zeta5Andreief.evaluationMatrix (gramFunctions h) y).det *
      (Zeta5Andreief.evaluationMatrix (weightedGramFunctions N h) y).det =
        gramIntegrand N h y := by
  rw [weightedGramEvaluationMatrix_det, gramEvaluationMatrix_eq, Matrix.det_transpose]
  unfold gramIntegrand
  rw [← vandermonde_det_sq]
  ring

/-- The multiple integral in (6.10) is absolutely integrable. -/
theorem gramIntegrand_integrable (N h : ℕ) :
    Integrable (gramIntegrand N h)
      (Measure.pi (fun _ : Fin h => volume.restrict (Ioi (0 : ℝ)))) := by
  have hh := Zeta5Andreief.determinant_product_integrable
    (volume.restrict (Ioi 0)) (gramFunctions h) (weightedGramFunctions N h)
    (gramFunctions_pair_integrable N h)
  apply hh.congr
  filter_upwards with y
  exact gramDeterminantProduct_eq N h y

/-- Andréief's identity specialized to the actual rational Hankel matrix. -/
theorem gramIntegral_eq_factorial_det (N h : ℕ) :
    (∫ y : Fin h → ℝ, gramIntegrand N h y
      ∂Measure.pi (fun _ : Fin h => volume.restrict (Ioi (0 : ℝ)))) =
        (Nat.factorial h : ℝ) * (realHankelMatrix N h).det := by
  have hh := Zeta5Andreief.andreief
    (volume.restrict (Ioi 0)) (gramFunctions h) (weightedGramFunctions N h)
    (gramFunctions_pair_integrable N h)
  simpa only [gramDeterminantProduct_eq, gramMomentMatrix_eq] using hh

/-- Equation (6.10), with the actual determinant polynomial on the left
and the complete positive Vandermonde integral on the right. -/
theorem determinant_eq_gramIntegral (N h : ℕ) :
    (determinant N h).eval₂ (Rat.castHom ℝ) zetaSeries =
      (1/(Nat.factorial h : ℝ)) *
        (∫ y : Fin h → ℝ, gramIntegrand N h y
          ∂Measure.pi (fun _ : Fin h => volume.restrict (Ioi (0 : ℝ)))) := by
  have he := (Polynomial.eval₂RingHom (Rat.castHom ℝ) zetaSeries).map_det
    (hankelMatrix N h)
  change (determinant N h).eval₂ (Rat.castHom ℝ) zetaSeries =
    (realHankelMatrix N h).det at he
  rw [he, gramIntegral_eq_factorial_det]
  have hf : (Nat.factorial h : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero h
  field_simp

#print axioms determinant_eq_gramIntegral

end Zeta5Construction
