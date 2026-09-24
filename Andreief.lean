import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
open MeasureTheory Matrix Equiv

namespace Zeta5Andreief

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]
variable {h : ℕ} (f g : Fin h → Ω → ℝ)

def evaluationMatrix (f : Fin h → Ω → ℝ) (x : Fin h → Ω) : Matrix (Fin h) (Fin h) ℝ :=
  fun i j => f i (x j)

def momentMatrix : Matrix (Fin h) (Fin h) ℝ :=
  fun i j => ∫ x, f i x*g j x ∂μ

def permTerm (σ τ : Equiv.Perm (Fin h)) (x : Fin h → Ω) : ℝ :=
  ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i : Fin h, (f (σ i) (x i)*g (τ i) (x i))

lemma permTerm_integrable (hf : ∀ i j, Integrable (fun x => f i x*g j x) μ)
    (σ τ : Equiv.Perm (Fin h)) :
    Integrable (permTerm f g σ τ) (Measure.pi (fun _ : Fin h => μ)) := by
  exact (Integrable.fintype_prod (fun i => hf (σ i) (τ i))).const_mul _

lemma det_mul_product_eq_sum (τ : Equiv.Perm (Fin h)) (x : Fin h → Ω) :
    (evaluationMatrix f x).det * (∏ i : Fin h, g (τ i) (x i)) =
      ∑ σ : Equiv.Perm (Fin h), permTerm f g σ τ x := by
  rw [Matrix.det_apply', Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ hσ
  unfold permTerm evaluationMatrix
  rw [mul_assoc, Finset.prod_mul_distrib]

lemma det_mul_product_integrable
    (hf : ∀ i j, Integrable (fun x => f i x*g j x) μ)
    (τ : Equiv.Perm (Fin h)) :
    Integrable (fun x => (evaluationMatrix f x).det * ∏ i : Fin h, g (τ i) (x i))
      (Measure.pi (fun _ : Fin h => μ)) := by
  simp_rw [det_mul_product_eq_sum]
  exact integrable_finsetSum Finset.univ (fun σ _ => permTerm_integrable μ f g hf σ τ)

lemma integral_det_mul_product
    (hf : ∀ i j, Integrable (fun x => f i x*g j x) μ)
    (τ : Equiv.Perm (Fin h)) :
    (∫ x : Fin h → Ω, (evaluationMatrix f x).det * ∏ i : Fin h, g (τ i) (x i)
      ∂Measure.pi (fun _ : Fin h => μ)) =
      ((momentMatrix μ f g).submatrix id τ).det := by
  simp_rw [det_mul_product_eq_sum]
  rw [integral_finsetSum Finset.univ (fun σ _ => permTerm_integrable μ f g hf σ τ)]
  simp only [permTerm, integral_const_mul,
    Matrix.det_apply', Matrix.submatrix_apply, id_eq, momentMatrix]
  apply Finset.sum_congr rfl
  intro σ hσ
  congr 1
  exact integral_fintype_prod_eq_prod
    (μ := fun _ : Fin h => μ) (fun i (x : Ω) => f (σ i) x*g (τ i) x)

lemma determinant_product_integrable
    (hf : ∀ i j, Integrable (fun x => f i x*g j x) μ) :
    Integrable (fun x => (evaluationMatrix f x).det*(evaluationMatrix g x).det)
      (Measure.pi (fun _ : Fin h => μ)) := by
  have he (x : Fin h → Ω) : (evaluationMatrix f x).det*(evaluationMatrix g x).det =
      ∑ τ : Equiv.Perm (Fin h), ((Equiv.Perm.sign τ : ℤ) : ℝ) *
        ((evaluationMatrix f x).det * ∏ i : Fin h, g (τ i) (x i)) := by
    rw [Matrix.det_apply' (evaluationMatrix g x), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro τ hτ
    dsimp [evaluationMatrix]
    ring
  simp_rw [he]
  exact integrable_finsetSum Finset.univ (fun τ _ =>
    (det_mul_product_integrable μ f g hf τ).const_mul _)

/-- Andréief's identity on a general sigma-finite measure space. Pairwise
integrability is sufficient; integrability of the determinant product is proved. -/
theorem andreief (hf : ∀ i j, Integrable (fun x => f i x*g j x) μ) :
    (∫ x : Fin h → Ω, (evaluationMatrix f x).det*(evaluationMatrix g x).det
      ∂Measure.pi (fun _ : Fin h => μ)) =
      (Nat.factorial h : ℝ) * (momentMatrix μ f g).det := by
  have he (x : Fin h → Ω) : (evaluationMatrix f x).det*(evaluationMatrix g x).det =
      ∑ τ : Equiv.Perm (Fin h), ((Equiv.Perm.sign τ : ℤ) : ℝ) *
        ((evaluationMatrix f x).det * ∏ i : Fin h, g (τ i) (x i)) := by
    rw [Matrix.det_apply' (evaluationMatrix g x), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro τ hτ
    dsimp [evaluationMatrix]
    ring
  simp_rw [he]
  rw [integral_finsetSum Finset.univ (fun τ _ =>
    (det_mul_product_integrable μ f g hf τ).const_mul _)]
  simp_rw [integral_const_mul, integral_det_mul_product μ f g hf, Matrix.det_permute']
  have hsign (τ : Equiv.Perm (Fin h)) :
      ((Equiv.Perm.sign τ : ℤ) : ℝ) * ((Equiv.Perm.sign τ : ℤ) : ℝ) = 1 := by
    exact_mod_cast Int.units_coe_mul_self (Equiv.Perm.sign τ)
  simp_rw [← mul_assoc, hsign, one_mul]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul]

#print axioms andreief

end Zeta5Andreief
