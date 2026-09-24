import PoleIntegral
import ConstructionPartialFractions
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Analysis.Matrix.PosDef

noncomputable section
open scoped BigOperators
open MeasureTheory Set Polynomial Matrix

namespace Zeta5Construction

def zetaSeries : ℝ := ∑' n : ℕ, 1/(n : ℝ)^5

def rationalMomentIntegrand (N h e : ℕ) (y : ℝ) : ℝ :=
  (numerator N e).eval₂ (Rat.castHom ℝ) (y^2) /
    (tailDenominator N h).eval₂ (Rat.castHom ℝ) (y^2) * integralWeight y

lemma rationalMomentIntegrand_split (N h e : ℕ) (y : ℝ) :
    rationalMomentIntegrand N h e y =
      (numerator N e / tailDenominator N h).eval₂ (Rat.castHom ℝ) (y^2) * integralWeight y +
        ∑ k : Fin h, (residue N e k : ℝ) *
          (integralWeight y/(y^2+(poleIndex N k : ℝ)^2)) := by
  unfold rationalMomentIntegrand
  rw [construction_partial_fraction_at_square, add_mul, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  ring

lemma rationalMomentIntegrand_integrable (N h e : ℕ) :
    IntegrableOn (rationalMomentIntegrand N h e) (Ioi 0) := by
  have hq := polynomialWeight_integrable (numerator N e / tailDenominator N h)
  have hs : IntegrableOn (fun y : ℝ => ∑ k : Fin h, (residue N e k : ℝ) *
      (integralWeight y/(y^2+(poleIndex N k : ℝ)^2))) (Ioi 0) := by
    apply integrable_finsetSum
    intro k hk
    apply (poleWeight_integrable _).const_mul
    exact_mod_cast poleIndex_pos N k
  apply (hq.add hs).congr
  filter_upwards with y
  exact (rationalMomentIntegrand_split N h e y).symm

/-- The rational-functional value equals the actual rational integral,
with every polynomial quotient and simple-pole contribution retained. -/
theorem rationalMoment_integral (N h e : ℕ) :
    (∫ y : ℝ in Ioi 0, rationalMomentIntegrand N h e y) =
      (quotientMoment N h e : ℝ) + ∑ k : Fin h, (residue N e k : ℝ) *
        (poleFunctional (poleIndex N k)).eval₂ (Rat.castHom ℝ) zetaSeries := by
  have hq := polynomialWeight_integrable (numerator N e / tailDenominator N h)
  have hk (k : Fin h) : IntegrableOn (fun y : ℝ => (residue N e k : ℝ) *
      (integralWeight y/(y^2+(poleIndex N k : ℝ)^2))) (Ioi 0) := by
    apply (poleWeight_integrable _).const_mul
    exact_mod_cast poleIndex_pos N k
  have hs := integrable_finsetSum Finset.univ (fun k _ => hk k)
  simp_rw [rationalMomentIntegrand_split]
  have ha := integral_add hq hs
  rw [ha, integral_finsetSum Finset.univ (fun k _ => hk k)]
  rw [← polynomialFunctional_eq_integral]
  congr 1
  apply Finset.sum_congr rfl
  intro k hkmem
  rw [integral_const_mul, ← paper_poleFunctional_eq_integral _ (poleIndex_pos N k)]
  rfl

/-- Actual evaluation of the paper's affine Hankel matrix. -/
def realHankelMatrix (N h : ℕ) : Matrix (Fin h) (Fin h) ℝ :=
  fun i j => (hankelMatrix N h i j).eval₂ (Rat.castHom ℝ) zetaSeries

theorem realHankelMatrix_entry (N h : ℕ) (i j : Fin h) :
    realHankelMatrix N h i j =
      ∫ y : ℝ in Ioi 0, rationalMomentIntegrand N h (i.val+j.val) y := by
  rw [rationalMoment_integral]
  unfold realHankelMatrix
  rw [hankelMatrix_entry]
  simp only [eval₂_add, eval₂_C, eval₂_finset_sum, eval₂_mul]
  rfl

/-- Recover the original, uncancelled rational function in (2.4). -/
lemma rationalMomentIntegrand_eq (N h e : ℕ) (y : ℝ) :
    rationalMomentIntegrand N h e y =
      (realDenominator N).eval (y^2)^6 * (y^2)^e /
        (realDenominator (N+h)).eval (y^2) * integralWeight y := by
  have hd : (realDenominator (N+h)).eval (y^2) =
      (realDenominator N).eval (y^2) *
        (tailDenominator N h).eval₂ (Rat.castHom ℝ) (y^2) := by
    simp only [realDenominator, eval_map, denominator_split, eval₂_mul]
  have hp := realDenominator_eval_pos N y
  have ht : 0 < (tailDenominator N h).eval₂ (Rat.castHom ℝ) (y^2) := by
    have hk := realDenominator_eval_pos (N+h) y
    rw [hd] at hk
    exact pos_of_mul_pos_right hk hp.le
  unfold rationalMomentIntegrand numerator
  simp only [eval₂_mul, eval₂_pow, eval₂_X]
  rw [hd]
  rw [show (denominator N).eval₂ (Rat.castHom ℝ) (y^2) =
      (realDenominator N).eval (y^2) by rw [realDenominator, eval_map]]
  field_simp <;> ring

lemma ofFn_eval (h : ℕ) (v : Fin h → ℝ) (t : ℝ) :
    (Polynomial.ofFn h v).eval t = ∑ i : Fin h, v i * t^i.val := by
  rw [Polynomial.ofFn_eq_sum_monomial]
  simp only [eval_finsetSum, eval_monomial]

lemma ofFn_ne_zero (h : ℕ) {v : Fin h → ℝ} (hv : v ≠ 0) :
    Polynomial.ofFn h v ≠ 0 := by
  intro hz
  apply hv
  funext i
  have hc := congrArg (fun p : ℝ[X] => p.coeff i.val) hz
  change v i = 0
  simpa only [Polynomial.ofFn_coeff_eq_val_of_lt v i.isLt, coeff_zero] using hc

lemma quadraticIntegrand_eq_sum (N h : ℕ) (v : Fin h → ℝ) (y : ℝ) :
    quadraticIntegrand N (N+h) (Polynomial.ofFn h v) y =
      ∑ i : Fin h, ∑ j : Fin h, v i *
        rationalMomentIntegrand N h (i.val+j.val) y * v j := by
  simp_rw [rationalMomentIntegrand_eq]
  unfold quadraticIntegrand
  rw [ofFn_eval]
  simp only [pow_two]
  rw [Finset.sum_mul_sum]
  simp only [Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [pow_add]
  ring

/-- The actual matrix quadratic form is the strictly positive rational
integral from Proposition 2.2. -/
theorem realHankelMatrix_quadraticIntegral (N h : ℕ) (v : Fin h → ℝ) :
    (∫ y : ℝ in Ioi 0, quadraticIntegrand N (N+h) (Polynomial.ofFn h v) y) =
      ∑ i : Fin h, ∑ j : Fin h, v i * realHankelMatrix N h i j * v j := by
  simp_rw [quadraticIntegrand_eq_sum]
  have hij (i j : Fin h) : IntegrableOn (fun y : ℝ => v i *
      rationalMomentIntegrand N h (i.val+j.val) y * v j) (Ioi 0) :=
    ((rationalMomentIntegrand_integrable N h (i.val+j.val)).const_mul (v i)).mul_const (v j)
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hij i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum Finset.univ (fun j _ => hij i j)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_mul_const, integral_const_mul, realHankelMatrix_entry]

/-- The explicitly constructed matrix at ζ(5) is positive definite. -/
theorem realHankelMatrix_posDef (N h : ℕ) : (realHankelMatrix N h).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, realHankelMatrix_entry,
      Nat.add_comm]
  · intro v hv
    have hp := quadraticIntegral_pos N (N+h) (ofFn_ne_zero h hv)
    rw [realHankelMatrix_quadraticIntegral] at hp
    simpa only [dotProduct, mulVec, star_trivial, Finset.mul_sum, mul_assoc] using hp

/-- Unconditional determinant positivity, for the actual matrix. -/
theorem realHankelMatrix_det_pos (N h : ℕ) : 0 < (realHankelMatrix N h).det :=
  (realHankelMatrix_posDef N h).det_pos

/-- The polynomial determinant itself, evaluated at the actual fifth-power
zeta series, is strictly positive. -/
theorem determinant_eval_pos (N h : ℕ) :
    0 < (determinant N h).eval₂ (Rat.castHom ℝ) zetaSeries := by
  have he := (Polynomial.eval₂RingHom (Rat.castHom ℝ) zetaSeries).map_det
    (hankelMatrix N h)
  change (determinant N h).eval₂ (Rat.castHom ℝ) zetaSeries =
    (realHankelMatrix N h).det at he
  rw [he]
  exact realHankelMatrix_det_pos N h

/-- The normalization S_K from (2.5) also has a positive value. -/
theorem normalizedDeterminant_eval_pos (N h : ℕ) :
    0 < (normalizedDeterminant N h).eval₂ (Rat.castHom ℝ) zetaSeries := by
  rw [normalizedDeterminant, eval₂_mul, eval₂_C]
  apply mul_pos
  · change (0 : ℝ) < (normalizingScalar N h : ℝ)
    exact_mod_cast normalizingScalar_pos N h
  · exact determinant_eval_pos N h

#print axioms determinant_eval_pos

end Zeta5Construction
