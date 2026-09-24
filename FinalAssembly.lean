import NormalizationLog
import MatrixIntegral
import Zeta5Reduction

noncomputable section
open scoped BigOperators Topology
open Filter Polynomial
namespace Zeta5FinalAssembly
open Zeta5Parameters Zeta5Construction Zeta5Reduction

lemma source_zeta_eq : Zeta5Reduction.zeta5=Zeta5Construction.zetaSeries := zeta5_eq_series

lemma paperPolynomial_eval_pos (n M : ℕ) :
    0<(paperPolynomial n M).eval₂ (Rat.castHom ℝ) Zeta5Construction.zetaSeries := by
  rw [paperPolynomial, eval₂_mul, eval₂_C]
  exact mul_pos (by change (0:ℝ)<(normalizer n M:ℝ); exact_mod_cast normalizer_pos n M)
    (normalizedDeterminant_eval_pos (N n) (Zeta5Parameters.h n))

lemma log_paperPolynomial (n M : ℕ) :
    Real.log ((paperPolynomial n M).eval₂ (Rat.castHom ℝ) Zeta5Construction.zetaSeries) =
      Real.log (normalizer n M:ℝ) + Real.log
        ((normalizedDeterminant (N n) (Zeta5Parameters.h n)).eval₂ (Rat.castHom ℝ)
          Zeta5Construction.zetaSeries) := by
  rw [paperPolynomial, eval₂_mul, eval₂_C, Real.log_mul
    (by change (normalizer n M:ℝ)≠0; exact_mod_cast ne_of_gt (normalizer_pos n M))
    (ne_of_gt (normalizedDeterminant_eval_pos (N n) (Zeta5Parameters.h n)))]
  rfl

/-- Lift actual rational polynomials with integer coefficients, then apply
the independently checked degree-versus-decay irrationality criterion. -/
theorem irrational_of_eventual_integer_rational_polynomials
    (ξ : ℝ) (C : ℕ) (c : ℝ) (hc : 0<c) (F : ℕ→ℚ[X])
    (hF : ∀ᶠ n : ℕ in atTop,
      (∃ Q : ℤ[X], Q.map (Int.castRingHom ℚ)=F n) ∧
      (F n).natDegree≤C*n ∧ 0<(F n).eval₂ (Rat.castHom ℝ) ξ ∧
      (F n).eval₂ (Rat.castHom ℝ) ξ<Real.exp (-c*(n:ℝ)^2)) : Irrational ξ := by
  classical
  let Q : ℕ→ℤ[X] := fun n => if h : ∃P : ℤ[X], P.map (Int.castRingHom ℚ)=F n
    then Classical.choose h else 0
  obtain ⟨n₀,hn₀⟩ := Filter.eventually_atTop.mp hF
  apply irrational_of_small_polynomial_family (Q:=Q) hc
  refine ⟨n₀,fun n hn => ?_⟩
  obtain ⟨hi,hd,hpos,hsmall⟩ := hn₀ n hn
  have hm : (Q n).map (Int.castRingHom ℚ)=F n := by
    dsimp [Q]
    rw [dif_pos hi]
    exact Classical.choose_spec hi
  have hdeg : (Q n).natDegree=(F n).natDegree := by
    rw [←hm, natDegree_map_eq_of_injective (Int.cast_injective (α:=ℚ))]
  have heval : eval ξ ((Q n).map (Int.castRingHom ℝ))=(F n).eval₂ (Rat.castHom ℝ) ξ := by
    rw [←hm, eval_map, eval₂_map]
    rfl
  exact ⟨hdeg.le.trans hd, heval.symm ▸ hpos, heval.symm ▸ hsmall⟩

/-- The last assembly step for the actual paper polynomial family. -/
theorem irrational_of_paperPolynomial_integer_log_decay (M : ℕ)
    (hinteger : ∀ᶠ n : ℕ in atTop, ∃ Q : ℤ[X], Q.map (Int.castRingHom ℚ)=paperPolynomial n M)
    (hdecay : ∀ᶠ n : ℕ in atTop,
      Real.log ((paperPolynomial n M).eval₂ (Rat.castHom ℝ) Zeta5Construction.zetaSeries)<
        -10*(n:ℝ)^2) : Irrational Zeta5Reduction.zeta5 := by
  rw [source_zeta_eq]
  apply irrational_of_eventual_integer_rational_polynomials _ 37 10 (by norm_num) (fun n => paperPolynomial n M)
  filter_upwards [hinteger,hdecay] with n hi hd
  refine ⟨hi, (paperPolynomial_degree n M).le, paperPolynomial_eval_pos n M, ?_⟩
  rw [←Real.exp_log (paperPolynomial_eval_pos n M)]
  exact Real.exp_lt_exp.mpr hd

lemma paperPolynomial_log_decay_of_bounds (M : ℕ) (A B : ℝ)
    (hAB : 1600*(A+B) < -10)
    (hm : ∀ᶠ n : ℕ in atTop, Real.log (normalizer n M:ℝ)≤A*(40*(n:ℝ))^2)
    (hF : ∀ᶠ n : ℕ in atTop,
      Real.log ((normalizedDeterminant (N n) (Zeta5Parameters.h n)).eval₂
        (Rat.castHom ℝ) Zeta5Construction.zetaSeries)≤B*(40*(n:ℝ))^2) :
    ∀ᶠ n : ℕ in atTop,
      Real.log ((paperPolynomial n M).eval₂ (Rat.castHom ℝ) Zeta5Construction.zetaSeries)<
        -10*(n:ℝ)^2 := by
  filter_upwards [hm,hF,Filter.eventually_ge_atTop 1] with n hmn hFn hn
  rw [log_paperPolynomial]
  have hnR : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hh := mul_lt_mul_of_pos_right hAB (sq_pos_of_pos hnR)
  nlinarith

#print axioms paperPolynomial_log_decay_of_bounds
#print axioms irrational_of_paperPolynomial_integer_log_decay
end Zeta5FinalAssembly
