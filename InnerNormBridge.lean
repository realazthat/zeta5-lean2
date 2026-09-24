import InnerDeterminant
import Mathlib.NumberTheory.Padics.PadicNumbers

noncomputable section
open scoped BigOperators
namespace Zeta5InnerNormBridge
open Polynomial Zeta5Outer Zeta5InnerDeterminant

lemma rational_valuation_of_cast_norm (p : ℕ) [Fact p.Prime] (q : ℚ) (e : ℤ)
    (hn : ‖(q:ℚ_[p])‖≤(p:ℝ)^(-e)) :
    ((e:ℚ):WithTop ℚ)≤rationalPadicValuation p q := by
  apply (rationalPadicValuation_lower_iff p q (e:ℚ)).mpr
  by_cases hq : q=0
  · exact Or.inl hq
  · right
    have hq' : (q:ℚ_[p])≠0 := by exact_mod_cast hq
    rw [Padic.norm_eq_zpow_neg_valuation hq', Padic.valuation_ratCast] at hn
    have hp : (1:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    have he : e≤padicValRat p q := by
      have h := (zpow_le_zpow_iff_right₀ hp).mp hn
      omega
    exact_mod_cast he

lemma coeffLower_of_cast_norm (p : ℕ) [Fact p.Prime] (P : ℚ[X]) (e : ℤ)
    (hn : ∀k, ‖(P.coeff k:ℚ_[p])‖≤(p:ℝ)^(-e)) :
    CoeffLower (rationalPadicValuation p) P e := fun k => rational_valuation_of_cast_norm p _ e (hn k)

lemma affine_coeff_norm (p : ℕ) [Fact p.Prime] (P : ℚ[X]) (B : ℝ)
    (hB : 0≤B) (hd : P.natDegree≤1)
    (h0 : ‖((P.eval (0:ℚ):ℚ):ℚ_[p])‖≤B) (h1 : ‖((P.eval (1:ℚ):ℚ):ℚ_[p])‖≤B) :
    ∀k, ‖(P.coeff k:ℚ_[p])‖≤B := by
  have hcoeff : P.coeff 1=P.eval 1-P.eval 0 := by
    have he := P.as_sum_range_C_mul_X_pow' (show P.natDegree<2 by omega)
    have hev := congrArg (fun Q : ℚ[X] => Q.eval 1-Q.eval 0) he
    simpa [Finset.sum_range_succ] using hev.symm
  intro k
  rcases k with _|k
  · simpa [coeff_zero_eq_eval_zero] using h0
  · cases k with
    | zero =>
      rw [hcoeff, Rat.cast_sub]
      exact (Zeta5Local.local_norm_sub_le_max _ _).trans (max_le h1 h0)
    | succ k =>
      rw [coeff_eq_zero_of_natDegree_lt (by omega)]
      simpa using hB

lemma affine_coeffLower_of_eval01 (p : ℕ) [Fact p.Prime] (P : ℚ[X]) (e : ℤ)
    (hd : P.natDegree≤1)
    (h0 : ‖((P.eval (0:ℚ):ℚ):ℚ_[p])‖≤(p:ℝ)^(-e))
    (h1 : ‖((P.eval (1:ℚ):ℚ):ℚ_[p])‖≤(p:ℝ)^(-e)) :
    CoeffLower (rationalPadicValuation p) P e :=
  coeffLower_of_cast_norm p P e (affine_coeff_norm p P _ (by positivity) hd h0 h1)

#print axioms affine_coeffLower_of_eval01
end Zeta5InnerNormBridge
