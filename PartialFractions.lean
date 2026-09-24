import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic

/-!
# Exact finite partial fractions

These identities are valid over an arbitrary field. Consequently they can be
used directly over ℚ, ℝ, or ℚ_p, and retain the polynomial quotient rather
than assuming that the rational function is proper.
-/
namespace Zeta5Local
open Polynomial Finset

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]

/-- The remainder on division by the nodal polynomial is exactly the
interpolant of the original numerator values at those nodes. -/
theorem remainder_eq_interpolate (P : Polynomial F) (s : Finset ι) (v : ι → F)
    (hv : Set.InjOn v s) :
    P %ₘ Lagrange.nodal s v = Lagrange.interpolate s v (fun i => P.eval (v i)) := by
  apply Lagrange.eq_interpolate_of_eval_eq (fun i => P.eval (v i)) hv
  · simpa only [Lagrange.degree_nodal] using
      Polynomial.degree_modByMonic_lt P (Lagrange.nodal_monic (s := s) (v := v))
  · intro i hi
    have h := congrArg (Polynomial.eval (v i))
      (Polynomial.modByMonic_add_div P (Lagrange.nodal s v))
    simpa only [Polynomial.eval_add, Polynomial.eval_mul,
      Lagrange.eval_nodal_at_node hi, zero_mul, add_zero] using h

/-- Full rational-function partial fractions, including the polynomial
quotient. The poles are distinct, and evaluation avoids them. -/
theorem partial_fraction_eval (P : Polynomial F) (s : Finset ι) (v : ι → F)
    (hv : Set.InjOn v s) (x : F) (hx : ∀ i ∈ s, x ≠ v i) :
    P.eval x / (Lagrange.nodal s v).eval x =
      (P / Lagrange.nodal s v).eval x +
        ∑ i ∈ s, (P.eval (v i) / ∏ j ∈ s.erase i, (v i - v j)) / (x - v i) := by
  have hden : (Lagrange.nodal s v).eval x ≠ 0 := Lagrange.eval_nodal_not_at_node hx
  have h := congrArg (Polynomial.eval x)
    (Polynomial.modByMonic_add_div P (Lagrange.nodal s v))
  rw [Polynomial.eval_add, Polynomial.eval_mul, remainder_eq_interpolate P s v hv,
    Lagrange.eval_interpolate_not_at_node _ hx,
    Polynomial.divByMonic_eq_div P (Lagrange.nodal_monic (s := s) (v := v))] at h
  have hsum : (∑ i ∈ s, Lagrange.nodalWeight s v i * (x - v i)⁻¹ * P.eval (v i)) =
      ∑ i ∈ s, (P.eval (v i) / ∏ j ∈ s.erase i, (v i - v j)) / (x - v i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Lagrange.nodalWeight, Finset.prod_inv_distrib]
    ring
  rw [hsum] at h
  apply (div_eq_iff hden).mpr
  linear_combination -h

/-- The same identity after any field embedding, for example evaluating a
rational-coefficient construction at a real integration variable. -/
theorem partial_fraction_eval₂ {E : Type*} [Field E] (f : F →+* E)
    (P : Polynomial F) (s : Finset ι) (v : ι → F)
    (hv : Set.InjOn v s) (x : E) (hx : ∀ i ∈ s, x ≠ f (v i)) :
    P.eval₂ f x / (Lagrange.nodal s v).eval₂ f x =
      (P / Lagrange.nodal s v).eval₂ f x +
        ∑ i ∈ s, f (P.eval (v i) / ∏ j ∈ s.erase i, (v i - v j)) / (x - f (v i)) := by
  have hv' : Set.InjOn (fun i => f (v i)) s := by
    intro i hi j hj h
    exact hv hi hj (f.injective h)
  have h := partial_fraction_eval (P.map f) s (fun i => f (v i)) hv' x hx
  have hT : (Lagrange.nodal s v).map f = Lagrange.nodal s (fun i => f (v i)) := by
    simp only [Lagrange.nodal, Polynomial.map_prod, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C]
  rw [← hT, ← Polynomial.map_div f] at h
  simpa only [Polynomial.eval_map_apply, Polynomial.eval_map,
    map_div₀, map_prod, map_sub, Polynomial.eval₂_at_apply] using h

#print axioms partial_fraction_eval
#print axioms partial_fraction_eval₂
end Zeta5Local
