import InnerNormBridge
import ActualRationalDistribution

noncomputable section
open scoped BigOperators
namespace Zeta5InnerDistributionBound
open Polynomial Zeta5Construction Zeta5NumeratorFunctional Zeta5Local
open Zeta5InnerNormBridge Zeta5Outer
variable {p : ℕ} [Fact p.Prime]

noncomputable def diskValue (N h : ℕ) (A : ℚ[X]) (x : ℚ_[p]) (a : ℕ) : ℚ_[p] :=
  (rationalTauFunctional ((actualPullbackPolynomial N h A).comp
    (C (a:ℚ)+C (p:ℚ)*X)):ℚ_[p]) +
  ∑ i : Fin h, ((actualPullbackResidue N A i:ℚ_[p])/(p:ℚ_[p])) *
    (residuePoleValue ((p:ℚ_[p])^5*x+distributionConstant p) ((poleIndex N i:ℤ)-a) +
      residuePoleValue ((p:ℚ_[p])^5*x+distributionConstant p) (-(poleIndex N i:ℤ)-a))

lemma numeratorFunctional_affine_degree (N h : ℕ) (A : ℚ[X]) :
    (numeratorFunctional N h polynomialFunctional A).natDegree≤1 := by
  rw [numeratorFunctional_apply]
  apply (natDegree_add_le _ _).trans
  apply max_le
  · simp
  · apply natDegree_sum_le_of_forall_le
    intro i hi
    apply (natDegree_C_mul_le _ _).trans
    rw [poleFunctional_affine]
    apply (natDegree_add_le _ _).trans
    apply max_le
    · exact (natDegree_mul_C_le _ _).trans natDegree_X_le
    · simp

lemma functional_norm_of_disks (hp7 : 7≤p) (N h : ℕ) (A : ℚ[X]) (x : ℚ_[p]) (e : ℤ)
    (hdisk : ∀ a∈Finset.range p, ‖diskValue N h A x a‖≤(p:ℝ)^(-(e+4))) :
    ‖(numeratorFunctional N h polynomialFunctional A).eval₂ (Rat.castHom ℚ_[p]) x‖≤
      (p:ℝ)^(-e) := by
  rw [numeratorFunctional_padic_distribution hp7]
  change ‖(p:ℚ_[p])⁻¹^4*∑ a∈Finset.range p, diskValue N h A x a‖≤_
  have hsum : ‖∑ a∈Finset.range p, diskValue N h A x a‖≤(p:ℝ)^(-(e+4)) :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) hdisk
  rw [norm_mul, norm_pow, norm_inv, Padic.norm_p, inv_inv]
  calc
    _ ≤ (p:ℝ)^4*(p:ℝ)^(-(e+4)) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by
      rw [←zpow_natCast, ←zpow_add₀ (by exact_mod_cast (Fact.out:p.Prime).ne_zero)]
      congr 1
      omega

lemma functional_coeffLower_of_disks (hp7 : 7≤p) (N h : ℕ) (A : ℚ[X]) (e : ℤ)
    (hdisk : ∀x : ℚ, x=0 ∨ x=1 → ∀a∈Finset.range p,
      ‖diskValue N h A (x:ℚ_[p]) a‖≤(p:ℝ)^(-(e+4))) :
    CoeffLower (rationalPadicValuation p) (numeratorFunctional N h polynomialFunctional A) e := by
  apply affine_coeffLower_of_eval01 p _ e (numeratorFunctional_affine_degree N h A)
  · have hh := functional_norm_of_disks hp7 N h A (0:ℚ_[p]) e (by simpa using hdisk 0 (Or.inl rfl))
    simpa only [←Rat.coe_castHom, ←Polynomial.eval₂_at_apply, map_zero] using hh
  · have hh := functional_norm_of_disks hp7 N h A (1:ℚ_[p]) e (by simpa using hdisk 1 (Or.inr rfl))
    simpa only [←Rat.coe_castHom, ←Polynomial.eval₂_at_apply, map_one] using hh

#print axioms functional_coeffLower_of_disks
end Zeta5InnerDistributionBound
