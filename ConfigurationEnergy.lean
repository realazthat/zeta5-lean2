import ArcsineMixture
import EnergyComparison
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite

namespace Zeta5ConfigurationEnergy
open MeasureTheory Real Metric Set
open Zeta5CirclePotential Zeta5CircleMeasures Zeta5EnergyMixtures
open Zeta5ArcsineMixture

noncomputable def sigma {h : ℕ} (t : Fin h → ℝ) (K R : ℝ) : Measure ℂ :=
  weightedMeasure (fun _ : Fin h => 1/K) (fun i => circleMeasure (t i : ℂ) R)

instance sigma_finite {h : ℕ} (t : Fin h → ℝ) (K R : ℝ) : IsFiniteMeasure (sigma t K R) := by
  unfold sigma
  infer_instance

 theorem sigma_nullSingleton {h : ℕ} (t : Fin h → ℝ) (K : ℝ) {R : ℝ} (hR : 0 < R) :
    NullSingletonClass (sigma t K R) :=
  weightedMeasure_nullSingleton _ _ (fun i => circleMeasure_nullSingleton _ (ne_of_gt hR))

 theorem sigma_mass {h : ℕ} (t : Fin h → ℝ) {K : ℝ} (hK : 0 < K) (R : ℝ) :
    (sigma t K R).real univ = (h : ℝ)/K := by
  rw [sigma,weightedMeasure_mass _ (fun _ => by positivity)]
  simp [div_eq_mul_inv]

 theorem sigma_self_log_integrable {h : ℕ} (t : Fin h → ℝ) (K : ℝ) {R : ℝ} (hR : 0 < R) :
    Integrable logKernel ((sigma t K R).prod (sigma t K R)) :=
  log_integrable_weighted_product _ _ _ _ (fun i j =>
    circle_circle_log_integrable (t j : ℂ) (t i : ℂ) hR R)

 theorem sigma_rho_log_integrable {h : ℕ} (t : Fin h → ℝ) (K : ℝ) {R : ℝ} (hR : 0 < R) :
    Integrable logKernel ((sigma t K R).prod rho) :=
  log_integrable_weighted_left _ _ _ (fun i =>
    log_integrable_swap _ _ (rho_circle_log_integrable (t i) hR))

 theorem sigma_add_rho_log_integrable {h : ℕ} (t : Fin h → ℝ) (K : ℝ) {R : ℝ} (hR : 0 < R) :
    Integrable logKernel (((sigma t K R)+rho).prod ((sigma t K R)+rho)) := by
  rw [Measure.add_prod,Measure.prod_add,Measure.prod_add,
    integrable_add_measure,integrable_add_measure,integrable_add_measure]
  exact ⟨⟨sigma_self_log_integrable t K hR,sigma_rho_log_integrable t K hR⟩,
    ⟨log_integrable_swap _ _ (sigma_rho_log_integrable t K hR),rho_log_integrable⟩⟩

 theorem sigma_rho_energy {h : ℕ} (t : Fin h → ℝ) {K : ℝ} (hK : 0 < K)
    {R : ℝ} (hR : 0 < R) :
    mutualEnergy (sigma t K R) rho = (1/K)*∑ i, truncatedPotential R (t i) := by
  rw [sigma,energy_weighted_left _ (fun _ => by positivity) _ _
    (fun i => log_integrable_swap _ _ (rho_circle_log_integrable (t i) hR))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [← mutualEnergy_symm _ _ (rho_circle_log_integrable (t i) hR),rho_circle_energy (t i) hR]

 theorem circle_self_energy' (c : ℂ) {R : ℝ} (hR : 0 < R) :
    mutualEnergy (circleMeasure c R) (circleMeasure c R) = Real.log R := by
  unfold mutualEnergy logKernel
  rw [integral_prod _ (circle_circle_log_integrable c c hR R)]
  change (∫ w : ℂ, ∫ z : ℂ, Real.log ‖w-z‖ ∂circleMeasure c R ∂circleMeasure c R) = _
  simpa only [norm_sub_rev] using circle_measure_self_energy c hR

 theorem circle_mutual_energy' (c d : ℂ) {R : ℝ} (hR : 0 < R) (hcd : c ≠ d) :
    Real.log ‖c-d‖ ≤ mutualEnergy (circleMeasure c R) (circleMeasure d R) := by
  unfold mutualEnergy logKernel
  rw [integral_prod _ (circle_circle_log_integrable d c hR R)]
  change _ ≤ ∫ w : ℂ, ∫ z : ℂ, Real.log ‖w-z‖ ∂circleMeasure d R ∂circleMeasure c R
  simpa only [norm_sub_rev] using circle_measure_mutual_energy d c hR (Ne.symm hcd)

noncomputable def doubleLogSum {h : ℕ} (t : Fin h → ℝ) : ℝ :=
  ∑ i, ∑ j, Real.log |t i-t j|

 theorem sigma_energy_lower {h : ℕ} (t : Fin h → ℝ) (ht : Function.Injective t)
    {K : ℝ} (hK : 0 < K) {R : ℝ} (hR : 0 < R) :
    doubleLogSum t+(h : ℝ)*Real.log R ≤ K^2*mutualEnergy (sigma t K R) (sigma t K R) := by
  have he : mutualEnergy (sigma t K R) (sigma t K R) =
      (1/K)^2*∑ i, ∑ j, mutualEnergy (circleMeasure (t i : ℂ) R) (circleMeasure (t j : ℂ) R) := by
    rw [sigma,energy_weighted_product _ _ (fun _ => by positivity) (fun _ => by positivity)
      _ _ (fun i j => circle_circle_log_integrable (t j : ℂ) (t i : ℂ) hR R)]
    simp only [pow_two,Finset.mul_sum]
  rw [he]
  have hcancel : K^2*((1/K)^2)=1 := by field_simp
  rw [← mul_assoc,hcancel,one_mul]
  calc
    _ = ∑ i, ∑ j, (Real.log |t i-t j|+if i=j then Real.log R else 0) := by
      simp [Finset.sum_add_distrib,doubleLogSum]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases hij : i=j
      · subst j
        simp [circle_self_energy' _ hR]
      · rw [if_neg hij,add_zero]
        have hne : (t i : ℂ) ≠ (t j : ℂ) := by
          intro heq
          exact hij (ht (Complex.ofReal_injective heq))
        simpa only [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using
          circle_mutual_energy' (t i : ℂ) (t j : ℂ) hR hne

 theorem sigma_rho_comparison {h : ℕ} (t : Fin h → ℝ) {K : ℝ} (hK : 0 < K)
    (hmass : (h : ℝ)/K = 37/40) {R : ℝ} (hR : 0 < R) :
    mutualEnergy (sigma t K R) (sigma t K R)+mutualEnergy rho rho ≤
      2*mutualEnergy (sigma t K R) rho := by
  haveI := sigma_nullSingleton t K hR
  apply Zeta5RealEnergy.complex_measure_energy_comparison
  · apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    change (sigma t K R).real univ = rho.real univ
    rw [sigma_mass t hK R,rho_mass]
    exact hmass
  · exact sigma_add_rho_log_integrable t K hR

/-- The discrete logarithmic-energy bound, obtained from actual nonatomic
circle and arcsine measures and the proved zero-mass comparison theorem. -/
 theorem configuration_energy_bound {h : ℕ} (t : Fin h → ℝ)
    (ht : Function.Injective t) (ht0 : ∀ i, 0 < t i)
    {K : ℝ} (hK : 0 < K) (hmass : (h : ℝ)/K = 37/40)
    {R : ℝ} (hR : 0 < R) (η M : ℝ) (V : ℝ → ℝ)
    (htrunc : ∀ x : ℝ, 0 ≤ x → truncatedPotential R x ≤ potential x+η)
    (hfield : ∀ x : ℝ, 0 < x → 2*potential x-V x ≤ M) :
    doubleLogSum t-K*∑ i, V (t i) ≤
      ((37/40 : ℝ)*M-mutualEnergy rho rho+2*(37/40 : ℝ)*η)*K^2-(h : ℝ)*Real.log R := by
  have hlo := sigma_energy_lower t ht hK hR
  have hcomp := mul_le_mul_of_nonneg_left (sigma_rho_comparison t hK hmass hR) (sq_nonneg K)
  have hx : K^2*(2*mutualEnergy (sigma t K R) rho) =
      2*K*∑ i, truncatedPotential R (t i) := by
    rw [sigma_rho_energy t hK hR]
    field_simp
  rw [mul_add,hx] at hcomp
  have hs : 2*(∑ i, truncatedPotential R (t i))-(∑ i, V (t i)) ≤
      (h : ℝ)*(M+2*η) := by
    have hsum : (∑ i, (2*truncatedPotential R (t i)-V (t i))) ≤
        ∑ _i : Fin h, (M+2*η) := by
      apply Finset.sum_le_sum
      intro i _
      have hu := htrunc (t i) (ht0 i).le
      have hv := hfield (t i) (ht0 i)
      linarith
    simpa only [Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hsum
  have hsK := mul_le_mul_of_nonneg_left hs hK.le
  have hcard : (h : ℝ) = (37/40 : ℝ)*K := (div_eq_iff (ne_of_gt hK)).1 hmass
  calc
    _ ≤ K*((h : ℝ)*(M+2*η))-K^2*mutualEnergy rho rho-(h : ℝ)*Real.log R := by
      nlinarith
    _ = _ := by rw [hcard]; ring

 theorem doubleLogSum_eq_pair_sum {h : ℕ} (t : Fin h → ℝ) :
    doubleLogSum t = 2*∑ i, ∑ j ∈ Finset.Ioi i, Real.log |t i-t j| := by
  let f : Fin h → Fin h → ℝ := fun i j => Real.log |t i-t j|
  have hsymm (i j : Fin h) : f j i = f i j := by
    exact congrArg Real.log (abs_sub_comm _ _)
  have hpair (i j : Fin h) : f j i+f i j = 2*f i j := by rw [hsymm]; ring
  have hdiag (i : Fin h) : f i i = 0 := by simp [f]
  have hcompl (i : Fin h) : (∑ j ∈ ({i} : Finset (Fin h))ᶜ, f j i) = ∑ j, f j i := by
    have hc := Finset.sum_add_sum_compl ({i} : Finset (Fin h)) (fun j => f j i)
    simpa only [Finset.sum_singleton,hdiag,zero_add] using hc
  have hh := Finset.sum_sum_Ioi_add_eq_sum_sum_off_diag f
  simp_rw [hpair,← Finset.mul_sum,hcompl] at hh
  unfold doubleLogSum
  change (∑ i, ∑ j, f i j) = 2*∑ i, ∑ j ∈ Finset.Ioi i, f i j
  rw [hh]
  exact Finset.sum_comm

 theorem configuration_energy_bound_with_tail {h : ℕ} (t : Fin h → ℝ)
    (ht : Function.Injective t) (ht0 : ∀ i, 0 < t i)
    {K : ℝ} (hK : 0 < K) (hmass : (h : ℝ)/K = 37/40)
    {R : ℝ} (hR : 0 < R) (η M : ℝ) (V : ℝ → ℝ)
    (htrunc : ∀ x : ℝ, 0 ≤ x → truncatedPotential R x ≤ potential x+η)
    (hfield : ∀ x : ℝ, 0 < x → 2*potential x-V x+Real.sqrt x/K ≤ M) :
    2*(∑ i, ∑ j ∈ Finset.Ioi i, Real.log |t i-t j|)-K*(∑ i, V (t i))+
      (∑ i, Real.sqrt (t i)) ≤
      ((37/40 : ℝ)*M-mutualEnergy rho rho+2*(37/40 : ℝ)*η)*K^2-(h : ℝ)*Real.log R := by
  have hb := configuration_energy_bound t ht ht0 hK hmass hR η M
    (fun x => V x-Real.sqrt x/K) htrunc (by
      intro x hx
      have hv := hfield x hx
      linarith)
  have he : K*(∑ i, (V (t i)-Real.sqrt (t i)/K)) =
      K*(∑ i, V (t i))-(∑ i, Real.sqrt (t i)) := by
    rw [Finset.sum_sub_distrib,← Finset.sum_div,mul_sub]
    congr 1
    field_simp
  rw [he,doubleLogSum_eq_pair_sum] at hb
  linarith

open Filter in
/-- The regularization hypotheses disappear eventually, with radius `1/(K+1)`.
The remaining field inequality is the numerical potential certificate. -/
 theorem eventually_configuration_energy_bound_with_tail (η : ℝ) (hη : 0 < η) :
    ∀ᶠ K : ℕ in atTop, ∀ (h : ℕ) (t : Fin h → ℝ),
      Function.Injective t → (∀ i, 0 < t i) → 0 < (K : ℝ) →
      (h : ℝ)/(K : ℝ) = 37/40 → ∀ (M : ℝ) (V : ℝ → ℝ),
      (∀ x : ℝ, 0 < x → 2*potential x-V x+Real.sqrt x/(K : ℝ) ≤ M) →
      2*(∑ i, ∑ j ∈ Finset.Ioi i, Real.log |t i-t j|)-(K : ℝ)*(∑ i, V (t i))+
        (∑ i, Real.sqrt (t i)) ≤
        ((37/40 : ℝ)*M-mutualEnergy rho rho+2*(37/40 : ℝ)*η)*(K : ℝ)^2+
          (h : ℝ)*Real.log ((K : ℝ)+1) := by
  filter_upwards [eventually_truncated_potential_le η hη] with K htrunc h t ht ht0 hK hmass M V hfield
  have hb := configuration_energy_bound_with_tail t ht ht0 hK hmass
    (by positivity : 0 < 1/((K : ℝ)+1)) η M V htrunc hfield
  simpa only [one_div,Real.log_inv,mul_neg,sub_neg_eq_add] using hb

#print axioms doubleLogSum_eq_pair_sum
#print axioms configuration_energy_bound_with_tail
#print axioms eventually_configuration_energy_bound_with_tail
#print axioms sigma_rho_comparison
#print axioms configuration_energy_bound
#print axioms sigma_add_rho_log_integrable
#print axioms sigma_rho_energy
#print axioms sigma_energy_lower
end Zeta5ConfigurationEnergy
