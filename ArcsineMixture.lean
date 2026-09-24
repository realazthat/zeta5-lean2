import EnergyMixtures
import RealEnergy

set_option maxHeartbeats 0

namespace Zeta5ArcsineMixture
open MeasureTheory Real Metric Set
open Zeta5RealEnergy Zeta5CirclePotential Zeta5CircleMeasures Zeta5EnergyMixtures

abbrev Component := Fin 16

def row (i : Component) : ℚ × ℚ × ℚ := arcsineData[i.val]'(by simpa [arcsineData] using i.isLt)
noncomputable def left (i : Component) : ℝ := (row i).1
noncomputable def right (i : Component) : ℝ := (row i).2.1
noncomputable def mass (i : Component) : ℝ := (row i).2.2

 theorem data_properties (i : Component) :
    0 < left i ∧ left i < right i ∧ right i < 1 ∧ 0 < mass i := by
  fin_cases i <;> norm_num [left,right,mass,row,arcsineData]

 theorem data_nested (i j : Component) (hij : i ≤ j) :
    left j ≤ left i ∧ right i ≤ right j := by
  change i.val ≤ j.val at hij
  fin_cases i <;> fin_cases j <;> norm_num [left,right,row,arcsineData] at *

/-- Compute the finite mass total in ℚ, then transport it to ℝ. Keeping the
arithmetic certificate rational avoids a deeply nested real-arithmetic proof
that overflows the independent NanoDa checker's stack. -/
theorem mass_sum : (∑ i, mass i) = (37/40 : ℝ) := by
  have rational_sum : (∑ i : Component, (row i).2.2) = (37/40 : ℚ) := by
    decide +kernel
  change (∑ i : Component, ((row i).2.2 : ℝ)) = _
  calc
    _ = ((∑ i : Component, (row i).2.2 : ℚ) : ℝ) :=
      (map_sum (Rat.castHom ℝ) _ _).symm
    _ = _ := by rw [rational_sum]; norm_num

noncomputable def componentMeasure (i : Component) : Measure ℂ :=
  arcsineMeasure (left i) (right i)
instance component_probability (i : Component) : IsProbabilityMeasure (componentMeasure i) := by
  unfold componentMeasure
  infer_instance
instance component_nullSingleton (i : Component) : NullSingletonClass (componentMeasure i) :=
  arcsineMeasure_nullSingleton _ _ (data_properties i).2.1
noncomputable def rho : Measure ℂ := weightedMeasure mass componentMeasure
instance rho_finite : IsFiniteMeasure rho := by unfold rho; infer_instance
instance rho_nullSingleton : NullSingletonClass rho :=
  weightedMeasure_nullSingleton mass componentMeasure (fun _ => inferInstance)

 theorem rho_mass : rho.real univ = (37/40 : ℝ) := by
  rw [rho, weightedMeasure_mass mass (fun i => (data_properties i).2.2.2.le),mass_sum]

 theorem components_log_integrable (i j : Component) :
    Integrable logKernel ((componentMeasure i).prod (componentMeasure j)) :=
  arcsine_arcsine_log_integrable _ _ _ _ (data_properties j).2.1
    (data_properties i).2.1 (data_properties j).1.le (data_properties j).2.2.1.le
    (data_properties i).1.le (data_properties i).2.2.1.le

 theorem rho_log_integrable : Integrable logKernel (rho.prod rho) :=
  log_integrable_weighted_product mass mass componentMeasure componentMeasure components_log_integrable

noncomputable def potential (t : ℝ) : ℝ := ∑ i, mass i*arcsinePotential (left i) (right i) t
noncomputable def truncatedPotential (ε t : ℝ) : ℝ :=
  ∑ i, mass i*truncatedArcsinePotential (left i) (right i) ε t

 theorem rho_potential (t : ℝ) :
    (∫ z : ℂ, Real.log ‖(t : ℂ)-z‖ ∂rho) = potential t := by
  rw [rho, integral_weightedMeasure mass (fun i => (data_properties i).2.2.2.le)
    componentMeasure _ (fun i => arcsine_real_log_integrable _ _ t (data_properties i).2.1)]
  simp only [componentMeasure,arcsine_real_log_integral,potential]

 theorem component_mutual_energy (i j : Component) :
    mutualEnergy (componentMeasure i) (componentMeasure j) =
      Real.log ((right (max i j)-left (max i j))/4) := by
  rcases le_total i j with hij | hji
  · rw [max_eq_right hij]
    unfold mutualEnergy
    rw [integral_prod _ (components_log_integrable i j)]
    exact nested_arcsine_energy _ _ _ _ (data_properties j).2.1 (data_properties i).2.1
      (data_nested i j hij).1 (data_nested i j hij).2
  · rw [max_eq_left hji, mutualEnergy_symm _ _ (components_log_integrable i j)]
    unfold mutualEnergy
    rw [integral_prod _ (components_log_integrable j i)]
    exact nested_arcsine_energy _ _ _ _ (data_properties i).2.1 (data_properties j).2.1
      (data_nested j i hji).1 (data_nested j i hji).2

 theorem rho_energy : mutualEnergy rho rho =
    ∑ i, ∑ j, mass i*mass j*Real.log ((right (max i j)-left (max i j))/4) := by
  rw [rho, energy_weighted_product mass mass (fun i => (data_properties i).2.2.2.le)
    (fun i => (data_properties i).2.2.2.le) componentMeasure componentMeasure components_log_integrable]
  simp_rw [component_mutual_energy]

open Filter in
 theorem eventually_truncated_potential_le (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, 0 ≤ t →
      truncatedPotential (1/((n : ℝ)+1)) t ≤ potential t+η := by
  have he : ∀ᶠ n : ℕ in atTop, ∀ i : Component, ∀ t : ℝ, 0 ≤ t →
      truncatedArcsinePotential (left i) (right i) (1/((n : ℝ)+1)) t ≤
        arcsinePotential (left i) (right i) t+η :=
    Filter.eventually_all.2 (fun i => eventually_truncated_arcsine_le _ _
      (data_properties i).2.1 (data_properties i).2.2.1.le η hη)
  filter_upwards [he] with n hn t ht
  calc
    _ ≤ ∑ i, mass i*(arcsinePotential (left i) (right i) t+η) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hn i t ht) (data_properties i).2.2.2.le
    _ = potential t+(37/40 : ℝ)*η := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul,mass_sum]
      rfl
    _ ≤ potential t+η := by linarith

 theorem rho_circle_log_integrable (t : ℝ) {R : ℝ} (hR : 0 < R) :
    Integrable logKernel (rho.prod (circleMeasure (t : ℂ) R)) := by
  rw [rho,weightedMeasure,Measure.prod_sum_left]
  apply integrable_sum_measure
  · intro i
    rw [Measure.prod_smul_left]
    exact (arcsine_circle_log_integrable _ _ (data_properties i).2.1.le
      (data_properties i).1.le (data_properties i).2.2.1.le (t : ℂ) hR).smul_measure
        ENNReal.ofReal_ne_top
  · exact Summable.of_finite

 theorem rho_circle_energy (t : ℝ) {R : ℝ} (hR : 0 < R) :
    mutualEnergy rho (circleMeasure (t : ℂ) R) = truncatedPotential R t := by
  have hf (w : ℂ) : (∫ z : ℂ, Real.log ‖w-z‖ ∂circleMeasure (t : ℂ) R) =
      Real.log (max ‖(t : ℂ)-w‖ R) := by
    simpa only [norm_sub_rev] using circle_log_integral (t : ℂ) w hR
  have hc : Continuous (fun w : ℂ => Real.log (max ‖(t : ℂ)-w‖ R)) := by
    apply Continuous.log
    · fun_prop
    · intro w
      exact ne_of_gt (hR.trans_le (le_max_right _ _))
  unfold mutualEnergy
  rw [integral_prod _ (rho_circle_log_integrable t hR)]
  change (∫ w : ℂ, ∫ z : ℂ, Real.log ‖w-z‖ ∂circleMeasure (t : ℂ) R ∂rho) = _
  simp_rw [hf]
  rw [rho,integral_weightedMeasure mass (fun i => (data_properties i).2.2.2.le)
    componentMeasure _ (fun i => continuous_integrable_arcsine _ hc _ _)]
  unfold truncatedPotential
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [componentMeasure,← circle_arcsine_cross_energy (left i) (right i) t hR]
  simp_rw [hf]

#print axioms rho_mass
#print axioms rho_log_integrable
#print axioms rho_energy
#print axioms eventually_truncated_potential_le
#print axioms rho_circle_energy
end Zeta5ArcsineMixture
