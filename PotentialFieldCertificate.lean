import ArcsineNumericBridge
import ArcsineMonotonicity
import ConfigurationEnergy
import FieldMinimum
import AppendixNumericalCertificate

namespace Zeta5ArcsineMixture
open MeasureTheory Real Metric Set
open Zeta5CirclePotential Zeta5CircleMeasures Zeta5EnergyMixtures
open Zeta5ConfigurationEnergy Zeta5Construction

 theorem numerical_field_eq_external {t : ℝ} (ht : 0 < t) :
    Zeta5AppendixNumerics.field t = externalField (3/40 : ℝ) t := by
  rw [externalField_eq_explicit _ ht]
  rfl

/-- The 684 certified cells imply the required potential bound on the compact interval. -/
 theorem compact_potential_field_bound {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 2) :
    2*potential t-externalField (3/40 : ℝ) t < -(1329/200 : ℝ) := by
  obtain ⟨c, _hc, hl, hr, hcert⟩ := Zeta5AppendixNumerics.interval_cell_certificate t ⟨ht.le,ht2⟩
  have hp := potential_cell_max (c.1 : ℝ) t (c.2 : ℝ) hl hr
  have hf := Zeta5AppendixNumerics.lowerField_le_field ht hl hr
  simp only [potential_eq_numerical_potential] at hp ⊢
  rw [numerical_field_eq_external ht] at hf
  unfold Zeta5AppendixNumerics.cellBound at hcert
  linarith

/-- The support bound and elementary tail estimate handle the unbounded half-line. -/
 theorem tail_potential_field_bound {t K : ℝ} (ht : 2 ≤ t) (hK : 2 ≤ K) :
    2*potential t-externalField (3/40 : ℝ) t+Real.sqrt t/K < -(1329/200 : ℝ) := by
  have hu := potential_tail_upper t ht
  have hv := externalField_lower (by norm_num : (0 : ℝ) ≤ 3/40) (by linarith : 0 < t)
  have hf := Zeta5RealEnergy.tail_field_bound ht hK
  calc
    _ ≤ 2*((37/40 : ℝ)*Real.log t)-
        (2*Real.pi*Real.sqrt t+(1-6*(3/40 : ℝ))*Real.log t-6*(3/40 : ℝ)^3/t)+
          Real.sqrt t/K := by linarith
    _ = (13/10 : ℝ)*Real.log t+6*(3/40 : ℝ)^3/t-
        (2*Real.pi-1/K)*Real.sqrt t := by ring
    _ < _ := hf

/-- The corrected field bound retains the integrable exponential tail. -/
 theorem corrected_potential_field_bound {K : ℝ} (hK : 2 ≤ K) {t : ℝ} (ht : 0 < t) :
    2*potential t-externalField (3/40 : ℝ) t+Real.sqrt t/K ≤
      -(1329/200 : ℝ)+Real.sqrt 2/K := by
  rcases le_total t 2 with ht2 | ht2
  · have hm := compact_potential_field_bound ht ht2
    have hs : Real.sqrt t/K ≤ Real.sqrt 2/K :=
      div_le_div_of_nonneg_right (Real.sqrt_le_sqrt ht2) (by linarith)
    linarith
  · have hm := tail_potential_field_bound ht2 hK
    have hs : 0 ≤ Real.sqrt 2/K := by positivity
    linarith

open Filter in
/-- The unconditional discrete logarithmic-energy estimate, with an arbitrarily
small asymptotic quadratic regularization loss. -/
 theorem eventually_discrete_energy_bound (η : ℝ) (hη : 0 < η) :
    ∀ᶠ K : ℕ in atTop, ∀ (h : ℕ) (t : Fin h → ℝ),
      Function.Injective t → (∀ i, 0 < t i) →
      (h : ℝ)/(K : ℝ) = 37/40 →
      2*(∑ i, ∑ j ∈ Finset.Ioi i, Real.log |t i-t j|)-(K : ℝ)*(∑ i, externalField (3/40 : ℝ) (t i))+
        (∑ i, Real.sqrt (t i)) ≤
        ((37/40 : ℝ)*(-(1329/200 : ℝ)+Real.sqrt 2/(K : ℝ))-
          Zeta5AppendixNumerics.energyValue+2*(37/40 : ℝ)*η)*(K : ℝ)^2+
          (h : ℝ)*Real.log ((K : ℝ)+1) := by
  filter_upwards [eventually_configuration_energy_bound_with_tail η hη,
    eventually_ge_atTop 2] with K hbound hK h t ht ht0 hmass
  have hK' : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hb := hbound h t ht ht0 (by linarith) hmass
    (-(1329/200 : ℝ)+Real.sqrt 2/(K : ℝ)) (externalField (3/40 : ℝ))
    (fun _ hx => corrected_potential_field_bound hK' hx)
  simpa only [rho_energy_eq_energyValue] using hb

#print axioms compact_potential_field_bound
#print axioms corrected_potential_field_bound
#print axioms eventually_discrete_energy_bound
end Zeta5ArcsineMixture
