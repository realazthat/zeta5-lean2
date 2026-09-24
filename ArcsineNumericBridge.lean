import ArcsineMixture
import AppendixNumericBase
import AppendixNumerics

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5ArcsineMixture
open MeasureTheory Real Metric Set
open Zeta5CirclePotential Zeta5CircleMeasures Zeta5EnergyMixtures

 theorem arcsinePotential_eq_componentPotential (a b t : ℝ) (hab : a < b) :
    arcsinePotential a b t = Zeta5AppendixNumerics.componentPotential a b t := by
  unfold Zeta5AppendixNumerics.componentPotential
  by_cases h : a ≤ t ∧ t ≤ b
  · rw [if_pos h]
    exact arcsine_potential_inside a b t hab h
  · rw [if_neg h]
    apply arcsine_potential_outside a b t hab
    rcases lt_or_ge t a with ht | ht
    · exact Or.inl ht
    · exact Or.inr (lt_of_not_ge (fun hb => h ⟨ht,hb⟩))

/-- Expand the fixed component sum before arithmetic normalization to keep the
resulting proof shallow enough for the independent kernel checkers. -/
private lemma sum_fin16 (f : Fin 16 → ℝ) : (∑ i, f i) = f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + (f 10 + (f 11 + (f 12 + (f 13 + (f 14 + (f 15))))))))))))))) := by
  simp [Fin.sum_univ_succ]

 theorem potential_eq_numerical_potential (t : ℝ) :
    potential t = Zeta5AppendixNumerics.potential t := by
  unfold potential
  simp_rw [arcsinePotential_eq_componentPotential _ _ t (data_properties _).2.1]
  rw [sum_fin16]
  norm_num [mass,left,right,row,Zeta5RealEnergy.arcsineData,
    Zeta5AppendixNumerics.potential]
  ring

 theorem rho_energy_eq_energyValue :
    mutualEnergy rho rho = Zeta5AppendixNumerics.energyValue := by
  rw [rho_energy]
  simp_rw [sum_fin16]
  norm_num [mass,left,right,row,Zeta5RealEnergy.arcsineData,
    Zeta5AppendixNumerics.energyValue]
  ring

#print axioms potential_eq_numerical_potential
#print axioms rho_energy_eq_energyValue
end Zeta5ArcsineMixture
