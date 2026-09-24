import RealDeterminantAsymptotic
import AppendixNumerics

noncomputable section
open scoped BigOperators Topology
open MeasureTheory Set Filter
namespace Zeta5Construction

def paperRealCoefficient : ℝ :=
  -(37/40)*(1329/200)-Zeta5AppendixNumerics.energyValue

lemma eventually_sourceEnergyBound_of_discrete (η : ℝ)
    (hdiscrete : ∀ᶠ K : ℕ in atTop, ∀ (h : ℕ) (t : Fin h → ℝ),
      Function.Injective t → (∀ i, 0 < t i) → (h:ℝ)/(K:ℝ)=37/40 →
      2*(∑ i, ∑ j ∈ Finset.Ioi i, Real.log |t i-t j|)-(K:ℝ)*(∑ i, externalField (3/40) (t i))+
        (∑ i, Real.sqrt (t i)) ≤
        ((37/40)*(-(1329/200)+Real.sqrt 2/(K:ℝ))-Zeta5AppendixNumerics.energyValue+
          2*(37/40)*η)*(K:ℝ)^2+(h:ℝ)*Real.log ((K:ℝ)+1)) :
    ∀ᶠ n : ℕ in atTop, SourceEnergyBound paperRealCoefficient η n := by
  have hm : Tendsto (fun n : ℕ => 40*n) atTop atTop :=
    tendsto_atTop_mono (fun n => by change n ≤ 40*n; omega) tendsto_id
  filter_upwards [hm.eventually hdiscrete,
    eventually_ge_atTop 1] with n hb hn
  intro t ht hinj
  have hnp : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hmass : ((37*n:ℕ):ℝ)/((40*n:ℕ):ℝ)=37/40 := by push_cast; field_simp
  have he := hb (37*n) t hinj ht hmass
  unfold paperRealCoefficient
  push_cast at he
  convert he using 1 <;> ring

lemma paperRealCoefficient_lt :
    paperRealCoefficient+normalizationConstant (3/40) (37/40) < -(2733991/2000000:ℝ) := by
  simpa only [paperRealCoefficient, normalizationConstant, Zeta5AppendixNumerics.cstar, neg_div] using
    Zeta5AppendixNumerics.final_coefficient


end Zeta5Construction
