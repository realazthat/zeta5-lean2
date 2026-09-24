import LeanCert.Tactic.IntervalAuto.PointIneq
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta5AppendixNumerics

noncomputable def componentPotential (a b t : ℝ) : ℝ :=
  if a ≤ t ∧ t ≤ b then Real.log ((b-a)/4)
  else Real.log ((|t-(a+b)/2| + Real.sqrt ((t-a)*(t-b)))/2)

noncomputable def potential (t : ℝ) : ℝ :=
  (525779809/50000000000 : ℝ) * componentPotential (1953374043/500000000000 : ℝ) (8992695531/1000000000000 : ℝ) t +
  (29471737793/1000000000000 : ℝ) * componentPotential (289031033/125000000000 : ℝ) (3068199571/200000000000 : ℝ) t +
  (42934365099/1000000000000 : ℝ) * componentPotential (280457333/200000000000 : ℝ) (6432545181/250000000000 : ℝ) t +
  (29102115983/500000000000 : ℝ) * componentPotential (220431339/250000000000 : ℝ) (20954789123/500000000000 : ℝ) t +
  (6903762131/100000000000 : ℝ) * componentPotential (289098953/500000000000 : ℝ) (65851089563/1000000000000 : ℝ) t +
  (78873099189/1000000000000 : ℝ) * componentPotential (396324613/1000000000000 : ℝ) (24870259471/250000000000 : ℝ) t +
  (84856120711/1000000000000 : ℝ) * componentPotential (283911191/1000000000000 : ℝ) (72162863729/500000000000 : ℝ) t +
  (88396082127/1000000000000 : ℝ) * componentPotential (53051547/250000000000 : ℝ) (201105762729/1000000000000 : ℝ) t +
  (706427057/8000000000 : ℝ) * componentPotential (82548843/500000000000 : ℝ) (269345996903/1000000000000 : ℝ) t +
  (17094464251/200000000000 : ℝ) * componentPotential (33336783/250000000000 : ℝ) (86772388539/250000000000 : ℝ) t +
  (39449592119/500000000000 : ℝ) * componentPotential (55761057/500000000000 : ℝ) (86161340883/200000000000 : ℝ) t +
  (35176735959/500000000000 : ℝ) * componentPotential (19269871/200000000000 : ℝ) (515561896511/1000000000000 : ℝ) t +
  (11767795323/200000000000 : ℝ) * componentPotential (85815639/1000000000000 : ℝ) (297724389273/500000000000 : ℝ) t +
  (22210660553/500000000000 : ℝ) * componentPotential (78667711/1000000000000 : ℝ) (664241383483/1000000000000 : ℝ) t +
  (30462865791/1000000000000 : ℝ) * componentPotential (14825913/200000000000 : ℝ) (89520072139/125000000000 : ℝ) t +
  (5959622577/1000000000000 : ℝ) * componentPotential (7174131/100000000000 : ℝ) (746637295669/1000000000000 : ℝ) t

noncomputable def field (t : ℝ) : ℝ :=
  Real.log (1+t) -6*(3/40)*Real.log (t+(3/40)^2)-2+12*(3/40)
    +2*Real.sqrt t*(Real.pi+Real.arctan (1/Real.sqrt t)-6*Real.arctan ((3/40)/Real.sqrt t))

noncomputable def vstar : ℝ :=
  Real.log (1+59205077/10000000000)-6*(3/40)*Real.log (59205079/10000000000+(3/40)^2)
    -2+12*(3/40)+2*Real.sqrt (59205079/10000000000)*
      (Real.pi+Real.arctan (1/Real.sqrt (59205079/10000000000))
        -6*Real.arctan ((3/40)/Real.sqrt (59205077/10000000000)))

lemma log_sqrt_upper {s x u L : ℝ} (hs : 0 < s) (hu : 0 ≤ u)
    (hxu : x ≤ u^2) (hL : Real.log ((s+u)/2) ≤ L) :
    Real.log ((s+Real.sqrt x)/2) ≤ L := by
  apply le_trans _ hL
  apply Real.log_le_log (by positivity)
  gcongr
  exact Real.sqrt_le_iff.mpr ⟨hu, hxu⟩

lemma arctan_upper {x a : ℝ} (ha₀ : -(Real.pi/2) < a) (ha₁ : a < Real.pi/2)
    (h : x * Real.cos a ≤ Real.sin a) : Real.arctan x ≤ a := by
  rw [← Real.arctan_tan ha₀ ha₁]
  apply Real.arctan_mono
  rw [Real.tan_eq_sin_div_cos]
  exact (le_div_iff₀ (Real.cos_pos_of_mem_Ioo ⟨ha₀, ha₁⟩)).2 h

lemma arctan_lower {x a : ℝ} (ha₀ : -(Real.pi/2) < a) (ha₁ : a < Real.pi/2)
    (h : Real.sin a ≤ x * Real.cos a) : a ≤ Real.arctan x := by
  rw [← Real.arctan_tan ha₀ ha₁]
  apply Real.arctan_mono
  rw [Real.tan_eq_sin_div_cos]
  exact (div_le_iff₀ (Real.cos_pos_of_mem_Ioo ⟨ha₀, ha₁⟩)).2 h

lemma arctan_div_sqrt_upper {t c u A : ℝ} (hc : 0 ≤ c) (hu : 0 < u)
    (hut : u^2 ≤ t) (hA : Real.arctan (c/u) ≤ A) :
    Real.arctan (c/Real.sqrt t) ≤ A := by
  have hs : u ≤ Real.sqrt t := Real.le_sqrt_of_sq_le hut
  apply le_trans _ hA
  gcongr

lemma arctan_div_sqrt_lower {t c u A : ℝ} (hc : 0 ≤ c) (ht : 0 < t) (hu : 0 ≤ u)
    (htu : t ≤ u^2) (hA : A ≤ Real.arctan (c/u)) :
    A ≤ Real.arctan (c/Real.sqrt t) := by
  have hs : Real.sqrt t ≤ u := Real.sqrt_le_iff.mpr ⟨hu, htu⟩
  apply le_trans hA
  gcongr

end Zeta5AppendixNumerics
