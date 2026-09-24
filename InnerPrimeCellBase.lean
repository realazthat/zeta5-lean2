import ScalarUniform
import Mathlib.Tactic

noncomputable section
namespace Zeta5InnerAsymptotics

theorem floor_linear_interval (x l r a : ℚ) (m : ℤ)
    (hl : l≤x) (hr : x<r) (ha : 0<a)
    (hlo : (m:ℚ)≤a*l) (hhi : a*r≤(m:ℚ)+1) :
    ⌊a*x⌋=m := by
  apply Int.floor_eq_iff.mpr
  constructor <;> nlinarith

end Zeta5InnerAsymptotics
