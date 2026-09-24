import ExternalField
import AppendixNumericSpecial
import AppendixCellBase

noncomputable section
open Set Filter
open scoped Topology

namespace Zeta5AppendixNumerics

def fieldBracket (y : ℝ) : ℝ :=
  Real.pi+Real.arctan (1/y)-6*Real.arctan ((3/40:ℝ)/y)

def fieldPhi (y : ℝ) : ℝ :=
  Real.log (1+y^2)-6*(3/40)*Real.log (y^2+(3/40)^2)-2+12*(3/40)+
    2*(y*fieldBracket y)

lemma arctan_const_div_hasDerivAt {c y : ℝ} (hc : 0 < c) (hy : 0 < y) :
    HasDerivAt (fun u : ℝ => Real.arctan (c/u)) (-c/(y^2+c^2)) y := by
  apply (((hasDerivAt_const y c).div (hasDerivAt_id y) hy.ne').arctan).congr_deriv
  have h1 : 1+(c/y)^2 ≠ 0 := by positivity
  have h2 : y^2+c^2 ≠ 0 := by positivity
  simp only [Pi.div_apply, id_eq, zero_mul, mul_one, zero_sub]
  field_simp

lemma fieldBracket_hasDerivAt {y : ℝ} (hy : 0 < y) :
    HasDerivAt fieldBracket
      (-1/(1+y^2)+(9/20:ℝ)/((3/40)^2+y^2)) y := by
  have h1 := arctan_const_div_hasDerivAt (c := 1) (by norm_num) hy
  have h2 := arctan_const_div_hasDerivAt (c := 3/40) (by norm_num) hy
  apply ((h1.const_add Real.pi).sub (h2.const_mul 6)).congr_deriv
  ring

lemma fieldBracket_monotone : MonotoneOn fieldBracket (Ioc 0 (1/2:ℝ)) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioc 0 (1/2:ℝ))
  · intro y hy
    exact (fieldBracket_hasDerivAt hy.1).continuousAt.continuousWithinAt
  · intro y hy
    exact (fieldBracket_hasDerivAt (interior_subset hy).1).hasDerivWithinAt
  · intro y hy
    have hy' := interior_subset hy
    have h1 : 0 < 1+y^2 := by positivity
    have h2 : 0 < (3/40:ℝ)^2+y^2 := by positivity
    have hsq : y^2 ≤ (1/4:ℝ) := by nlinarith [hy'.1, hy'.2]
    have hb : 1/(1+y^2) ≤ (9/20:ℝ)/((3/40)^2+y^2) := by
      apply (div_le_div_iff₀ h1 h2).mpr
      nlinarith
    rw [neg_div]
    linarith

lemma fieldBracket_positive_large {y : ℝ} (hy : (1/2:ℝ) ≤ y) :
    0 < fieldBracket y := by
  have hyp : 0 < y := by linarith
  have hs : 0 < Real.sqrt 3 := by positivity
  have hs2 : Real.sqrt 3 ≤ 2 := by apply Real.sqrt_le_iff.mpr; norm_num
  have ha : (3/40:ℝ)/y ≤ (Real.sqrt 3)⁻¹ := by
    rw [inv_eq_one_div, div_le_div_iff₀ hyp hs]
    nlinarith
  have hatan := Real.arctan_strictMono.monotone ha
  rw [Real.arctan_inv_sqrt_three] at hatan
  have hp : 0 < Real.arctan (1/y) := Real.arctan_pos.mpr (by positivity)
  unfold fieldBracket
  linarith

lemma fieldPhi_hasDerivAt {y : ℝ} (hy : 0 < y) :
    HasDerivAt fieldPhi (2*fieldBracket y) y := by
  have h1 := (((hasDerivAt_id y).pow 2).const_add 1).log (by change 1+y^2 ≠ 0; positivity)
  have h2 := (((hasDerivAt_id y).pow 2).add_const ((3/40:ℝ)^2)).log (by change y^2+(3/40:ℝ)^2 ≠ 0; positivity)
  have h3 := ((hasDerivAt_id y).mul (fieldBracket_hasDerivAt hy)).const_mul 2
  apply ((((h1.sub (h2.const_mul (6*(3/40:ℝ)))).sub_const 2).add_const
    (12*(3/40:ℝ))).add h3).congr_deriv
  simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, one_mul]
  have hq : y^2+(3/40:ℝ)^2 ≠ 0 := by positivity
  have hq' : (3/40:ℝ)^2+y^2 ≠ 0 := by positivity
  have ho : 1+y^2 ≠ 0 := by positivity
  field_simp
  ring

lemma fieldPhi_sqrt {t : ℝ} (ht : 0 ≤ t) : fieldPhi (Real.sqrt t) = field t := by
  unfold fieldPhi fieldBracket field
  rw [Real.sq_sqrt ht]
  ring

lemma field_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt field (fieldBracket (Real.sqrt t)/Real.sqrt t) t := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hc := (fieldPhi_hasDerivAt hs).comp t (Real.hasDerivAt_sqrt ht.ne')
  have he : field =ᶠ[𝓝 t] fun u => fieldPhi (Real.sqrt u) := by
    filter_upwards [eventually_gt_nhds ht] with u hu
    exact (fieldPhi_sqrt hu.le).symm
  apply (hc.congr_of_eventuallyEq he).congr_deriv
  field_simp

lemma externalField_eq_field {t : ℝ} (ht : 0 < t) :
    Zeta5Construction.externalField (3/40) t = field t := by
  exact Zeta5Construction.externalField_eq_explicit (3/40) ht

abbrev qMinus : ℝ := 59205077/10000000000
abbrev qPlus : ℝ := 59205079/10000000000

lemma fieldBracket_nonpos_left {y : ℝ} (hy : 0 < y) (hyq : y ≤ Real.sqrt qMinus) :
    fieldBracket y ≤ 0 := by
  have hq : Real.sqrt qMinus ≤ (1/2:ℝ) := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num [qMinus]⟩
  have hm := fieldBracket_monotone
    (show y ∈ Ioc 0 (1/2:ℝ) from ⟨hy, hyq.trans hq⟩)
    (show Real.sqrt qMinus ∈ Ioc 0 (1/2:ℝ) from ⟨by positivity, hq⟩) hyq
  have hn := qminus_derivative_negative
  change 2*fieldBracket (Real.sqrt qMinus) < 0 at hn
  linarith

lemma fieldBracket_nonneg_right {y : ℝ} (hyq : Real.sqrt qPlus ≤ y) :
    0 ≤ fieldBracket y := by
  by_cases hy : y ≤ (1/2:ℝ)
  · have hp : 0 < Real.sqrt qPlus := by positivity
    have hm := fieldBracket_monotone
      (show Real.sqrt qPlus ∈ Ioc 0 (1/2:ℝ) from ⟨hp, hyq.trans hy⟩)
      (show y ∈ Ioc 0 (1/2:ℝ) from ⟨hp.trans_le hyq, hy⟩) hyq
    have hn := qplus_derivative_positive
    change 0 < 2*fieldBracket (Real.sqrt qPlus) at hn
    linarith
  · exact (fieldBracket_positive_large (le_of_not_ge hy)).le

lemma field_antitone_left : AntitoneOn field (Ioc 0 qMinus) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioc 0 qMinus)
  · intro t ht
    exact (field_hasDerivAt ht.1).continuousAt.continuousWithinAt
  · intro t ht
    exact (field_hasDerivAt (interior_subset ht).1).hasDerivWithinAt
  · intro t ht
    have ht' := interior_subset ht
    apply div_nonpos_of_nonpos_of_nonneg
    · exact fieldBracket_nonpos_left (Real.sqrt_pos.mpr ht'.1) (Real.sqrt_le_sqrt ht'.2)
    · exact Real.sqrt_nonneg _

lemma field_monotone_right : MonotoneOn field (Ici qPlus) := by
  have hp : (0:ℝ) < qPlus := by norm_num [qPlus]
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici qPlus)
  · intro t ht
    exact (field_hasDerivAt (hp.trans_le ht)).continuousAt.continuousWithinAt
  · intro t ht
    exact (field_hasDerivAt (hp.trans_le (interior_subset ht))).hasDerivWithinAt
  · intro t ht
    apply div_nonneg
    · exact fieldBracket_nonneg_right (Real.sqrt_le_sqrt (interior_subset ht))
    · exact Real.sqrt_nonneg _

lemma vstar_le_field_middle {t : ℝ} (ht : t ∈ Icc qMinus qPlus) : vstar ≤ field t := by
  have hqm : (0:ℝ) < qMinus := by norm_num [qMinus]
  have hqp : (0:ℝ) < qPlus := by norm_num [qPlus]
  have htp : 0 < t := hqm.trans_le ht.1
  have hsm : Real.sqrt qMinus ≤ Real.sqrt t := Real.sqrt_le_sqrt ht.1
  have hsp : Real.sqrt t ≤ Real.sqrt qPlus := Real.sqrt_le_sqrt ht.2
  have hm : Real.arctan ((3/40:ℝ)/Real.sqrt t) ≤
      Real.arctan ((3/40:ℝ)/Real.sqrt qMinus) := by
    apply Real.arctan_strictMono.monotone
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hsm
  have hp : Real.arctan (1/Real.sqrt qPlus) ≤ Real.arctan (1/Real.sqrt t) := by
    apply Real.arctan_strictMono.monotone
    exact div_le_div_of_nonneg_left zero_le_one (by positivity) hsp
  let d0 := Real.pi+Real.arctan (1/Real.sqrt qPlus)-6*Real.arctan ((3/40:ℝ)/Real.sqrt qMinus)
  have hd0 : d0 < 0 := vstar_parenthesis_negative
  have hdb : d0 ≤ fieldBracket (Real.sqrt t) := by unfold d0 fieldBracket; linarith
  have hm1 := mul_le_mul_of_nonpos_right hsp hd0.le
  have hm2 := mul_le_mul_of_nonneg_left hdb (Real.sqrt_nonneg t)
  have hl1 : Real.log (1+qMinus) ≤ Real.log (1+t) :=
    Real.log_le_log (by positivity) (by linarith [ht.1])
  have hl2 : Real.log (t+(3/40:ℝ)^2) ≤ Real.log (qPlus+(3/40:ℝ)^2) :=
    Real.log_le_log (by positivity) (add_le_add ht.2 (le_rfl : (3/40:ℝ)^2 ≤ (3/40)^2))
  unfold vstar field
  change Real.log (1+qMinus)-6*(3/40)*Real.log (qPlus+(3/40)^2)-2+12*(3/40)+
    2*Real.sqrt qPlus*d0 ≤ _
  change Real.log (1+qMinus)-6*(3/40)*Real.log (qPlus+(3/40)^2)-2+12*(3/40)+
    2*Real.sqrt qPlus*d0 ≤ Real.log (1+t)-6*(3/40)*Real.log (t+(3/40)^2)-2+12*(3/40)+
      2*Real.sqrt t*fieldBracket (Real.sqrt t)
  norm_num only [qMinus, qPlus, fieldBracket, d0] at hl1 hl2 hm1 hm2 ⊢
  nlinarith only [hl1, hl2, hm1, hm2]

lemma vstar_le_field {t : ℝ} (ht : 0 < t) : vstar ≤ field t := by
  have hq : qMinus ≤ qPlus := by norm_num [qMinus, qPlus]
  by_cases hm : t ≤ qMinus
  · exact (vstar_le_field_middle ⟨le_rfl, hq⟩).trans
      (field_antitone_left ⟨ht, hm⟩ ⟨by norm_num [qMinus], le_rfl⟩ hm)
  · by_cases hp : qPlus ≤ t
    · exact (vstar_le_field_middle ⟨hq, le_rfl⟩).trans
        (field_monotone_right (show qPlus ∈ Ici qPlus by simp) hp hp)
    · exact vstar_le_field_middle ⟨le_of_not_ge hm, le_of_not_ge hp⟩

/-- The analytic justification for every certified lower-field cell. -/
theorem lowerField_le_field {l r t : ℝ} (ht : 0 < t) (hlt : l ≤ t) (htr : t ≤ r) :
    lowerField l r ≤ field t := by
  unfold lowerField
  split_ifs with hr hl
  · exact field_antitone_left ⟨ht, htr.trans hr⟩ ⟨ht.trans_le htr, hr⟩ htr
  · exact field_monotone_right hl (hl.trans hlt) hlt
  · exact vstar_le_field ht

#print axioms lowerField_le_field

end Zeta5AppendixNumerics
