import ScalarUniform
import Mathlib.Data.Rat.Floor
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

noncomputable section
namespace Zeta5RealKernel

def overlap (u v : ℝ) : ℝ :=
  if Int.fract u<1/2 then
    if Int.fract v<1/2 then min (Int.fract u) (Int.fract v)
    else max 0 (Int.fract u+Int.fract v-1)
  else
    if Int.fract v<1/2 then max 0 (Int.fract u+Int.fract v-1)
    else min (Int.fract u) (Int.fract v)-1/2

def highLength (u : ℝ) : ℝ := Int.fract (2*u)/2

def BB (x : ℝ) : ℝ := highLength (3/40*x)-2*(highLength (3/40*x))^2

def AB (x : ℝ) : ℝ := overlap (3/40*x) x-2*highLength (3/40*x)*highLength x

def gamma (x : ℝ) : ℝ :=
  let T : ℝ := ⌊23/10*x⌋
  let a : ℝ := ⌊3/20*x⌋
  let b : ℝ := ⌊2*x⌋
  (T^2-T*b-5*T-9*a^2+3*a*b+15*a)/2 +
  highLength x*(-T+3*a)+highLength (3/40*x)*(-18*a+3*b+6)+
  3*overlap (3/40*x) x+(23/10*x-T)/2*(2*T-b-5)+
  max ((23/10*x-T)/2-highLength x) 0

def scalar (x : ℝ) : ℝ :=
  let m : ℝ := ⌊37/20*x⌋
  2*(37/40*x)*(⌊x⌋:ℝ)-12*(37/40*x)*(⌊3/40*x⌋:ℝ)-
    2*(m*(37/40*x)-m*(m+1)/4)

def kernel (x : ℝ) : ℝ := -gamma x-scalar x

def linearPart (x : ℝ) : ℝ :=
  4*(37/40)+2*(37/40)*Int.fract x-12*(37/40)*Int.fract (3/40*x)

def remainder (x : ℝ) : ℝ :=
  let τ := Int.fract (23/10*x)
  let σ := Int.fract (2*x)
  let η := Int.fract (37/20*x)
  (τ*(τ-σ)-max (τ-σ) 0+η*(1-η))/2+9*BB x-3*AB x

theorem fract_double (u : ℝ) :
    Int.fract (2*u) = if Int.fract u<1/2 then 2*Int.fract u else 2*Int.fract u-1 := by
  have h0 := Int.fract_nonneg u
  have h1 := Int.fract_lt_one u
  split_ifs with h
  · apply Int.fract_eq_iff.mpr
    refine ⟨by linarith,by linarith,2*⌊u⌋,?_⟩
    unfold Int.fract
    push_cast
    ring
  · apply Int.fract_eq_iff.mpr
    refine ⟨by linarith,by linarith,2*⌊u⌋+1,?_⟩
    unfold Int.fract
    push_cast
    ring

theorem highLength_bounds (u : ℝ) : 0≤highLength u ∧ highLength u≤1/2 := by
  unfold highLength
  constructor
  · exact div_nonneg (Int.fract_nonneg _) (by norm_num)
  · have := Int.fract_lt_one (2*u)
    linarith

/-- The overlap of two high intervals has the usual elementary bounds. -/
theorem overlap_bounds (u v : ℝ) :
    max (highLength u+highLength v-1/2) 0≤overlap u v ∧
    overlap u v≤min (highLength u) (highLength v) := by
  have hu0 := Int.fract_nonneg u
  have hu1 := Int.fract_lt_one u
  have hv0 := Int.fract_nonneg v
  have hv1 := Int.fract_lt_one v
  unfold highLength overlap
  rw [fract_double,fract_double]
  simp only [min_def,max_def]
  split_ifs <;> constructor <;> linarith

theorem BB_bounds (x : ℝ) : 0≤BB x ∧ BB x≤1/8 := by
  have h := highLength_bounds (3/40*x)
  unfold BB
  constructor
  · nlinarith [mul_nonneg h.1 (sub_nonneg.mpr h.2)]
  · nlinarith [sq_nonneg (highLength (3/40*x)-1/4)]

private theorem product_quarter_bound (a b : ℝ) (ha : 0≤a) (hb : 0≤b)
    (hab : a+b≤1/2) : a*b≤1/16 := by
  nlinarith [sq_nonneg (a-b),mul_nonneg (sub_nonneg.mpr hab) (by linarith : 0≤1/2+(a+b))]

theorem AB_bounds (x : ℝ) : -(1/8)≤AB x ∧ AB x≤1/8 := by
  have ha := highLength_bounds (3/40*x)
  have hb := highLength_bounds x
  have ho := overlap_bounds (3/40*x) x
  have ho0 : 0≤overlap (3/40*x) x := (le_max_right _ _).trans ho.1
  have hos : highLength (3/40*x)+highLength x-1/2≤overlap (3/40*x) x :=
    (le_max_left _ _).trans ho.1
  have hoa : overlap (3/40*x) x≤highLength (3/40*x) := ho.2.trans (min_le_left _ _)
  have hob : overlap (3/40*x) x≤highLength x := ho.2.trans (min_le_right _ _)
  unfold AB
  constructor
  · by_cases hs : highLength (3/40*x)+highLength x≤1/2
    · nlinarith [product_quarter_bound _ _ ha.1 hb.1 hs]
    · have hp := product_quarter_bound (1/2-highLength (3/40*x)) (1/2-highLength x)
        (by linarith) (by linarith) (by linarith)
      nlinarith
  · rcases le_total (highLength (3/40*x)) (highLength x) with h | h
    · nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr h),sq_nonneg (highLength (3/40*x)-1/4)]
    · nlinarith [mul_nonneg hb.1 (sub_nonneg.mpr h),sq_nonneg (highLength x-1/4)]

theorem gamma_eq_moments (x : ℝ) :
    gamma x=Zeta5Inner.gammaFromMoments x (Int.fract (23/10*x))
      (Int.fract (2*x)) (BB x) (AB x) := by
  unfold gamma Zeta5Inner.gammaFromMoments BB AB highLength Int.fract
  rw [show 2*((3:ℝ)/40*x)=(3/20)*x by ring]
  dsimp only
  rw [←sub_div]
  rw [show max (((23/10*x-(⌊23/10*x⌋:ℝ))-(2*x-(⌊2*x⌋:ℝ)))/2) 0 =
      max ((23/10*x-(⌊23/10*x⌋:ℝ))-(2*x-(⌊2*x⌋:ℝ))) 0/2 by
        simpa only [zero_div] using max_div_div_right (by norm_num : (0:ℝ)≤2)
          ((23/10*x-(⌊23/10*x⌋:ℝ))-(2*x-(⌊2*x⌋:ℝ))) 0]
  ring

theorem scalar_eq_fractions (x : ℝ) :
    scalar x=Zeta5Inner.normalizationFromFractions x (Int.fract x)
      (Int.fract (3/40*x)) (Int.fract (37/20*x)) := by
  unfold scalar Zeta5Inner.normalizationFromFractions Int.fract
  ring

theorem kernel_decomposition (x : ℝ) : kernel x=x*linearPart x+remainder x := by
  unfold kernel
  rw [gamma_eq_moments,scalar_eq_fractions,Zeta5Inner.remainder_decomposition]
  unfold linearPart remainder
  ring

theorem remainder_bounds (x : ℝ) : -(1/2)≤remainder x ∧ remainder x≤13/8 := by
  have hB := BB_bounds x
  have hA := AB_bounds x
  exact Zeta5Inner.remainder_bounds _ _ _ _ _
    (Int.fract_nonneg _) (Int.fract_lt_one _).le
    (Int.fract_nonneg _) (Int.fract_lt_one _).le
    (Int.fract_nonneg _) (Int.fract_lt_one _).le hB.1 hB.2 hA.1 hA.2

open Zeta5InnerAsymptotics MeasureTheory Set

theorem overlap_rat_cast (u v : ℚ) :
    (overlapLimit u v:ℝ)=overlap u v := by
  unfold overlapLimit overlap
  have hu : Int.fract (u:ℝ)<1/2 ↔ Int.fract u<(1/2:ℚ) := by
    rw [←Rat.cast_fract]
    simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] using (Rat.cast_lt (K:=ℝ) (p:=Int.fract u) (q:=1/2))
  have hv : Int.fract (v:ℝ)<1/2 ↔ Int.fract v<(1/2:ℚ) := by
    rw [←Rat.cast_fract]
    simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] using (Rat.cast_lt (K:=ℝ) (p:=Int.fract v) (q:=1/2))
  simp only [hu,hv]
  split_ifs <;> push_cast <;> rfl

theorem gamma_rat_cast (x : ℚ) :
    (Zeta5InnerAsymptotics.gamma x:ℝ)=Zeta5RealKernel.gamma x := by
  unfold Zeta5InnerAsymptotics.gamma gammaAtAllocation baseIntegral
    baseConstant highKCoefficient highNCoefficient extraCost Zeta5RealKernel.gamma highLength
  push_cast
  rw [overlap_rat_cast]
  rw [show 2*((3:ℝ)/40*x)=3/20*x by ring]
  have hf (c : ℚ) : ⌊(c:ℝ)*(x:ℝ)⌋=⌊c*x⌋ := by
    rw [←Rat.cast_mul,Rat.floor_cast]
  have h23 := hf (23/10)
  have h3 := hf (3/20)
  have h2 := hf 2
  norm_num at h23 h3 h2
  rw [h23,h3,h2]
  push_cast
  rfl


theorem scalar_rat_cast (x : ℚ) :
    (scalarLimit x:ℝ)=scalar x := by
  unfold scalarLimit floorIntegral scalar
  rw [show 2*((37:ℚ)/40*x)=37/20*x by ring]
  push_cast
  have hf (c : ℚ) : ⌊(c:ℝ)*(x:ℝ)⌋=⌊c*x⌋ := by
    rw [←Rat.cast_mul,Rat.floor_cast]
  have h3 := hf (3/40)
  have h37 := hf (37/20)
  norm_num at h3 h37
  rw [h3,h37,Rat.floor_cast]
  ring

theorem kernel_rat_cast (x : ℚ) : (innerKernel x:ℝ)=kernel x := by
  unfold innerKernel kernel
  push_cast
  rw [gamma_rat_cast,scalar_rat_cast]


theorem measurable_overlap : Measurable (fun q : ℝ×ℝ => overlap q.1 q.2) := by
  unfold overlap
  apply Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
  · apply Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) <;> fun_prop
  · apply Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) <;> fun_prop

theorem measurable_remainder : Measurable remainder := by
  unfold remainder BB AB highLength
  dsimp only
  have h : Measurable (fun x : ℝ => overlap (3/40*x) x) :=
    measurable_overlap.comp (f:=fun x : ℝ => ((3/40:ℝ)*x,x)) (by fun_prop)
  fun_prop

theorem measurable_linearPart : Measurable linearPart := by
  unfold linearPart
  fun_prop

theorem measurable_kernel : Measurable kernel := by
  simp_rw [funext kernel_decomposition]
  exact measurable_id.mul measurable_linearPart |>.add measurable_remainder

theorem linearPart_bounds (x : ℝ) : -(37/5)≤linearPart x ∧ linearPart x≤111/20 := by
  have h0:=Int.fract_nonneg x
  have h1:=Int.fract_lt_one x
  have g0:=Int.fract_nonneg (3/40*x)
  have g1:=Int.fract_lt_one (3/40*x)
  unfold linearPart
  constructor <;> linarith

theorem kernel_integrableOn (a b : ℝ) : IntegrableOn kernel (Icc a b) := by
  apply Measure.integrableOn_of_bounded (M:=8*(|a|+|b|)+2) (measure_Icc_lt_top.ne)
    measurable_kernel.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  have hx0 : |x|≤|a|+|b| := by
    apply abs_le.mpr
    constructor
    · have:=neg_abs_le a; have:=abs_nonneg b; linarith [hx.1]
    · have:=le_abs_self b; have:=abs_nonneg a; linarith [hx.2]
  rw [Real.norm_eq_abs,kernel_decomposition]
  have hf : |linearPart x|≤8 := by
    apply abs_le.mpr
    constructor <;> linarith [(linearPart_bounds x).1,(linearPart_bounds x).2]
  have hr : |remainder x|≤2 := by
    apply abs_le.mpr
    constructor <;> linarith [(remainder_bounds x).1,(remainder_bounds x).2]
  calc
    |x*linearPart x+remainder x|≤|x*linearPart x|+|remainder x| := abs_add_le _ _
    _ ≤ (|a|+|b|)*8+2 := by
      rw [abs_mul]
      exact add_le_add (mul_le_mul hx0 hf (abs_nonneg _) (by positivity)) hr
    _ = _ := by ring

theorem kernel_div_cube_integrableOn (a b : ℝ) (ha : 0<a) :
    IntegrableOn (fun x => kernel x/x^3) (Icc a b) := by
  have hc : ContinuousOn (fun x : ℝ => (x^3)⁻¹) (Icc a b) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx
    exact pow_ne_zero _ (ne_of_gt (ha.trans_le hx.1))
  simpa only [div_eq_mul_inv] using (kernel_integrableOn a b).mul_continuousOn hc isCompact_Icc

#print axioms kernel_decomposition
#print axioms kernel_rat_cast
#print axioms kernel_div_cube_integrableOn
end Zeta5RealKernel

