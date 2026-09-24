import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

open MeasureTheory Filter Set
open scoped Topology
noncomputable section
namespace Zeta5NormalizationTail

def α : ℝ := 3 / 40
def lam : ℝ := 37 / 40
def G (v : ℝ) : ℝ := v * (1-v) * (2*v-1) / 6
def B (v : ℝ) : ℝ := v * (1-v)
def F (x : ℝ) : ℝ := 4*lam + 2*lam*Int.fract x - 12*lam*Int.fract (α*x)
def P (x : ℝ) : ℝ := 74*B (Int.fract (α*x)) - lam*B (Int.fract x)
def C (x : ℝ) : ℝ := (74/α)*G (Int.fract (α*x)) - lam*G (Int.fract x)
def pbar : ℝ := 2923/240

theorem cubic_bound {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : u-u^3 ≤ 2/5 := by
  by_cases h : u ≤ 2/5
  · nlinarith [pow_nonneg hu0 3]
  · have hprod := mul_nonneg (sq_nonneg (u-3/5)) (show 0 ≤ u+6/5 by linarith)
    nlinarith

theorem G_bound {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) : |G v| ≤ 1/60 := by
  rw [abs_le]
  have hpos : ∀u : ℝ, 0≤u → u≤1 → u*(1-u^2) ≤ 2/5 := by
    intro u h0 h1
    nlinarith [cubic_bound h0 h1]
  by_cases h : 0 ≤ 2*v-1
  · have hu := hpos (2*v-1) h (by linarith)
    have hn := mul_nonneg h (show 0 ≤ 1-(2*v-1)^2 by nlinarith)
    constructor <;> dsimp [G] <;> nlinarith
  · have hu := hpos (1-2*v) (by linarith) (by linarith)
    have hn := mul_nonneg (show 0 ≤ 1-2*v by linarith) (show 0 ≤ 1-(1-2*v)^2 by nlinarith)
    constructor <;> dsimp [G] <;> nlinarith

theorem C_bound (x : ℝ) : |C x| ≤ 17 := by
  have h1 := G_bound (Int.fract_nonneg (α*x)) (Int.fract_lt_one (α*x)).le
  have h2 := G_bound (Int.fract_nonneg x) (Int.fract_lt_one x).le
  calc
    |C x| ≤ |74/α| * |G (Int.fract (α*x))| + |lam| * |G (Int.fract x)| := by
      simpa only [C, abs_mul] using abs_sub ((74/α)*G (Int.fract (α*x))) (lam*G (Int.fract x))
    _ ≤ |74/α| * (1/60) + |lam| * (1/60) := add_le_add
      (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
      (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
    _ ≤ 17 := by norm_num [α, lam]

theorem fract_deriv_right (x : ℝ) :
    HasDerivWithinAt Int.fract 1 (Ioi x) x := by
  have he : ∀ᶠ y in 𝓝[Ioi x] x, Int.floor y = Int.floor x :=
    (tendsto_pure.mp (tendsto_floor_right_pure_floor x)).filter_mono
      (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have hd := ((hasDerivAt_id x).sub_const (Int.floor x : ℝ)).hasDerivWithinAt (s := Ioi x)
  apply hd.congr_of_eventuallyEq
  · filter_upwards [he] with y hy
    simp only [Int.fract, hy, id_eq]
  · rfl

theorem fract_mul_deriv_right (a x : ℝ) (ha : 0 < a) :
    HasDerivWithinAt (fun y => Int.fract (a*y)) a (Ioi x) x := by
  have hd := (fract_deriv_right (a*x)).comp x
    (((hasDerivAt_id x).const_mul a).hasDerivWithinAt (s := Ioi x))
    (show MapsTo (fun y : ℝ => a*y) (Ioi x) (Ioi (a*x)) from
      fun y hy => mul_lt_mul_of_pos_left hy ha)
  simpa only [Function.comp_def, mul_one, one_mul] using hd

theorem continuous_P : Continuous P := by
  have hB : Continuous (fun x : ℝ => B (Int.fract x)) :=
    (show ContinuousOn B (Icc 0 1) from (by unfold B; fun_prop)).comp_fract'' (by norm_num [B])
  exact (hB.comp (continuous_const.mul continuous_id)).const_mul 74 |>.sub (hB.const_mul lam)

theorem continuous_C : Continuous C := by
  have hG : Continuous (fun x : ℝ => G (Int.fract x)) :=
    (show ContinuousOn G (Icc 0 1) from (by unfold G; fun_prop)).comp_fract'' (by norm_num [G])
  exact (hG.comp (continuous_const.mul continuous_id)).const_mul (74/α) |>.sub (hG.const_mul lam)

theorem P_deriv_right (x : ℝ) :
    HasDerivWithinAt P (F x+lam) (Ioi x) x := by
  have hf := fract_deriv_right x
  have hg := fract_mul_deriv_right α x (by norm_num [α])
  have hd := (hg.mul (hg.const_sub 1)).const_mul 74 |>.sub
    ((hf.mul (hf.const_sub 1)).const_mul lam)
  convert hd using 1 <;> (try dsimp [P, B, F, α, lam]) <;> first | rfl | ring

theorem C_deriv_right (x : ℝ) :
    HasDerivWithinAt C (P x-pbar) (Ioi x) x := by
  have hf := fract_deriv_right x
  have hg := fract_mul_deriv_right α x (by norm_num [α])
  have hd := ((((hg.mul (hg.const_sub 1)).mul ((hg.const_mul 2).sub_const 1)).div_const 6).const_mul (74/α)).sub
    ((((hf.mul (hf.const_sub 1)).mul ((hf.const_mul 2).sub_const 1)).div_const 6).const_mul lam)
  convert hd using 1 <;> (try dsimp [C, G, P, B, pbar, α, lam]) <;> first | rfl | ring

/-- An upper antiderivative: its right derivative dominates the tail kernel. -/
def U (x : ℝ) : ℝ := lam/x + P x/x^2 - pbar/x^2 + 2*C x/x^3 - 34/x^3 - (13/16)/x^2

def Uderiv (x : ℝ) : ℝ := F x/x^2 + 6*(17-C x)/x^4 + (13/8)/x^3

theorem U_deriv_right {x : ℝ} (hx : x ≠ 0) :
    HasDerivWithinAt U (Uderiv x) (Ioi x) x := by
  have hi := (hasDerivAt_id x).hasDerivWithinAt (s := Ioi x)
  have h2 := hi.pow 2
  have h3 := hi.pow 3
  have hc (c : ℝ) := hasDerivWithinAt_const x (Ioi x) c
  have hd := (((((hc lam).div hi hx).add
    ((P_deriv_right x).div h2 (pow_ne_zero 2 hx))).sub
    ((hc pbar).div h2 (pow_ne_zero 2 hx))).add
    (((C_deriv_right x).const_mul 2).div h3 (pow_ne_zero 3 hx))).sub
    ((hc 34).div h3 (pow_ne_zero 3 hx)) |>.sub
    ((hc (13/16)).div h2 (pow_ne_zero 2 hx))
  convert hd using 1 <;> first | rfl | (simp only [Uderiv, id_eq, Pi.pow_apply, Nat.cast_ofNat]; field_simp; ring)

theorem continuousOn_U {a b : ℝ} (ha : 0 < a) : ContinuousOn U (Icc a b) := by
  unfold U
  have hi : ContinuousOn (fun x : ℝ => x) (Icc a b) := continuousOn_id
  have hn : ∀x ∈ Icc a b, x ≠ 0 := fun x hx => ne_of_gt (ha.trans_le hx.1)
  have hP := continuous_P.continuousOn (s := Icc a b)
  have hC := continuous_C.continuousOn (s := Icc a b)
  fun_prop (disch := solve_by_elim [pow_ne_zero])

theorem tail_integral_le_upper_primitive {R : ℝ → ℝ} {M : ℝ} (hM : 20 ≤ M)
    (hR : IntegrableOn (fun x => R x/x^3) (Icc 20 M))
    (hbound : ∀x ∈ Ioo 20 M, R x ≤ x*F x+13/8) :
    (∫ x in (20:ℝ)..M, R x/x^3) ≤ U M-U 20 := by
  apply intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hM
    (continuousOn_U (by norm_num))
    (fun x hx => U_deriv_right (by linarith [hx.1])) hR
  intro x hx
  have hxp : 0<x := by linarith [hx.1]
  have hc : C x ≤ 17 := (le_abs_self _).trans (C_bound x)
  have hh := div_le_div_of_nonneg_right (hbound x hx) (le_of_lt (pow_pos hxp 3))
  have hn := div_nonneg (show 0 ≤ 6*(17-C x) by linarith) (pow_nonneg hxp.le 4)
  have hid : (x*F x+13/8)/x^3 = F x/x^2+(13/8)/x^3 := by
    field_simp
    <;> ring
  rw [hid] at hh
  dsimp [Uderiv]
  linarith

theorem P_twenty : P 20 = 37/2 := by norm_num [P, B, α, lam, Int.fract]
theorem C_twenty : C 20 = 0 := by norm_num [C, G, α, lam, Int.fract]

theorem U_twenty : U 20 = 2677/48000 := by
  norm_num [U, P_twenty, C_twenty, lam, pbar]

theorem tail_integral_bound {R : ℝ → ℝ} {M : ℝ} (hM : 20 ≤ M)
    (hR : IntegrableOn (fun x => R x/x^3) (Icc 20 M))
    (hbound : ∀x ∈ Ioo 20 M, R x ≤ x*F x+13/8)
    (hP : P M=0) (hC : C M=0) :
    (∫ x in (20:ℝ)..M, R x/x^3) ≤
      -(2677/48000) + lam/M - (pbar-1/4)/M^2 + 34/M^3 := by
  have hm : 0<M := by linarith
  have hb := tail_integral_le_upper_primitive hM hR hbound
  rw [U_twenty] at hb
  dsimp [U] at hb
  rw [hP,hC] at hb
  have h2 : 0 ≤ 1/M^2 := div_nonneg (by norm_num) (sq_nonneg M)
  have h3 : 0 ≤ 1/M^3 := div_nonneg (by norm_num) (pow_nonneg hm.le 3)
  have heq :
      (lam/M + 0/M^2 - pbar/M^2 + 2*0/M^3 - 34/M^3 - (13/16)/M^2 - 2677/48000)
      + (17/16)*(1/M^2) + 68*(1/M^3) =
      -(2677/48000) + lam/M - (pbar-1/4)/M^2 + 34/M^3 := by ring
  rw [← heq]
  linarith

/-- The finite tail bound at the fixed cutoff used in the irrationality proof. -/
theorem tail_integral_bound_100000 {R : ℝ → ℝ}
    (hR : IntegrableOn (fun x => R x/x^3) (Icc 20 100000))
    (hbound : ∀x ∈ Ioo 20 100000, R x ≤ x*F x+13/8) :
    (∫ x in (20:ℝ)..100000, R x/x^3) ≤ -(6970198065777/125000000000000) := by
  have hP : P 100000=0 := by norm_num [P, B, α, lam, Int.fract]
  have hC : C 100000=0 := by norm_num [C, G, α, lam, Int.fract]
  simpa only [lam, pbar] using
    (by convert tail_integral_bound (by norm_num : (20:ℝ)≤100000) hR hbound hP hC using 1 <;> norm_num [lam,pbar])

/-- Combined outer, bounded-inner, tail, small-prime and allocation-loss constant.
The two conservative losses are 9/640 for the outer rank and 1/36 for inner allocation. -/
def normalizationCoefficient : ℚ :=
  129101/96000 + 322437603634266857629/7535670527041937280000 - 2677/48000 +
  7*(37/40)/100000 - (2923/240-1/4)/(100000:ℚ)^2 + 34/(100000:ℚ)^3 + 1/36

theorem normalizationCoefficient_eq : normalizationCoefficient =
    2001164943296771438302478205521/1471810649812878375000000000000 := by
  norm_num [normalizationCoefficient]

/-- Exact margin after all three deliberately weakened bounds; it exceeds ten. -/
theorem adjusted_margin :
    -1600*(normalizationCoefficient-2733991/2000000) =
      10793591849509142369834294479/919881656133048984375000000 ∧
    10 < -1600*(normalizationCoefficient-2733991/2000000) := by
  norm_num [normalizationCoefficient]

#print axioms Zeta5NormalizationTail.C_bound
#print axioms Zeta5NormalizationTail.C_deriv_right
#print axioms Zeta5NormalizationTail.tail_integral_bound
#print axioms Zeta5NormalizationTail.tail_integral_bound_100000
#print axioms Zeta5NormalizationTail.adjusted_margin
end Zeta5NormalizationTail
