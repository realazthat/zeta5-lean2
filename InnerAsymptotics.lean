import PaperParameters
import Allocation
import InnerValuation
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Tactic

/-!
# Exact pole counts and their limiting floor function

These lemmas connect the literal finite pole sets in `PaperParameters` to
the floor-function kernel used in Section 5.1.
-/

set_option maxHeartbeats 800000

namespace Zeta5InnerAsymptotics

open Finset

theorem single_class_count (A p a : ℕ) (hp : 0 < p)
    (ha : 0 < a) (hap : a < p) :
    (((Finset.Icc 1 A).filter fun j => j % p = a % p).card : ℤ) =
      ⌊((A : ℚ) - a) / p⌋ + 1 := by
  have hpq : (0 : ℚ) < p := by exact_mod_cast hp
  have haq : (0 : ℚ) < a := by exact_mod_cast ha
  have hapq : (a : ℚ) < p := by exact_mod_cast hap
  have hneg : ⌊(-(a : ℚ)) / p⌋ = (-1 : ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor
    · norm_num
      rw [le_div_iff₀ hpq]
      linarith
    · norm_num
      exact div_neg_of_neg_of_pos (neg_neg_of_pos haq) hpq
  have hfloor : (-1 : ℤ) ≤ ⌊((A : ℚ) - a) / p⌋ := by
    apply Int.le_floor.mpr
    norm_num
    rw [le_div_iff₀ hpq]
    nlinarith [show (0 : ℚ) ≤ A from Nat.cast_nonneg A]
  have hinterval : Finset.Icc 1 A = Finset.Ioc 0 A := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hinterval]
  have hc := Nat.Ioc_filter_modEq_card 0 A hp a
  simp only [Nat.ModEq, Nat.cast_zero, zero_sub, hneg, sub_neg_eq_add,
    max_eq_left (by omega : (0 : ℤ) ≤ ⌊((A : ℚ) - a) / p⌋ + 1)] at hc
  exact hc

/-- The exact finite pole count equals the limiting floor expression, rather
than merely approximating it. The approximation later is only in summing
these values over the grid of classes. -/
theorem poleCount_eq_floor (A p a : ℕ) (hp : 0 < p)
    (ha : 0 < a) (hhalf : 2 * a < p) :
    (Zeta5Parameters.poleCount A p a : ℤ) =
      ⌊((A : ℚ) - a) / p⌋ + ⌊((A : ℚ) + a) / p⌋ + 1 := by
  have hap : a < p := by omega
  have hb : 0 < p - a := by omega
  have hbp : p - a < p := by omega
  have hane : a ≠ p - a := by omega
  have hdis : Disjoint
      ((Finset.Icc 1 A).filter fun j => j % p = a % p)
      ((Finset.Icc 1 A).filter fun j => j % p = (p-a) % p) := by
    rw [Finset.disjoint_left]
    intro j hj₁ hj₂
    have h₁ := (Finset.mem_filter.mp hj₁).2
    have h₂ := (Finset.mem_filter.mp hj₂).2
    rw [Nat.mod_eq_of_lt hap] at h₁
    rw [Nat.mod_eq_of_lt hbp] at h₂
    exact hane (h₁.symm.trans h₂)
  unfold Zeta5Parameters.poleCount
  rw [Finset.filter_or, Finset.card_union_of_disjoint hdis, Nat.cast_add,
    single_class_count A p a hp ha hap,
    single_class_count A p (p-a) hp hb hbp]
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have harg : ((A : ℚ) - (p-a : ℕ)) / p = ((A : ℚ) + a) / p - 1 := by
    rw [Nat.cast_sub hap.le]
    field_simp
    ring
  rw [harg, Int.floor_sub_one]
  omega

theorem poleCount_eq_limiting (A p a : ℕ) (hp : 0 < p)
    (ha : 0 < a) (hhalf : 2 * a < p) :
    (Zeta5Parameters.poleCount A p a : ℤ) =
      Zeta5Inner.poleCount ((A : ℚ) / p) ((a : ℚ) / p) := by
  rw [poleCount_eq_floor A p a hp ha hhalf]
  unfold Zeta5Inner.poleCount
  rw [sub_div, add_div]

/-- The paper's finite ordinary class counts also take two consecutive values. -/
theorem actual_poleCount_two_values (A p a : ℕ) (hp : 0 < p)
    (ha : 0 < a) (hhalf : 2 * a < p) :
    (Zeta5Parameters.poleCount A p a : ℤ) = ⌊2 * ((A : ℚ) / p)⌋ ∨
      (Zeta5Parameters.poleCount A p a : ℤ) = ⌊2 * ((A : ℚ) / p)⌋ + 1 := by
  rw [poleCount_eq_limiting A p a hp ha hhalf]
  exact Zeta5Inner.poleCount_two_values _ _

/-- Pointwise count discrepancy, uniformly in the ordinary class. -/
theorem actual_poleCount_error (A p a : ℕ) (hp : 0 < p)
    (ha : 0 < a) (hhalf : 2*a < p) :
    |(Zeta5Parameters.poleCount A p a : ℚ) - 2*((A : ℚ)/p)| ≤ 1 := by
  have hfloor := Int.floor_le (2*((A : ℚ)/p))
  have hfloor' := Int.lt_floor_add_one (2*((A : ℚ)/p))
  rw [abs_le]
  rcases actual_poleCount_two_values A p a hp ha hhalf with h | h
  · have hq : (Zeta5Parameters.poleCount A p a : ℚ) =
        (⌊2*((A : ℚ)/p)⌋ : ℚ) := by exact_mod_cast h
    rw [hq]
    constructor <;> linarith

  · have hq : (Zeta5Parameters.poleCount A p a : ℚ) =
        (⌊2*((A : ℚ)/p)⌋ : ℚ) + 1 := by exact_mod_cast h
    rw [hq]
    constructor <;> linarith

/-- Integer form of the upper count bound needed for nonnegative allocation
dimensions, with no limiting hypotheses. -/
theorem poleCount_mul_le (A p a : ℕ) (hp : 0 < p)
    (ha : 0 < a) (hhalf : 2*a < p) :
    p * Zeta5Parameters.poleCount A p a ≤ 2*A+p := by
  have h := (abs_le.mp (actual_poleCount_error A p a hp ha hhalf)).2
  have hpq : (0 : ℚ) < p := by exact_mod_cast hp
  have hq : (Zeta5Parameters.poleCount A p a : ℚ) ≤
      (2*(A : ℚ)+p)/p := by
    calc
      _ ≤ 2*((A : ℚ)/p)+1 := by linarith
      _ = _ := by field_simp
  have hq' := (le_div_iff₀ hpq).mp hq
  rw [mul_comm] at hq'
  exact_mod_cast hq'
/-- The single-class count in quotient-and-remainder form. -/
theorem single_class_count_quotient (A p a : ℕ) (hp : 0 < p)
    (ha : 0 < a) (hap : a < p) :
    (((Finset.Icc 1 A).filter fun j => j % p = a % p).card : ℤ) =
      (A / p : ℕ) + if a ≤ A % p then 1 else 0 := by
  rw [single_class_count A p a hp ha hap]
  have hpq : (0 : ℚ) < p := by exact_mod_cast hp
  have haq : (0 : ℚ) < a := by exact_mod_cast ha
  have hapq : (a : ℚ) < p := by exact_mod_cast hap
  have hr0 : (0 : ℚ) ≤ (A % p : ℕ) := Nat.cast_nonneg _
  have hrp : ((A % p : ℕ) : ℚ) < p := by exact_mod_cast Nat.mod_lt A hp
  have hA : (A : ℚ) = (p : ℚ)*(A / p : ℕ) + (A % p : ℕ) := by
    exact_mod_cast (Nat.div_add_mod A p).symm
  have harg : ((A : ℚ) - a) / p =
      (A / p : ℕ) + (((A % p : ℕ) : ℚ) - a) / p := by
    rw [hA]
    field_simp
    ring
  rw [harg, Int.floor_natCast_add]
  by_cases h : a ≤ A % p
  · have hq : (a : ℚ) ≤ (A % p : ℕ) := by exact_mod_cast h
    have hz : ⌊(((A % p : ℕ) : ℚ) - a) / p⌋ = (0 : ℤ) := by
      apply Int.floor_eq_iff.mpr
      norm_num
      constructor
      · exact div_nonneg (sub_nonneg.mpr hq) hpq.le
      · rw [div_lt_iff₀ hpq]
        linarith
    simp [h, hz]

  · have hq : ((A % p : ℕ) : ℚ) < a := by exact_mod_cast (Nat.lt_of_not_ge h)
    have hz : ⌊(((A % p : ℕ) : ℚ) - a) / p⌋ = (-1 : ℤ) := by
      apply Int.floor_eq_iff.mpr
      norm_num
      constructor
      · rw [le_div_iff₀ hpq]
        linarith
      · exact div_neg_of_neg_of_pos (sub_neg.mpr hq) hpq
    simp [h, hz]

/-- Each nonzero residue belongs to exactly one ordinary square class.
Hence the total pole count omits exactly the multiples of p. -/
theorem poleCount_sum (A p : ℕ) (hp : 0 < p) (hodd : p % 2 = 1) :
    (∑ a ∈ Finset.Icc 1 ((p-1)/2), Zeta5Parameters.poleCount A p a) = A - A/p := by
  let m := (p-1)/2
  have hm : 2*m+1 = p := by dsimp [m]; omega
  let S := (Finset.Icc 1 A).filter fun j => j%p ≠ 0
  let f : ℕ → ℕ := fun j => if j%p ≤ m then j%p else p-j%p
  have hmap : (S : Set ℕ).MapsTo f (Finset.Icc 1 m) := by
    intro j hj
    have hj' : j%p ≠ 0 := (Finset.mem_filter.mp hj).2
    have hjp := Nat.mod_lt j hp
    simp only [Finset.mem_coe, Finset.mem_Icc]
    dsimp [f]
    split_ifs <;> omega
  have hfiber := Finset.card_eq_sum_card_fiberwise hmap
  have hclasses : ∀ a ∈ Finset.Icc 1 m,
      (S.filter fun j => f j = a) =
        (Finset.Icc 1 A).filter fun j =>
          j%p = a%p ∨ j%p = (p-a)%p := by
    intro a ha
    have ha' := Finset.mem_Icc.mp ha
    have hap : a < p := by omega
    have hb : p-a < p := by omega
    ext j
    have hjp := Nat.mod_lt j hp
    simp only [S, Finset.mem_filter, Finset.mem_Icc,
      Nat.mod_eq_of_lt hap, Nat.mod_eq_of_lt hb]
    dsimp [f]
    split_ifs <;> omega
  have hsum : (∑ a ∈ Finset.Icc 1 m, Zeta5Parameters.poleCount A p a) = S.card := by
    rw [hfiber]
    apply Finset.sum_congr rfl
    intro a ha
    rw [hclasses a ha]
    rfl
  have hinterval : Finset.Icc 1 A = Finset.Ioc 0 A := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hdvd : ((Finset.Icc 1 A).filter fun j => j%p = 0).card = A/p := by
    rw [hinterval]
    simp only [← Nat.dvd_iff_mod_eq_zero]
    exact Nat.Ioc_filter_dvd_card_eq_div A p
  have htotal := Finset.card_filter_add_card_filter_not
    (s := Finset.Icc 1 A) (fun j => j%p = 0)
  have hS : S.card = A-A/p := by
    change _ + S.card = _ at htotal
    rw [hdvd] at htotal
    have hcard : (Finset.Icc 1 A).card = A := by simp
    rw [hcard] at htotal
    omega
  exact hsum.trans hS
/-- A rational interval contains its length times the grid density, with
discrepancy strictly below one. This is the per-cell estimate used in (5.7). -/
theorem rational_grid_count_error (p l r : ℚ) (hp : 0 ≤ p) (hlr : l ≤ r) :
    |((Finset.Ico ⌈p*l⌉ ⌈p*r⌉).card : ℚ) - p*(r-l)| < 1 := by
  have hceil : ⌈p*l⌉ ≤ ⌈p*r⌉ :=
    Int.ceil_mono (mul_le_mul_of_nonneg_left hlr hp)
  have hc := Int.card_Ico_of_le ⌈p*l⌉ ⌈p*r⌉ hceil
  have hcq : ((Finset.Ico ⌈p*l⌉ ⌈p*r⌉).card : ℚ) =
      (⌈p*r⌉ : ℚ) - (⌈p*l⌉ : ℚ) := by exact_mod_cast hc
  rw [hcq, abs_lt]
  constructor <;>
    linarith [Int.le_ceil (p*l), Int.le_ceil (p*r),
      Int.ceil_lt_add_one (p*l), Int.ceil_lt_add_one (p*r)]

/-- A finite step function has a grid-sum error bounded independently of p.
The bound is the sum of the absolute cell heights, so O(M) cells with
O(M²) heights give an explicit O(M³) discrepancy. -/
theorem weighted_grid_error
    {ι : Type*} (S : Finset ι) (p : ℚ) (l r w : ι → ℚ)
    (hp : 0 ≤ p) (hlr : ∀ i ∈ S, l i ≤ r i) :
    |(∑ i ∈ S, w i * ((Finset.Ico ⌈p*l i⌉ ⌈p*r i⌉).card : ℚ)) -
      p * ∑ i ∈ S, w i * (r i-l i)| ≤ ∑ i ∈ S, |w i| := by
  have heq : (∑ i ∈ S, w i * ((Finset.Ico ⌈p*l i⌉ ⌈p*r i⌉).card : ℚ)) -
      p * ∑ i ∈ S, w i * (r i-l i) =
      ∑ i ∈ S, w i * (((Finset.Ico ⌈p*l i⌉ ⌈p*r i⌉).card : ℚ) -
        p*(r i-l i)) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro i hi
  rw [abs_mul]
  calc
    _ ≤ |w i| * 1 := mul_le_mul_of_nonneg_left
      (rational_grid_count_error p (l i) (r i) hp (hlr i hi)).le (abs_nonneg _)
    _ = _ := mul_one _

def baseConstant (T qN qK : ℚ) : ℚ :=
  T^2 - T*qK - 5*T - 9*qN^2 + 3*qN*qK + 15*qN

def highKCoefficient (T qN : ℚ) : ℚ := -T + 3*qN

def highNCoefficient (qN qK : ℚ) : ℚ := -18*qN + 3*qK + 6

/-- Expand a base-allocation row block using the two-valued pole counts.
Only the indicators of the high N-class, high K-class, and their overlap
remain. Thus three grid-count estimates suffice for the entire base sum. -/
theorem base_cost_indicator_expansion
    (T qN qK u v : ℚ) (hu : u^2 = u) :
    (T - 3*(qN+u)) * (T + 3*(qN+u) - (qK+v) - 5) =
      baseConstant T qN qK + v*highKCoefficient T qN +
        u*highNCoefficient qN qK + 3*u*v := by
  unfold baseConstant highKCoefficient highNCoefficient
  nlinarith [hu]

theorem sum_base_cost_indicator_expansion
    {ι : Type*} (S : Finset ι) (T qN qK : ℚ) (u v : ι → ℚ)
    (hu : ∀ i ∈ S, (u i)^2 = u i) :
    (∑ i ∈ S, (T-3*(qN+u i))*(T+3*(qN+u i)-(qK+v i)-5)) =
      (S.card : ℚ)*baseConstant T qN qK +
        (∑ i ∈ S, v i)*highKCoefficient T qN +
        (∑ i ∈ S, u i)*highNCoefficient qN qK +
        3*(∑ i ∈ S, u i*v i) := by
  calc
    _ = ∑ i ∈ S, (baseConstant T qN qK + v i*highKCoefficient T qN +
        u i*highNCoefficient qN qK + 3*u i*v i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact base_cost_indicator_expansion T qN qK _ _ (hu i hi)
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        ← Finset.sum_mul, mul_assoc, ← Finset.mul_sum]

/-- Integrating the same indicator expansion simply replaces class counts
by lengths. The finite-grid discrepancy therefore has this explicit bound. -/
theorem base_cost_grid_error
    (T qN qK m HN HK HB p lN lK lB : ℚ)
    (hm : |m-p/2| ≤ 1/2)
    (hN : |HN-p*lN| ≤ 1) (hK : |HK-p*lK| ≤ 1) (hB : |HB-p*lB| ≤ 1) :
    |(m*baseConstant T qN qK + HK*highKCoefficient T qN +
        HN*highNCoefficient qN qK + 3*HB) -
      p*(baseConstant T qN qK/2 + lK*highKCoefficient T qN +
        lN*highNCoefficient qN qK + 3*lB)| ≤
      |baseConstant T qN qK|/2 + |highKCoefficient T qN| +
        |highNCoefficient qN qK| + 3 := by
  have heq :
      (m*baseConstant T qN qK + HK*highKCoefficient T qN +
        HN*highNCoefficient qN qK + 3*HB) -
      p*(baseConstant T qN qK/2 + lK*highKCoefficient T qN +
        lN*highNCoefficient qN qK + 3*lB) =
      (m-p/2)*baseConstant T qN qK + (HK-p*lK)*highKCoefficient T qN +
        (HN-p*lN)*highNCoefficient qN qK + 3*(HB-p*lB) := by ring
  rw [heq]
  calc
    _ ≤ |(m-p/2)*baseConstant T qN qK| +
        |(HK-p*lK)*highKCoefficient T qN| +
        |(HN-p*lN)*highNCoefficient qN qK| + |3*(HB-p*lB)| := by
      have h1 := abs_add_le ((m-p/2)*baseConstant T qN qK)
        ((HK-p*lK)*highKCoefficient T qN)
      have h2 := abs_add_le ((m-p/2)*baseConstant T qN qK +
        (HK-p*lK)*highKCoefficient T qN) ((HN-p*lN)*highNCoefficient qN qK)
      have h3 := abs_add_le ((m-p/2)*baseConstant T qN qK +
        (HK-p*lK)*highKCoefficient T qN + (HN-p*lN)*highNCoefficient qN qK)
        (3*(HB-p*lB))
      linarith only [h1, h2, h3]
    _ ≤ _ := by
      simp only [abs_mul]
      norm_num
      linarith only [hB, mul_le_mul_of_nonneg_right hm (abs_nonneg (baseConstant T qN qK)),
        mul_le_mul_of_nonneg_right hK (abs_nonneg (highKCoefficient T qN)),
        mul_le_mul_of_nonneg_right hN (abs_nonneg (highNCoefficient qN qK))]

theorem poleCount_quotient_indicators (A p a : ℕ) (hp : 0 < p)
    (ha : 0 < a) (hhalf : 2*a < p) :
    (Zeta5Parameters.poleCount A p a : ℤ) =
      2*(A/p : ℕ) + (if a ≤ A%p then 1 else 0) +
        (if p-a ≤ A%p then 1 else 0) := by
  have hap : a < p := by omega
  have hb : 0 < p-a := by omega
  have hbp : p-a < p := by omega
  have hdis : Disjoint
      ((Finset.Icc 1 A).filter fun j => j%p = a%p)
      ((Finset.Icc 1 A).filter fun j => j%p = (p-a)%p) := by
    rw [Finset.disjoint_left]
    intro j hj₁ hj₂
    have h₁ := (Finset.mem_filter.mp hj₁).2
    have h₂ := (Finset.mem_filter.mp hj₂).2
    rw [Nat.mod_eq_of_lt hap] at h₁
    rw [Nat.mod_eq_of_lt hbp] at h₂
    omega
  unfold Zeta5Parameters.poleCount
  rw [Finset.filter_or, Finset.card_union_of_disjoint hdis, Nat.cast_add,
    single_class_count_quotient A p a hp ha hap,
    single_class_count_quotient A p (p-a) hp hb hbp]
  ring

/-- All literal ordinary block dimensions add to the required polynomial
space dimension; the prime hypotheses discharge the allocation conditions. -/
theorem actual_classDimension_sum (n M p : ℕ)
    (ha : Zeta5Parameters.Admissible n M) (hp : 3 ≤ p)
    (hodd : p % 2 = 1) (hinner : 3*p ≤ Zeta5Parameters.K n) :
    Zeta5Parameters.zeroDimension M +
      ∑ a ∈ Finset.Icc 1 ((p-1)/2), Zeta5Parameters.classDimension n M p a =
      Zeta5Parameters.h n := by
  apply Zeta5Parameters.classDimension_sum n M p hp
  · have := Zeta5Parameters.admissible_zeroDimension_small ha
    dsimp [Zeta5Parameters.h]
    omega
  · intro a ha'
    have ham := Finset.mem_Icc.mp ha'
    exact Zeta5Parameters.baseAllocation_ge_three_poleCount ha hp hinner
      (poleCount_mul_le _ _ _ (by omega) (by omega) (by omega))
  · exact poleCount_sum _ _ (by omega) hodd

/-- The high-value ordinary classes form one integer interval. -/
def highClasses (A p : ℕ) : Finset ℕ :=
  if A%p ≤ (p-1)/2 then Finset.Icc 1 (A%p)
  else Finset.Icc (p-A%p) ((p-1)/2)

def lowLevel (A p : ℕ) : ℕ :=
  2*(A/p) + if A%p ≤ (p-1)/2 then 0 else 1

theorem poleCount_highClasses (A p a : ℕ) (hp : 0 < p)
    (ha : 0 < a) (hhalf : 2*a < p) :
    Zeta5Parameters.poleCount A p a =
      lowLevel A p + if a ∈ highClasses A p then 1 else 0 := by
  have h := poleCount_quotient_indicators A p a hp ha hhalf
  have hr := Nat.mod_lt A hp
  have ham : a ≤ (p-1)/2 := by omega
  unfold highClasses lowLevel
  split_ifs with hlo hahi hahi
  · simp only [Finset.mem_Icc] at hahi
    have hpa : ¬p-a ≤ A%p := by omega
    simp only [hahi.2, ↓reduceIte, hpa] at h
    omega
  · have hn : ¬a ≤ A%p := by
      simp only [Finset.mem_Icc] at hahi
      omega
    have hpa : ¬p-a ≤ A%p := by omega
    simp only [hn, hpa, ↓reduceIte] at h
    omega
  · simp only [Finset.mem_Icc] at hahi
    have ha' : a ≤ A%p := by omega
    have hpa : p-a ≤ A%p := by omega
    simp only [ha', hpa, ↓reduceIte] at h
    omega
  · have ha' : a ≤ A%p := by omega
    have hpa : ¬p-a ≤ A%p := by
      simp only [Finset.mem_Icc] at hahi
      omega
    simp only [ha', hpa, ↓reduceIte] at h
    omega

theorem highClasses_subset (A p : ℕ) (hp : 0 < p) :
    highClasses A p ⊆ Finset.Icc 1 ((p-1)/2) := by
  intro a ha
  have hr := Nat.mod_lt A hp
  unfold highClasses at ha
  split_ifs at ha with hlo <;> simp only [Finset.mem_Icc] at * <;> omega

/-- The measure of a high-class interval multiplied by p. -/
def highMass (A p : ℕ) : ℚ :=
  if A%p ≤ (p-1)/2 then ((A%p : ℕ) : ℚ) else ((A%p : ℕ) : ℚ) - p/2

theorem highClasses_card (A p : ℕ) (hp : 0 < p) (hodd : p%2=1) :
    (highClasses A p).card =
      if A%p ≤ (p-1)/2 then A%p else A%p-(p-1)/2 := by
  have hr := Nat.mod_lt A hp
  have he : 2*((p-1)/2)+1=p := by omega
  unfold highClasses
  split_ifs <;> rw [Nat.card_Icc] <;> omega

theorem highClasses_card_error (A p : ℕ) (hp : 0 < p) (hodd : p%2=1) :
    |((highClasses A p).card : ℚ)-highMass A p| ≤ 1/2 := by
  rw [highClasses_card A p hp hodd]
  unfold highMass
  have he : 2*((p-1)/2)+1=p := by omega
  have heq : 2*(((p-1)/2 : ℕ) : ℚ)+1=p := by exact_mod_cast he
  split_ifs with hlo
  · norm_num
  · rw [Nat.cast_sub (by omega)]
    rw [abs_of_nonneg (by linarith : 0 ≤ ((A%p : ℕ) : ℚ)-((p-1)/2 : ℕ)-(((A%p : ℕ) : ℚ)-p/2))]
    linarith

/-- The measure of an intersection of two high intervals, multiplied by p. -/
def overlapMass (A B p : ℕ) : ℚ :=
  if A%p ≤ (p-1)/2 then
    if B%p ≤ (p-1)/2 then min ((A%p : ℕ) : ℚ) ((B%p : ℕ) : ℚ)
    else max 0 (((A%p : ℕ) : ℚ)+((B%p : ℕ) : ℚ)-p)
  else
    if B%p ≤ (p-1)/2 then max 0 (((A%p : ℕ) : ℚ)+((B%p : ℕ) : ℚ)-p)
    else min ((A%p : ℕ) : ℚ) ((B%p : ℕ) : ℚ)-p/2

theorem highClasses_inter_card (A B p : ℕ) (hp : 0 < p) (hodd : p%2=1) :
    ((highClasses A p) ∩ (highClasses B p)).card =
      if A%p ≤ (p-1)/2 then
        if B%p ≤ (p-1)/2 then min (A%p) (B%p)
        else A%p+1-(p-B%p)
      else
        if B%p ≤ (p-1)/2 then B%p+1-(p-A%p)
        else min (A%p) (B%p)-(p-1)/2 := by
  have hrA := Nat.mod_lt A hp
  have hrB := Nat.mod_lt B hp
  have he : 2*((p-1)/2)+1=p := by omega
  unfold highClasses
  split_ifs with hA hB hB
  · have hi : Finset.Icc 1 (A%p) ∩ Finset.Icc 1 (B%p) =
        Finset.Icc 1 (min (A%p) (B%p)) := by ext a; simp; omega
    rw [hi, Nat.card_Icc]
    omega
  · have hi : Finset.Icc 1 (A%p) ∩ Finset.Icc (p-B%p) ((p-1)/2) =
        Finset.Icc (p-B%p) (A%p) := by ext a; simp; omega
    rw [hi, Nat.card_Icc]
  · have hi : Finset.Icc (p-A%p) ((p-1)/2) ∩ Finset.Icc 1 (B%p) =
        Finset.Icc (p-A%p) (B%p) := by ext a; simp; omega
    rw [hi, Nat.card_Icc]
  · have hi : Finset.Icc (p-A%p) ((p-1)/2) ∩ Finset.Icc (p-B%p) ((p-1)/2) =
        Finset.Icc (p-min (A%p) (B%p)) ((p-1)/2) := by ext a; simp; omega
    rw [hi, Nat.card_Icc]
    omega

/-- Endpoint inclusion costs at most one ordinary residue class. -/
theorem nat_interval_count_error (u v : ℕ) :
    |((v+1-u : ℕ) : ℚ)-max 0 ((v : ℚ)-u)| ≤ 1 := by
  by_cases huv : u ≤ v
  · rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one,
      max_eq_right (sub_nonneg.mpr (by exact_mod_cast huv : (u:ℚ) ≤ v))]
    have he : (v:ℚ)+1-u-((v:ℚ)-u)=1 := by ring
    rw [he]
    norm_num
  · have hnat : v+1-u=0 := by omega
    have hq : (v:ℚ)-u ≤ 0 := by
      have hh : (v:ℚ) ≤ u := by exact_mod_cast (Nat.le_of_lt (by omega : v<u))
      linarith
    rw [hnat, max_eq_left hq]
    norm_num

theorem highClasses_inter_card_error (A B p : ℕ) (hp : 0 < p) (hodd : p%2=1) :
    |(((highClasses A p) ∩ (highClasses B p)).card : ℚ)-overlapMass A B p| ≤ 1 := by
  rw [highClasses_inter_card A B p hp hodd]
  unfold overlapMass
  have hrA := Nat.mod_lt A hp
  have hrB := Nat.mod_lt B hp
  have he : 2*((p-1)/2)+1=p := by omega
  have heq : 2*(((p-1)/2 : ℕ) : ℚ)+1=p := by exact_mod_cast he
  split_ifs with hA hB hB
  · rw [Nat.cast_min]
    norm_num
  · have ht := nat_interval_count_error (p-B%p) (A%p)
    rw [Nat.cast_sub (Nat.le_of_lt hrB)] at ht
    convert ht using 1 <;> congr 2 <;> ring
  · have ht := nat_interval_count_error (p-A%p) (B%p)
    rw [Nat.cast_sub (Nat.le_of_lt hrA)] at ht
    convert ht using 1 <;> congr 2 <;> ring
  · rw [Nat.cast_sub (by omega), Nat.cast_min]
    have hEq : min ((A%p : ℕ) : ℚ) ((B%p : ℕ) : ℚ)-((p-1)/2 : ℕ)-
        (min ((A%p : ℕ) : ℚ) ((B%p : ℕ) : ℚ)-p/2)=1/2 := by linarith
    rw [hEq]
    norm_num

#print axioms poleCount_eq_floor
#print axioms actual_poleCount_two_values
#print axioms weighted_grid_error
#print axioms base_cost_grid_error

end Zeta5InnerAsymptotics
