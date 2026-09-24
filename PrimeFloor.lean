import PrimeSums
import FloorIndicators

noncomputable section
open Filter Asymptotics MeasureTheory
open scoped Topology BigOperators
namespace Zeta5PrimeSums
set_option maxHeartbeats 1000000

/-- Upper prime cutoff for the j-th indicator of floor(c*x/p). -/
def floorPrimeCut (a b c : ℝ) (j : ℕ) : ℝ :=
  max (1/b) (min (1/a) (c/j))

def floorPrimeConstant (a b c : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 ⌊c*b⌋₊, (floorPrimeCut a b c j-1/b)

lemma floorPrimeCut_mul (a b c x : ℝ) (j : ℕ) (hx : 0≤x) :
    floorPrimeCut a b c j*x = max (x/b) (min (x/a) (c*x/j)) := by
  unfold floorPrimeCut
  rw [max_mul_of_nonneg _ _ hx, min_mul_of_nonneg _ _ hx]
  apply congrArg₂ max
  · ring
  · apply congrArg₂ min <;> ring

lemma floor_prime_indicator_set (a b c x : ℝ) (j : ℕ)
    (ha : 0<a) (hb : 0<b) (hx : 0<x) (hj : 0<j) :
    (((Finset.Ioc ⌊x/b⌋₊ ⌊x/a⌋₊).filter Nat.Prime).filter
      (fun p : ℕ => (j:ℝ)≤c*(x/p))) =
      (Finset.Ioc ⌊x/b⌋₊ ⌊floorPrimeCut a b c j*x⌋₊).filter Nat.Prime := by
  ext p
  by_cases hp : p.Prime
  · have hp0 : (0:ℝ)<p := by exact_mod_cast hp.pos
    have hj0 : (0:ℝ)<j := by exact_mod_cast hj
    have hc0 : 0≤floorPrimeCut a b c j*x := by
      exact mul_nonneg ((one_div_pos.mpr hb).le.trans (le_max_left _ _)) hx.le
    have he : (j:ℝ)≤c*(x/p) ↔ (p:ℝ)≤c*x/j := by
      rw [←mul_div_assoc, le_div_iff₀ hp0, le_div_iff₀ hj0]
      rw [mul_comm (j:ℝ) (p:ℝ)]
    simp only [Finset.mem_filter, Finset.mem_Ioc, hp, and_true,
      Nat.floor_lt (div_nonneg hx.le hb.le),
      Nat.le_floor_iff (div_nonneg hx.le ha.le), Nat.le_floor_iff hc0]
    rw [floorPrimeCut_mul a b c x j hx.le, he, le_max_iff, le_min_iff]
    constructor
    · rintro ⟨⟨hlo,hhi⟩,hcut⟩
      exact ⟨hlo,Or.inr ⟨hhi,hcut⟩⟩
    · rintro ⟨hlo,hupper⟩
      rcases hupper with hbad | ⟨hhi,hcut⟩
      · linarith
      · exact ⟨⟨hlo,hhi⟩,hcut⟩
  · simp [hp]

lemma floor_prime_sum_eq_theta (a b c x : ℝ)
    (ha : 0<a) (hab : a≤b) (hc : 0≤c) (hx : 0<x) :
    (∑ p ∈ Finset.Ioc ⌊x/b⌋₊ ⌊x/a⌋₊ with p.Prime,
      x*(⌊c*(x/p)⌋:ℝ)*Real.log p) =
      x*∑ j ∈ Finset.Icc 1 ⌊c*b⌋₊,
        (Chebyshev.theta (floorPrimeCut a b c j*x)-Chebyshev.theta (x/b)) := by
  have hb : 0<b := ha.trans_le hab
  have hexpand : (∑ p ∈ Finset.Ioc ⌊x/b⌋₊ ⌊x/a⌋₊ with p.Prime,
      x*(⌊c*(x/p)⌋:ℝ)*Real.log p) =
      ∑ p ∈ Finset.Ioc ⌊x/b⌋₊ ⌊x/a⌋₊ with p.Prime,
        ∑ j ∈ Finset.Icc 1 ⌊c*b⌋₊, if (j:ℝ)≤c*(x/p) then x*Real.log p else 0 := by
    apply Finset.sum_congr rfl
    intro p hp
    have hp0 : (0:ℝ)<p := by exact_mod_cast (Finset.mem_filter.mp hp).2.pos
    have hlo : x/b<(p:ℝ) := (Nat.floor_lt (div_nonneg hx.le hb.le)).mp
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
    have hxp : x/(p:ℝ)≤b := (div_le_iff₀ hp0).mpr
      (by have hh := (div_lt_iff₀ hb).mp hlo; nlinarith)
    rw [Zeta5RealKernel.floor_scaled_finite_indicators c (x/p) b hc (by positivity) hxp,
      Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> simp
  rw [hexpand, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj0 : 0<j := (Finset.mem_Icc.mp hj).1
  rw [←Finset.sum_filter, floor_prime_indicator_set a b c x j ha hb hx hj0]
  have hh := affine_prime_sum_eq_endpoints x 0 (x/b) (floorPrimeCut a b c j*x)
    (by rw [floorPrimeCut_mul a b c x j hx.le]; exact le_max_left _ _)
  simpa only [zero_mul, add_zero, zero_add] using hh

/-- Exact PNT limit for a floor contribution on the original prime interval.
All jumps are absorbed by weak upper prime cutoffs. -/
theorem floor_prime_sum_tendsto (a b c : ℝ)
    (ha : 0<a) (hab : a≤b) (hc : 0≤c) :
    Tendsto (fun x : ℝ =>
      (∑ p ∈ Finset.Ioc ⌊x/b⌋₊ ⌊x/a⌋₊ with p.Prime,
        x*(⌊c*(x/p)⌋:ℝ)*Real.log p)/x^2)
      atTop (𝓝 (floorPrimeConstant a b c)) := by
  have hb : 0<b := ha.trans_le hab
  have hlim := tendsto_finsetSum (Finset.Icc 1 ⌊c*b⌋₊) (fun j hj =>
    interval_asymptotic_ratio chebyshev_asymptotic (one_div_pos.mpr hb)
      ((one_div_pos.mpr hb).trans_le (le_max_left (1/b) (min (1/a) (c/j)))))
  change Tendsto (fun x : ℝ =>
    ∑ j ∈ Finset.Icc 1 ⌊c*b⌋₊,
      (Chebyshev.theta (floorPrimeCut a b c j*x)-Chebyshev.theta ((1/b)*x))/x)
    atTop (𝓝 (floorPrimeConstant a b c)) at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  rw [floor_prime_sum_eq_theta a b c x ha hab hc hx]
  rw [←Finset.sum_div]
  have he : (1/b)*x=x/b := by ring
  rw [he]
  field_simp
  simp only [mul_comm]

#print axioms floor_prime_sum_tendsto
end Zeta5PrimeSums
