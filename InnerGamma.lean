import InnerAllocationLimit
import Mathlib.Tactic

noncomputable section
namespace Zeta5InnerAsymptotics

def baseIntegral (T qN qK lN lK lB : ℚ) : ℚ :=
  baseConstant T qN qK/2 + lK*highKCoefficient T qN +
    lN*highNCoefficient qN qK + 3*lB

def extraCost (T qK : ℚ) : ℚ := 2*T-qK-5

def gammaAtAllocation (y T qN qK lN lK lB : ℚ) : ℚ :=
  baseIntegral T qN qK lN lK lB + (y-T)/2*extraCost T qK +
    max ((y-T)/2-lK) 0

/-- Stability at an allocation transition, with a uniform loss of one
half per residue modulus. This weaker estimate avoids any asymptotic
assumption about the greedily ordered extra rows. -/
theorem gamma_allocation_lower (y T t s qN qK lN lK lB : ℚ)
    (ht : t=T ∨ t+1=T) (hTy : T≤y) (hyT : y<T+1)
    (hs : s≤1/2) (hlK : 0≤lK) (hd : 0≤y-t-2*s) :
    gammaAtAllocation y T qN qK lN lK lB ≤
      baseIntegral t qN qK lN lK lB+s*extraCost t qK+1/2+
        (y-t-2*s)*(|extraCost t qK|/2+2) := by
  have hprod : (y-t-2*s)/2*extraCost t qK ≤
      (y-t-2*s)/2*|extraCost t qK| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) (by linarith)
  rcases ht with ht | ht
  · subst t
    have hmax : max ((y-T)/2-lK) 0 ≤ 1/2 := by
      apply max_le <;> linarith
    unfold gammaAtAllocation
    have he : (y-T)/2*extraCost T qK-s*extraCost T qK =
        (y-T-2*s)/2*extraCost T qK := by ring
    nlinarith only [hprod,hmax,hd,he]
  · have hmax : max ((y-T)/2-lK) 0 ≤ (y-T)/2 := by
      apply max_le <;> linarith
    have hsmall : y-T ≤ y-t-2*s := by linarith
    have he : gammaAtAllocation y T qN qK lN lK lB -
        (baseIntegral t qN qK lN lK lB+s*extraCost t qK) =
        1/2-lK+(y-t-2*s)/2*extraCost t qK+(y-T)+max ((y-T)/2-lK) 0 := by
      rw [← ht]
      unfold gammaAtAllocation baseIntegral baseConstant highKCoefficient highNCoefficient extraCost
      ring
    nlinarith only [he,hmax,hsmall,hprod,hlK,hd]

/-- A budget discrepancy smaller than one forces only the two adjacent
integer allocations that occur in the transition estimate. -/
theorem adjacent_allocation_of_error (y : ℚ) (t : ℕ) (s δ : ℚ)
    (hs0 : 0≤s) (hs : s<1/2) (hd0 : 0≤δ) (hd : δ<1)
    (he : y-(t:ℚ)-2*s=δ) :
    (t:ℤ)=⌊y⌋ ∨ (t:ℤ)+1=⌊y⌋ := by
  have ht : (t:ℤ) ≤ ⌊y⌋ := Int.le_floor.mpr (by push_cast; linarith)
  have hf : ⌊y⌋ < (t:ℤ)+2 := by
    apply Int.floor_lt.mpr
    push_cast
    linarith
  omega

/-- Length of the overlap of the two high-value floor-function intervals. -/
def overlapLimit (u v : ℚ) : ℚ :=
  if Int.fract u < 1/2 then
    if Int.fract v < 1/2 then min (Int.fract u) (Int.fract v)
    else max 0 (Int.fract u+Int.fract v-1)
  else
    if Int.fract v < 1/2 then max 0 (Int.fract u+Int.fract v-1)
    else min (Int.fract u) (Int.fract v)-1/2

theorem phase_half_iff (A p : ℕ) (hp : 0<p) :
    A%p ≤ (p-1)/2 ↔ ((A%p:ℕ):ℚ)/p < 1/2 := by
  have hpq : (0:ℚ)<p := by exact_mod_cast hp
  rw [div_lt_iff₀ hpq]
  constructor
  · intro h
    have h' : 2*(A%p)<p := by omega
    have hq : 2*((A%p:ℕ):ℚ)<p := by exact_mod_cast h'
    linarith
  · intro h
    have hq : 2*((A%p:ℕ):ℚ)<p := by linarith
    have h' : 2*(A%p)<p := by exact_mod_cast hq
    omega

theorem highMass_div (A p : ℕ) (hp : 0<p) :
    highMass A p/(p:ℚ) = Int.fract (2*(A:ℚ)/p)/2 := by
  have hpq : (p:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hp)
  have h := highMass_identity A p
  unfold Int.fract
  rw [← lowLevel_eq_floor A p hp, Int.cast_natCast]
  field_simp
  nlinarith

theorem overlapMass_div (A B p : ℕ) (hp : 0<p) :
    overlapMass A B p/(p:ℚ) = overlapLimit ((A:ℚ)/p) ((B:ℚ)/p) := by
  have hpq : (0:ℚ)<p := by exact_mod_cast hp
  unfold overlapMass overlapLimit
  simp only [Int.fract_div_natCast_eq_div_natCast_mod]
  simp only [← phase_half_iff A p hp, ← phase_half_iff B p hp]
  split_ifs with hA hB hB
  · exact (min_div_div_right hpq.le _ _).symm
  · rw [← max_div_div_right hpq.le, zero_div]
    congr 1
    field_simp
  · rw [← max_div_div_right hpq.le, zero_div]
    congr 1
    field_simp
  · rw [sub_div, ← min_div_div_right hpq.le]
    congr 1
    field_simp

/-- The paper's inner limiting function expressed through the three
interval lengths; this finite formula removes the integral in (5.4). -/
def gamma (x : ℚ) : ℚ :=
  gammaAtAllocation (23/10*x) ⌊23/10*x⌋ ⌊3/20*x⌋ ⌊2*x⌋
    (Int.fract (3/20*x)/2) (Int.fract (2*x)/2) (overlapLimit (3/40*x) x)

#print axioms gamma_allocation_lower
end Zeta5InnerAsymptotics
