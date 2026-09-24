import InnerWeights
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace Zeta5InnerAsymptotics
open Zeta5Parameters

/-- An elementary uniform bound for the actual base allocation. -/
theorem actual_baseAllocation_le (n M p : ℕ) (hp : 3 ≤ p) (hodd : p%2=1)
    (hcutoff : K n ≤ M*p) : baseAllocation n M p ≤ 6*M := by
  have hm : p ≤ 3*((p-1)/2) := by omega
  have ht := base_extra_budget n M p
  have hb : allocationBudget n M p ≤ 2*K n := by
    calc
      allocationBudget n M p ≤ h n+3*N n :=
        Nat.add_le_add (Nat.sub_le _ _) (Nat.mul_le_mul_left 3 (Nat.sub_le _ _))
      _ ≤ 2*K n := by dsimp [h,N,K]; omega
  have hmT := Nat.mul_le_mul_left (baseAllocation n M p) hm
  nlinarith

/-- Multiplying the allocation equation by two exhibits its bounded
error from the limiting allocation 2Hx. -/
theorem actual_allocation_identity (n M p : ℕ) (ha : Admissible n M)
    (hodd : p%2=1) :
    (p:ℚ)*(baseAllocation n M p:ℚ)+2*(extraCount n M p:ℚ) =
      2*((h n:ℚ)+3*(N n:ℚ))-2*(zeroDimension M:ℚ)-
        6*((N n/p:ℕ):ℚ)+(baseAllocation n M p:ℚ) := by
  have hz := admissible_zeroDimension_small ha
  have hzh : zeroDimension M ≤ h n := by dsimp [h]; omega
  have hdiv : N n/p ≤ N n := Nat.div_le_self _ _
  have hb := base_extra_budget n M p
  have hbq : ((((p-1)/2:ℕ):ℚ))*(baseAllocation n M p:ℚ)+
      (extraCount n M p:ℚ) =
      (h n:ℚ)-(zeroDimension M:ℚ)+3*((N n:ℚ)-((N n/p:ℕ):ℚ)) := by
    have hc := congrArg (fun z:ℕ => (z:ℚ)) hb
    simpa only [Nat.cast_add, Nat.cast_mul, allocationBudget,
      Nat.cast_sub hzh, Nat.cast_sub hdiv, Nat.cast_ofNat] using hc
  have he : 2*((p-1)/2)+1=p := by omega
  have heq : 2*((((p-1)/2:ℕ):ℚ))+1=p := by exact_mod_cast he
  nlinarith

theorem lowLevel_le (A p M : ℕ) (hp : 0 < p) (hcutoff : A ≤ M*p) :
    lowLevel A p ≤ 2*M+1 := by
  have hdiv : A/p ≤ M := by
    have := Nat.div_mul_le_self A p
    nlinarith
  unfold lowLevel
  split_ifs <;> omega

theorem lowLevel_eq_floor (A p : ℕ) (hp : 0 < p) :
    (lowLevel A p:ℤ) = ⌊2*(A:ℚ)/p⌋ := by
  have hpq : (0:ℚ) < p := by exact_mod_cast hp
  have hrem := Nat.mod_lt A hp
  have hdec : (A:ℚ) = (p:ℚ)*((A/p:ℕ):ℚ)+((A%p:ℕ):ℚ) := by
    exact_mod_cast (Nat.div_add_mod A p).symm
  unfold lowLevel
  split_ifs with hsmall
  · have hrq : 2*((A%p:ℕ):ℚ) < p := by exact_mod_cast (show 2*(A%p)<p by omega)
    symm
    apply Int.floor_eq_iff.mpr
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero,
      Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_zero, Int.cast_natCast]
    constructor
    · rw [le_div_iff₀ hpq]
      nlinarith [Nat.cast_nonneg (α:=ℚ) (A%p)]
    · rw [div_lt_iff₀ hpq]
      nlinarith
  · have hrq : (p:ℚ) ≤ 2*((A%p:ℕ):ℚ) := by exact_mod_cast (show p≤2*(A%p) by omega)
    have hrq' : ((A%p:ℕ):ℚ)<p := by exact_mod_cast hrem
    symm
    apply Int.floor_eq_iff.mpr
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero,
      Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_zero, Int.cast_natCast]
    constructor
    · rw [le_div_iff₀ hpq]
      nlinarith
    · rw [div_lt_iff₀ hpq]
      nlinarith

theorem highMass_identity (A p : ℕ) :
    2*highMass A p = 2*(A:ℚ)-(p:ℚ)*(lowLevel A p:ℚ) := by
  have hdec : (A:ℚ) = (p:ℚ)*((A/p:ℕ):ℚ)+((A%p:ℕ):ℚ) := by
    exact_mod_cast (Nat.div_add_mod A p).symm
  unfold highMass lowLevel
  split_ifs <;> push_cast <;> nlinarith

/-- The allocation budget is below its continuous value by a bounded
nonnegative quantity, independent of n and p for fixed M. -/
theorem actual_allocation_error (n M p : ℕ) (ha : Admissible n M)
    (hp : 3 ≤ p) (hodd : p%2=1) (hcutoff : K n ≤ M*p) :
    0 ≤ 2*((h n:ℚ)+3*(N n:ℚ))-
      ((p:ℚ)*(baseAllocation n M p:ℚ)+2*(extraCount n M p:ℚ)) ∧
    2*((h n:ℚ)+3*(N n:ℚ))-
      ((p:ℚ)*(baseAllocation n M p:ℚ)+2*(extraCount n M p:ℚ)) ≤
      14*(M:ℚ)+20 := by
  rw [actual_allocation_identity n M p ha hodd]
  have ht := actual_baseAllocation_le n M p hp hodd hcutoff
  have htq : (baseAllocation n M p:ℚ) ≤ 6*(M:ℚ) := by exact_mod_cast ht
  have hNK : N n ≤ K n := by dsimp [N,K]; omega
  have hdiv : N n/p ≤ M := by
    have := Nat.div_mul_le_self (N n) p
    nlinarith
  have hdivq : ((N n/p:ℕ):ℚ) ≤ M := by exact_mod_cast hdiv
  have hnq : (0:ℚ) ≤ ((N n/p:ℕ):ℚ) := by positivity
  have ht0 : (0:ℚ) ≤ baseAllocation n M p := by positivity
  unfold zeroDimension
  push_cast
  constructor <;> linarith

#print axioms actual_allocation_error
#print axioms lowLevel_eq_floor
end Zeta5InnerAsymptotics
