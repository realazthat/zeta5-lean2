import InnerBaseKernel
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace Zeta5InnerAsymptotics
open Zeta5Parameters

private theorem sum_twice_weights (L n k : ℕ) :
    (∑ i ∈ Finset.range L, (2*(i:ℤ)+6*(n:ℤ)-(k:ℤ)-4) : ℤ) =
      (L:ℤ)*((L:ℤ)+6*(n:ℤ)-(k:ℤ)-5) := by
  induction L with
  | zero => simp
  | succ L ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- Literal ordinary block weights give the quadratic cost, including
its extra row. -/
theorem actual_ordinary_block_cost (n M p a : ℕ)
    (hbase : 3*poleCount (N n) p a ≤ baseAllocation n M p) :
    ((∑ i ∈ Finset.range (classDimension n M p a),
      twiceOrdinaryWeight n p a i : ℤ) : ℚ) =
      ((baseAllocation n M p:ℚ)-3*(poleCount (N n) p a:ℚ)) *
      ((baseAllocation n M p:ℚ)+3*(poleCount (N n) p a:ℚ)-
        (poleCount (K n) p a:ℚ)-5) +
      (extra n M p a:ℚ) * (2*(baseAllocation n M p:ℚ)-
        (poleCount (K n) p a:ℚ)-4) := by
  unfold twiceOrdinaryWeight
  rw [sum_twice_weights]
  push_cast
  have hd : (classDimension n M p a:ℚ) =
      (baseAllocation n M p:ℚ)-3*(poleCount (N n) p a:ℚ)+(extra n M p a:ℚ) := by
    unfold classDimension
    rw [Nat.cast_add, Nat.cast_sub hbase, Nat.cast_mul, Nat.cast_ofNat]
  rw [hd]
  unfold extra
  split_ifs <;> norm_num <;> ring_nf <;> simp

theorem actual_ordinary_block_lower (n M p a : ℕ) (hp : 0 < p)
    (ha : 0 < a) (hhalf : 2*a < p)
    (hbase : 3*poleCount (N n) p a ≤ baseAllocation n M p) :
    ((baseAllocation n M p:ℚ)-3*(poleCount (N n) p a:ℚ)) *
      ((baseAllocation n M p:ℚ)+3*(poleCount (N n) p a:ℚ)-
        (poleCount (K n) p a:ℚ)-5) +
      (extra n M p a:ℚ) * (2*(baseAllocation n M p:ℚ)-
        (lowLevel (K n) p:ℚ)-5) ≤
    ((∑ i ∈ Finset.range (classDimension n M p a),
      twiceOrdinaryWeight n p a i : ℤ) : ℚ) := by
  rw [actual_ordinary_block_cost n M p a hbase]
  have hk : poleCount (K n) p a ≤ lowLevel (K n) p+1 := by
    rw [poleCount_highClasses _ _ _ hp ha hhalf]
    split_ifs <;> omega
  have hkq : (poleCount (K n) p a:ℚ) ≤ (lowLevel (K n) p:ℚ)+1 := by exact_mod_cast hk
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  linarith

private theorem fold_min_lower {ι : Type*} (l : List ι) (f : ι → ℤ)
    (w c : ℤ) (hw : c ≤ w) (hf : ∀ a ∈ l, c ≤ f a) :
    c ≤ l.foldl (fun w a => min w (f a)) w := by
  induction l generalizing w with
  | nil => exact hw
  | cons a l ih =>
    exact ih (min w (f a)) (le_min hw (hf a (by simp)))
      (fun b hb => hf b (by simp [hb]))

/-- The zero block is uniformly bounded below for K/p ≤ M. -/
theorem actual_zero_weight_lower (n M p i : ℕ) (hp : 0 < p)
    (hcutoff : K n ≤ M*p) :
    -((2*M+5:ℕ):ℤ) ≤ twiceZeroWeight n M p i := by
  have hdiv : K n/p ≤ M := by
    have := Nat.div_mul_le_self (K n) p
    nlinarith
  unfold twiceZeroWeight
  apply fold_min_lower
  · have hdivz : (K n/p:ℤ) ≤ M := by exact_mod_cast hdiv
    have hn : (0:ℤ) ≤ (N n:ℤ)/(p:ℤ) := Int.ediv_nonneg (by positivity) (by positivity)
    have hi : (0:ℤ) ≤ i := by positivity
    push_cast
    linarith
  · intro a ha
    have ham := Finset.mem_Icc.mp ((ordinaryClasses_mem p a).mp ha)
    have hc := poleCount_mul_le (K n) p a hp (by omega) (by omega)
    have hk : poleCount (K n) p a ≤ 2*M+1 := by nlinarith
    have hkz : (poleCount (K n) p a:ℤ) ≤ 2*(M:ℤ)+1 := by exact_mod_cast hk
    have hdim : (0:ℤ) ≤ classDimension n M p a := by positivity
    have hn : (0:ℤ) ≤ poleCount (N n) p a := by positivity
    push_cast
    linarith

def baseError (A B p : ℕ) (T : ℚ) : ℚ :=
  |baseConstant T (lowLevel A p) (lowLevel B p)|/2 +
  |highKCoefficient T (lowLevel A p)| +
  |highNCoefficient (lowLevel A p) (lowLevel B p)|+3

/-- A sufficient lower bound on the paper's literal doubled row exponent.
The only relaxation is replacing each allocated extra row by the cheaper
of the two possible ordinary row costs. -/
theorem actual_innerExponent_lower (n M p : ℕ) (had : Admissible n M)
    (hp : 3 ≤ p) (hodd : p%2=1) (hinner : 3*p ≤ K n) (hcutoff : K n ≤ M*p) :
    baseMass (N n) (K n) p (baseAllocation n M p) -
      baseError (N n) (K n) p (baseAllocation n M p) +
      (extraCount n M p:ℚ) * (2*(baseAllocation n M p:ℚ)-
        (lowLevel (K n) p:ℚ)-5) -
      (zeroDimension M:ℚ)*(2*(M:ℚ)+5) ≤ (innerExponent n M p:ℚ) := by
  have hb : ∀ a ∈ Finset.Icc 1 ((p-1)/2),
      3*poleCount (N n) p a ≤ baseAllocation n M p := by
    intro a ha
    have ham := Finset.mem_Icc.mp ha
    exact baseAllocation_ge_three_poleCount had hp hinner
      (poleCount_mul_le _ _ _ (by omega) (by omega) (by omega))
  have hord := Finset.sum_le_sum (s := Finset.Icc 1 ((p-1)/2))
    (fun a ha => actual_ordinary_block_lower n M p a (by omega)
      (by have := Finset.mem_Icc.mp ha; omega)
      (by have := Finset.mem_Icc.mp ha; omega) (hb a ha))
  rw [Finset.sum_add_distrib, ← Finset.sum_mul] at hord
  have hex : (∑ a ∈ Finset.Icc 1 ((p-1)/2), (extra n M p a:ℚ)) = extraCount n M p := by
    exact_mod_cast extra_sum n M p hp
  rw [hex] at hord
  have hzero := Finset.sum_le_sum (s := Finset.range (zeroDimension M))
    (fun i hi => actual_zero_weight_lower n M p i (by omega) hcutoff)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hzero
  have hzeroq : -(zeroDimension M:ℚ)*(2*(M:ℚ)+5) ≤
      ((∑ i ∈ Finset.range (zeroDimension M), twiceZeroWeight n M p i : ℤ):ℚ) := by
    exact_mod_cast hzero
  have hbase := actual_base_cost_error (N n) (K n) p (baseAllocation n M p) (by omega) hodd
  change |_ - _| ≤ baseError _ _ _ _ at hbase
  have hbasel := (abs_le.mp hbase).1
  unfold innerExponent
  push_cast
  push_cast at hzeroq hord
  linarith

#print axioms actual_innerExponent_lower
end Zeta5InnerAsymptotics
