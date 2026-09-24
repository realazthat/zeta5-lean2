import InnerUniform
import Mathlib.Tactic

noncomputable section
namespace Zeta5InnerAsymptotics
open Zeta5Parameters

private theorem baseError_bound_aux (S T a b : ℚ) (hS : 1≤S)
    (hT0 : 0≤T) (hT : T≤6*S) (ha0 : 0≤a) (ha : a≤2*S) (hb0 : 0≤b) (hb : b≤2*S) :
    |baseConstant T a b|/2+|highKCoefficient T a|+|highNCoefficient a b|+3 ≤ 107*S^2 := by
  have hS0 : 0≤S := by linarith
  have hT2 : T^2≤36*S^2 := by nlinarith [mul_self_le_mul_self hT0 hT]
  have ha2 : a^2≤4*S^2 := by nlinarith [mul_self_le_mul_self ha0 ha]
  have hTb : T*b≤12*S^2 := by nlinarith [mul_le_mul hT hb hb0 (by linarith : 0≤6*S)]
  have hab : a*b≤4*S^2 := by nlinarith [mul_le_mul ha hb hb0 (by linarith : 0≤2*S)]
  have hSS : S≤S^2 := by nlinarith
  have hc : |baseConstant T a b|≤100*S^2 := by
    rw [abs_le]
    unfold baseConstant
    constructor <;> nlinarith [sq_nonneg T,sq_nonneg a,mul_nonneg hT0 hb0,mul_nonneg ha0 hb0]
  have hk : |highKCoefficient T a|≤12*S := by
    rw [abs_le]
    unfold highKCoefficient
    constructor <;> linarith
  have hn : |highNCoefficient a b|≤42*S := by
    rw [abs_le]
    unfold highNCoefficient
    constructor <;> linarith
  nlinarith

/-- A single explicit constant bounds every error term for fixed M. -/
theorem innerError_uniform (n M p : ℕ) (hp : 3≤p) (hodd : p%2=1)
    (hcutoff : K n≤M*p) : innerError n M p ≤ 1000*((M:ℚ)+1)^2 := by
  let S : ℚ := (M:ℚ)+1
  have hS : 1≤S := by dsimp [S]; have hM := Nat.cast_nonneg (α:=ℚ) M; linarith
  have hS0 : 0≤S := by linarith
  have hT0 : (0:ℚ)≤baseAllocation n M p := by positivity
  have hT : (baseAllocation n M p:ℚ)≤6*S := by
    have h := actual_baseAllocation_le n M p hp hodd hcutoff
    have hq : (baseAllocation n M p:ℚ)≤6*(M:ℚ) := by exact_mod_cast h
    dsimp [S]
    linarith
  have hNK : N n≤K n := by dsimp [N,K]; omega
  have ha0 : (0:ℚ)≤lowLevel (N n) p := by positivity
  have hb0 : (0:ℚ)≤lowLevel (K n) p := by positivity
  have ha : (lowLevel (N n) p:ℚ)≤2*S := by
    have h := lowLevel_le (N n) p M (by omega) (hNK.trans hcutoff)
    have hq : (lowLevel (N n) p:ℚ)≤2*(M:ℚ)+1 := by exact_mod_cast h
    dsimp [S]
    linarith
  have hb : (lowLevel (K n) p:ℚ)≤2*S := by
    have h := lowLevel_le (K n) p M (by omega) hcutoff
    have hq : (lowLevel (K n) p:ℚ)≤2*(M:ℚ)+1 := by exact_mod_cast h
    dsimp [S]
    linarith
  have hbase : baseError (N n) (K n) p (baseAllocation n M p) ≤ 107*S^2 :=
    baseError_bound_aux S _ _ _ hS hT0 hT ha0 ha hb0 hb
  have hc : |extraCost (baseAllocation n M p) (lowLevel (K n) p)|≤19*S := by
    rw [abs_le]
    unfold extraCost
    constructor <;> linarith
  have hc' : |extraCost (baseAllocation n M p) (lowLevel (K n) p)|/2+2≤12*S := by linarith
  have hc0 : 0≤|extraCost (baseAllocation n M p) (lowLevel (K n) p)|/2+2 := by positivity
  have hD : 14*(M:ℚ)+20≤20*S := by dsimp [S]; linarith
  have hprod : (14*(M:ℚ)+20)*(|extraCost (baseAllocation n M p) (lowLevel (K n) p)|/2+2) ≤
      240*S^2 := by
    nlinarith [mul_le_mul hD hc' hc0 (by positivity : 0≤20*S)]
  have hzero : (zeroDimension M:ℚ)*(2*(M:ℚ)+5)≤50*S^2 := by
    unfold zeroDimension
    push_cast
    dsimp [S]
    nlinarith [Nat.cast_nonneg (α:=ℚ) M]
  unfold innerError
  change _≤1000*S^2
  nlinarith [sq_nonneg S]

/-- Uniform sufficient form of the first estimate (5.7), with the
explicit loss p/2 accepted for the shortened irrationality proof. -/
theorem actual_innerGamma_uniform (n M p : ℕ) (ha : Admissible n M)
    (hp : 3≤p) (hodd : p%2=1) (hinner : 3*p≤K n) (hcutoff : K n≤M*p) :
    (p:ℚ)*gamma ((K n:ℚ)/p)-(p:ℚ)/2-1000*((M:ℚ)+1)^2 ≤
      (innerExponent n M p:ℚ) := by
  have h := actual_innerGamma_lower n M p ha hp hodd hinner hcutoff
  have he := innerError_uniform n M p hp hodd hcutoff
  linarith

#print axioms actual_innerGamma_uniform
end Zeta5InnerAsymptotics
