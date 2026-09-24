import ScalarUniform
import Mathlib.Tactic

noncomputable section
namespace Zeta5OuterAsymptotics
open Zeta5Parameters

private theorem nat_sub_cast_max (a b : ℕ) :
    ((a-b:ℕ):ℚ)=max ((a:ℚ)-b) 0 := by
  by_cases h : b≤a
  · rw [Nat.cast_sub h,max_eq_left (sub_nonneg.mpr (by exact_mod_cast h))]
  · have hq : (a:ℚ)-b≤0 := by
      have h' : (a:ℚ)≤b := by exact_mod_cast (Nat.le_of_lt (by omega : a<b))
      linarith
    rw [Nat.sub_eq_zero_of_le (by omega),Nat.cast_zero,max_eq_right hq]

/-- The residue-only limiting expression R₀, after omitting the beneficial
zero-weight rank restriction. -/
def outerResidueMass (K N p : ℚ) : ℚ :=
  if K<p then 0 else
  if K<2*p then
    7*(K-p)-6*min N (K-p)-6*max (N+K-2*p) 0+max (K+4*N-2*p) 0
  else
    8*K-9*p-8*N-5*min N (K-2*p)-5*max (N+K-3*p) 0

def outerResidue (y : ℚ) : ℚ := outerResidueMass 1 (3/40) y

private theorem overlap_cast_lower (n p : ℕ) :
    max ((N n:ℚ)+((K n%p:ℕ):ℚ)-p) 0 ≤ (overlap n p:ℚ) := by
  unfold overlap
  rw [nat_sub_cast_max]
  push_cast
  apply max_le_max_right
  linarith

private theorem correctionRank_cast_upper (n p : ℕ) :
    (correctionRank n p:ℚ)≤max ((K n:ℚ)+4*(N n:ℚ)-2*p) 0+2 := by
  unfold correctionRank
  rw [nat_sub_cast_max]
  push_cast
  apply max_le
  · have h := le_max_left ((K n:ℚ)+4*(N n:ℚ)-2*p) 0
    linarith
  · have h := le_max_right ((K n:ℚ)+4*(N n:ℚ)-2*p) 0
    linarith

/-- The actual coarse outer exponent is bounded by K R₀(p/K)+3.
No class-count asymptotic or zero-count rank formula is assumed. -/
theorem actual_coarseOuterExponent_upper (n p : ℕ) (houter : K n<3*p) :
    -(coarseOuterExponent n p:ℚ) ≤ outerResidueMass (K n) (N n) p+3 := by
  have hKq : (K n:ℚ)<(p:ℚ) ↔ K n<p := by norm_cast
  have h2q : (K n:ℚ)<2*(p:ℚ) ↔ K n<2*p := by norm_cast
  unfold coarseOuterExponent outerResidueMass
  simp only [hKq,h2q]
  split_ifs with hK h2
  · norm_num
  · have hpk : p≤K n := by omega
    have hrem : K n%p=K n-p := by
      rw [Nat.mod_eq_sub_mod hpk,Nat.mod_eq_of_lt (by omega)]
    have hu := overlap_cast_lower n p
    rw [hrem,Nat.cast_sub hpk] at hu
    have hu' : max ((N n:ℚ)+(K n:ℚ)-2*p) 0 ≤ (overlap n p:ℚ) := by
      convert hu using 2 <;> ring
    have ht : min (N n:ℚ) ((K n:ℚ)-p)+max ((N n:ℚ)+(K n:ℚ)-2*p) 0 ≤
        (removedExtraCount n p:ℚ) := by
      unfold removedExtraCount
      rw [hrem,Nat.cast_add,Nat.cast_min,Nat.cast_sub hpk]
      exact add_le_add_right hu' _
    have hr := correctionRank_cast_upper n p
    simp only [Int.cast_sub,Int.cast_add,Int.cast_mul,Int.cast_neg,Int.cast_ofNat,Int.cast_one,Int.cast_natCast]
    linarith only [ht,hr]
  · have hpk : 2*p≤K n := by omega
    have hrem : K n%p=K n-2*p := by
      rw [Nat.mod_eq_sub_mod (by omega : p≤K n),
        Nat.mod_eq_sub_mod (by omega : p≤K n-p),Nat.mod_eq_of_lt (by omega)]
      omega
    have hu := overlap_cast_lower n p
    rw [hrem,Nat.cast_sub hpk,Nat.cast_mul,Nat.cast_ofNat] at hu
    have hu' : max ((N n:ℚ)+(K n:ℚ)-3*p) 0 ≤ (overlap n p:ℚ) := by
      convert hu using 2 <;> ring
    have ht : min (N n:ℚ) ((K n:ℚ)-2*p)+max ((N n:ℚ)+(K n:ℚ)-3*p) 0 ≤
        (removedExtraCount n p:ℚ) := by
      unfold removedExtraCount
      rw [hrem,Nat.cast_add,Nat.cast_min,Nat.cast_sub hpk,Nat.cast_mul,Nat.cast_ofNat]
      exact add_le_add_right hu' _
    have hr : (correctionRank n p:ℚ)=(K n:ℚ)+4*(N n:ℚ)+2-2*p := by
      unfold correctionRank
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    simp only [Int.cast_sub,Int.cast_add,Int.cast_mul,Int.cast_neg,Int.cast_ofNat,Int.cast_one,Int.cast_natCast]
    linarith only [ht,hr]

theorem outerResidueMass_scale (k K N p : ℚ) (hk : 0<k) :
    outerResidueMass (k*K) (k*N) (k*p) = k*outerResidueMass K N p := by
  have h2 : 2*(k*p)=k*(2*p) := by ring
  unfold outerResidueMass
  simp only [h2,mul_lt_mul_left hk]
  split_ifs <;> simp only [mul_zero]
  · simp only [mul_add,mul_sub,mul_min_of_nonneg hk.le,mul_max_of_nonneg hk.le,mul_zero]
    ring_nf
  · simp only [mul_add,mul_sub,mul_min_of_nonneg hk.le,mul_max_of_nonneg hk.le,mul_zero]
    ring_nf

theorem outerResidue_at_prime_ratio (n p : ℕ) (hn : 0<n) :
    outerResidueMass (K n) (N n) p = (K n:ℚ)*outerResidue ((p:ℚ)/(K n:ℚ)) := by
  have hk : (0:ℚ)<K n := by dsimp [K]; positivity
  have hnq : (K n:ℚ)*(3/40)=(N n:ℚ) := by dsimp [K,N]; push_cast; ring
  have hpq : (K n:ℚ)*((p:ℚ)/(K n:ℚ))=p := by field_simp
  have he := outerResidueMass_scale (K n) 1 (3/40) ((p:ℚ)/(K n:ℚ)) hk
  simpa only [mul_one,hnq,hpq,outerResidue] using he

/-- The sufficient outer normalization kernel, with the rank restriction
term d omitted. -/
def outerKernel (y : ℚ) : ℚ :=
  outerResidue y-y*Zeta5InnerAsymptotics.scalarLimit (1/y)

theorem actual_outer_localExponent_upper (n M p : ℕ) [Fact p.Prime]
    (ha : Admissible n M) (houter : K n<3*p) :
    -(localExponent n M p:ℚ) ≤
      (K n:ℚ)*outerKernel ((p:ℚ)/(K n:ℚ))+3+4*(M:ℚ) := by
  have hn : 0<n := by obtain ⟨hM,hK⟩ := ha; dsimp [K] at hK; nlinarith
  have hp : 0<p := (Fact.out : p.Prime).pos
  have hkq : (0:ℚ)<K n := by dsimp [K]; positivity
  have hpq : (0:ℚ)<p := by exact_mod_cast hp
  have hcut : K n<p*M := by have hM := ha.1; nlinarith
  have hcut' : K n≤M*p := by nlinarith
  have hs := (abs_le.mp (Zeta5InnerAsymptotics.actual_scalarLimit_error n M p ha hcut')).1
  have ho := actual_coarseOuterExponent_upper n p houter
  rw [outerResidue_at_prime_ratio n p hn] at ho
  have hinv : 1/((p:ℚ)/(K n:ℚ))=(K n:ℚ)/p := by field_simp
  have hscale : (K n:ℚ)*((p:ℚ)/(K n:ℚ))=p := by field_simp
  unfold localExponent
  rw [if_neg (by omega),if_neg (by omega)]
  push_cast
  unfold outerKernel
  rw [hinv,mul_sub,←mul_assoc,hscale]
  linarith

theorem coarse_positive_decay_margin :
    (7907:ℚ)/100-1600/36-1600*(9/640)=10913/900 ∧
    10<(7907:ℚ)/100-1600/36-1600*(9/640) := by norm_num

#print axioms actual_coarseOuterExponent_upper
end Zeta5OuterAsymptotics
