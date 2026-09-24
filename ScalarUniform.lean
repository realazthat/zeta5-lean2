import ScalarFloorSum
import Mathlib.Tactic

noncomputable section
namespace Zeta5InnerAsymptotics
open Zeta5Parameters

/-- The function N(x) of equation (5.5). -/
def scalarLimit (x : ℚ) : ℚ :=
  2*(37/40*x)*(⌊x⌋:ℚ)-12*(37/40*x)*(⌊3/40*x⌋:ℚ)-2*floorIntegral (37/40*x)

/-- The inner normalization kernel R(x) of equation (5.6). -/
def innerKernel (x : ℚ) : ℚ := -gamma x-scalarLimit x

theorem scalarLimit_at_prime_ratio (n p : ℕ) (hp : 0<p) :
    (p:ℚ)*scalarLimit ((K n:ℚ)/p) =
      2*(h n:ℚ)*((K n/p:ℕ):ℚ)-12*(h n:ℚ)*((N n/p:ℕ):ℚ)-
        2*(p:ℚ)*floorIntegral ((h n:ℚ)/p) := by
  have hpq : (p:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hp)
  have hh : (37:ℚ)/40*((K n:ℚ)/p)=(h n:ℚ)/p := by
    dsimp [K,h]
    push_cast
    ring
  have hN : (3:ℚ)/40*((K n:ℚ)/p)=(N n:ℚ)/p := by
    dsimp [K,N]
    push_cast
    ring
  unfold scalarLimit
  rw [hh,hN,floor_nat_ratio,floor_nat_ratio]
  simp only [Int.cast_natCast]
  field_simp

/-- Uniform scalar estimate at every prime in the cutoff range. -/
theorem actual_scalarLimit_error (n M p : ℕ) [Fact p.Prime]
    (ha : Admissible n M) (hcutoff : K n≤M*p) :
    |(padicValRat p (Zeta5Construction.normalizingScalar (N n) (h n)):ℚ)-
      (p:ℚ)*scalarLimit ((K n:ℚ)/p)|≤4*(M:ℚ) := by
  have hp0 : 0<p := (Fact.out : p.Prime).pos
  have hv := congrArg (fun z:ℤ => (z:ℚ)) (actual_normalizingScalar_valuation n M p ha hcutoff)
  simp only [Int.cast_sub,Int.cast_mul,Int.cast_sum,Int.cast_ofNat,Int.cast_natCast] at hv
  rw [scalar_floor_sum_eq_range] at hv
  have hs := floor_sum_error (h n) p hp0
  have hhk : h n≤K n := by dsimp [h,K]; omega
  have hm : 2*h n/p≤2*M := by
    have := Nat.div_mul_le_self (2*h n) p
    nlinarith
  have hmq : ((2*h n/p:ℕ):ℚ)≤2*(M:ℚ) := by exact_mod_cast hm
  rw [hv,scalarLimit_at_prime_ratio n p hp0,abs_le]
  rcases abs_le.mp hs with ⟨hslo,hshi⟩
  constructor <;> linarith

/-- The actual inner-prime exponent has a uniform sufficient upper bound
after negating it for the logarithm of the normalizer. -/
theorem actual_inner_localExponent_upper (n M p : ℕ) [Fact p.Prime]
    (ha : Admissible n M) (hcutoff : K n<p*M) (hinner : 3*p≤K n) :
    -(localExponent n M p:ℚ) ≤
      (p:ℚ)*innerKernel ((K n:ℚ)/p)+(p:ℚ)/2+1000*((M:ℚ)+1)^2+4*(M:ℚ) := by
  have hp : p.Prime := Fact.out
  have hcutoff' : K n≤M*p := by nlinarith
  have hlarge := actual_prime_gt_error n M p ha hcutoff'
  have hp3 : 3≤p := by omega
  have hodd : p%2=1 := by
    obtain ⟨k,hk⟩ := hp.odd_of_ne_two (by omega)
    omega
  have hi := actual_innerGamma_uniform n M p ha hp3 hodd hinner hcutoff'
  have hs := (abs_le.mp (actual_scalarLimit_error n M p ha hcutoff')).1
  unfold localExponent
  rw [if_neg (by omega),if_pos hinner]
  push_cast
  unfold innerKernel
  linarith

#print axioms actual_scalarLimit_error
#print axioms actual_inner_localExponent_upper
end Zeta5InnerAsymptotics
