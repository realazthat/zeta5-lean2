import InnerGamma
import Mathlib.Tactic

noncomputable section
namespace Zeta5InnerAsymptotics
open Zeta5Parameters

theorem baseIntegral_mul (A B p : ℕ) (T : ℚ) (hp : 0<p) :
    (p:ℚ)*baseIntegral T (lowLevel A p) (lowLevel B p)
      (highMass A p/p) (highMass B p/p) (overlapMass A B p/p) = baseMass A B p T := by
  have hpq : (p:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hp)
  unfold baseIntegral baseMass
  field_simp

/-- Evaluation of the canonical limiting kernel at the actual prime ratio. -/
theorem gamma_at_prime_ratio (n p : ℕ) (hp : 0<p) :
    gamma ((K n:ℚ)/p) =
      gammaAtAllocation (2*((h n:ℚ)+3*(N n:ℚ))/p)
        ⌊2*((h n:ℚ)+3*(N n:ℚ))/p⌋
        (lowLevel (N n) p) (lowLevel (K n) p)
        (highMass (N n) p/p) (highMass (K n) p/p)
        (overlapMass (N n) (K n) p/p) := by
  have hy : (23:ℚ)/10*((K n:ℚ)/p) = 2*((h n:ℚ)+3*(N n:ℚ))/p := by
    unfold K h N
    push_cast
    ring
  have hN : (3:ℚ)/20*((K n:ℚ)/p) = 2*(N n:ℚ)/p := by
    unfold K N
    push_cast
    ring
  have hK : 2*((K n:ℚ)/p) = 2*(K n:ℚ)/p := by ring
  have hN' : (3:ℚ)/40*((K n:ℚ)/p) = (N n:ℚ)/p := by
    unfold K N
    push_cast
    ring
  unfold gamma
  rw [hy,hN,hK,hN',← highMass_div (N n) p hp,← highMass_div (K n) p hp,
    ← overlapMass_div (N n) (K n) p hp,
    ← lowLevel_eq_floor (N n) p hp,← lowLevel_eq_floor (K n) p hp]
  simp only [Int.cast_natCast]

theorem actual_prime_gt_error (n M p : ℕ) (ha : Admissible n M)
    (hcutoff : K n ≤ M*p) : 14*M+20<p := by
  obtain ⟨hM,hK⟩ := ha
  nlinarith

def innerError (n M p : ℕ) : ℚ :=
  baseError (N n) (K n) p (baseAllocation n M p) +
  (zeroDimension M:ℚ)*(2*(M:ℚ)+5) +
  (14*(M:ℚ)+20)*(|extraCost (baseAllocation n M p) (lowLevel (K n) p)|/2+2)

/-- The literal inner exponent satisfies the limiting-kernel inequality
uniformly even when the base allocation crosses an integer. -/
theorem actual_innerGamma_lower (n M p : ℕ) (ha : Admissible n M)
    (hp : 3≤p) (hodd : p%2=1) (hinner : 3*p≤K n) (hcutoff : K n≤M*p) :
    (p:ℚ)*gamma ((K n:ℚ)/p)-(p:ℚ)/2-innerError n M p ≤
      (innerExponent n M p:ℚ) := by
  have hp0 : 0<p := by omega
  have hpq : (0:ℚ)<p := by exact_mod_cast hp0
  let y : ℚ := 2*((h n:ℚ)+3*(N n:ℚ))/p
  let t : ℕ := baseAllocation n M p
  let s : ℚ := (extraCount n M p:ℚ)/p
  let δ : ℚ := y-(t:ℚ)-2*s
  let D : ℚ := 2*((h n:ℚ)+3*(N n:ℚ))-
      ((p:ℚ)*(t:ℚ)+2*(extraCount n M p:ℚ))
  have hδ : δ=D/p := by dsimp [δ,D,y,s]; field_simp; ring
  have herr := actual_allocation_error n M p ha hp hodd hcutoff
  change 0≤D ∧ D≤14*(M:ℚ)+20 at herr
  have hlarge : 14*(M:ℚ)+20<(p:ℚ) := by exact_mod_cast actual_prime_gt_error n M p ha hcutoff
  have hd0 : 0≤δ := by rw [hδ]; exact div_nonneg herr.1 hpq.le
  have hd : δ<1 := by rw [hδ,div_lt_one hpq]; exact herr.2.trans_lt hlarge
  have hE : extraCount n M p < (p-1)/2 := Nat.mod_lt _ (by omega)
  have hs0 : 0≤s := by dsimp [s]; positivity
  have hs : s<1/2 := by
    dsimp [s]
    rw [div_lt_iff₀ hpq]
    have he : 2*extraCount n M p<p := by omega
    have heq : 2*(extraCount n M p:ℚ)<p := by exact_mod_cast he
    linarith
  have hadj := adjacent_allocation_of_error y t s δ hs0 hs hd0 hd rfl
  have hadjq : (t:ℚ)=(⌊y⌋:ℚ) ∨ (t:ℚ)+1=(⌊y⌋:ℚ) := by
    rcases hadj with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  have hL : 0≤highMass (K n) p/(p:ℚ) := by
    rw [highMass_div _ _ hp0]
    exact div_nonneg (Int.fract_nonneg _) (by norm_num)
  have hg := gamma_allocation_lower y (⌊y⌋:ℚ) t s (lowLevel (N n) p) (lowLevel (K n) p)
    (highMass (N n) p/p) (highMass (K n) p/p) (overlapMass (N n) (K n) p/p)
    hadjq (Int.floor_le _) (Int.lt_floor_add_one _) hs.le hL hd0
  have hgm := mul_le_mul_of_nonneg_left hg hpq.le
  have hΓ := gamma_at_prime_ratio n p hp0
  change gamma ((K n:ℚ)/p) = gammaAtAllocation y _ _ _ _ _ _ at hΓ
  rw [←hΓ] at hgm
  have hB := baseIntegral_mul (N n) (K n) p t hp0
  have hps : (p:ℚ)*s=(extraCount n M p:ℚ) := by dsimp [s]; field_simp
  have hpδ : (p:ℚ)*δ=D := by rw [hδ]; field_simp
  have hc0 : 0≤|extraCost (t:ℚ) (lowLevel (K n) p)|/2+2 := by positivity
  have hD := mul_le_mul_of_nonneg_right herr.2 hc0
  have hord := actual_innerExponent_lower n M p ha hp hodd hinner hcutoff
  unfold innerError
  dsimp [t] at hB hps hpδ hc0 hD hgm
  change (p:ℚ)*δ=D at hpδ
  change (p:ℚ)*s=(extraCount n M p:ℚ) at hps
  unfold extraCost at hgm hD
  have hδ' : y-(baseAllocation n M p:ℚ)-2*s=δ := rfl
  rw [hδ'] at hgm
  rw [mul_add,mul_add,mul_add,hB,
    ← mul_assoc (p:ℚ) s, hps, ← mul_assoc (p:ℚ) δ, hpδ] at hgm
  unfold extraCost
  linarith only [hgm,hD,hord]

#print axioms actual_innerGamma_lower
end Zeta5InnerAsymptotics
