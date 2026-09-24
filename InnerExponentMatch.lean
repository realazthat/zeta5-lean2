import InnerSources
import InnerDiskDegrees

noncomputable section
namespace Zeta5InnerExponentMatch
open Zeta5Parameters Zeta5InnerBasis Zeta5InnerDeterminant Zeta5InnerSources
open Zeta5InnerDisk Zeta5InnerFactorization Zeta5InnerFactorCounts

lemma denExponent_zero (A p : ℕ) (hp : 0<p) : denExponent A p 0=2*(A/p) := by
  unfold denExponent
  rw [near_card, linearNearCount_zero A p hp]

lemma denExponent_ordinary (A p a : ℕ) (ha : 1≤a) (hap : 2*a<p) :
    denExponent A p a=poleCount A p a := by
  unfold denExponent
  rw [near_card, linearNearCount_ordinary A p a ha hap]

lemma actual_disk_exponent_eq_source (n M p : ℕ) (hodd : p%2=1)
    (i j : RowIndex n M p) (c : Fin p) :
    (numeratorExponent (N n) ((p-1)/2) p c.val (rowOrder n M p i) (rowOrder n M p j):ℤ)-
      (denExponent (K n) p c.val:ℤ)-4=sourceExponent n M p hodd i j c := by
  have hp : 0<p := by omega
  have hm : 2*((p-1)/2)<p := by omega
  by_cases hc : c.val=0
  · simp only [hc, Nat.cast_zero, sourceExponent, if_true]
    rw [zero_numerator_exponent _ _ _ _ _ hp hm, denExponent_zero _ _ hp]
    push_cast
    ring
  · let a := sourceClass p hodd c
    have ha : a.val≠0 := fun hh => hc ((sourceClass_zero_iff p hodd c).mp hh)
    have hap : a.val≤p := by have hh:=a.isLt; omega
    have hn : numeratorExponent (N n) ((p-1)/2) p c.val (rowOrder n M p i) (rowOrder n M p j)=
        numeratorExponent (N n) ((p-1)/2) p a.val (rowOrder n M p i) (rowOrder n M p j) := by
      rcases sourceClass_eq_or_reflect p hodd c with h|h
      · rw [h]
      · rw [h, numeratorExponent_reflect _ _ _ _ _ _ hap]
    have hd : denExponent (K n) p c.val=denExponent (K n) p a.val := by
      rcases sourceClass_eq_or_reflect p hodd c with h|h
      · rw [h]
      · rw [h, denExponent_reflect _ _ _ hap]
    rw [hn,hd,ordinary_numerator_exponent _ _ _ _ _ hm a (by simpa using ha),
      denExponent_ordinary _ _ _ (by omega) (by have hh:=a.isLt; omega)]
    simp only [sourceExponent,hc,if_false]
    push_cast
    ring

lemma norm_of_p_scaled_norm (p : ℕ) [Fact p.Prime] (u d : ℕ) (z : ℚ_[p])
    (hn : ‖((p:ℚ_[p])^d/(p:ℚ_[p])^u)*z‖≤1) :
    ‖z‖≤(p:ℝ)^(-((u:ℤ)-(d:ℤ))) := by
  have hp0 : (p:ℚ_[p])≠0 := by exact_mod_cast (Fact.out:p.Prime).ne_zero
  have hpr : (p:ℝ)≠0 := by exact_mod_cast (Fact.out:p.Prime).ne_zero
  calc
    ‖z‖ = ‖(p:ℚ_[p])^u/(p:ℚ_[p])^d‖*‖((p:ℚ_[p])^d/(p:ℚ_[p])^u)*z‖ := by
      rw [←norm_mul]
      congr 1
      field_simp
    _ ≤ ‖(p:ℚ_[p])^u/(p:ℚ_[p])^d‖ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    _ = _ := by
      rw [norm_div, norm_pow, norm_pow, Padic.norm_p]
      rw [neg_sub, zpow_sub₀ hpr]
      simp only [zpow_natCast, inv_pow, div_eq_mul_inv, inv_inv]
      ring

#print axioms actual_disk_exponent_eq_source
#print axioms norm_of_p_scaled_norm
end Zeta5InnerExponentMatch
