import OuterNear

/-! Elementary valuation estimates for the outer simple-pole residues. -/
noncomputable section
open scoped BigOperators
open Polynomial Finset
namespace Zeta5OuterArithmetic
open Zeta5Construction Zeta5OuterMoments Zeta5OuterBasis Zeta5OuterNear Zeta5Outer

lemma nat_padicVal_le_one (p n : ℕ) [Fact p.Prime] (hn : 0 < n) (hnp : n < p^2) :
    padicValNat p n ≤ 1 := by
  by_contra hv
  have hd : p^2 ∣ n := (padicValNat_dvd_iff_le hn.ne').mpr (by omega)
  exact Nat.not_dvd_of_pos_of_lt hn hnp hd

lemma int_padicVal_le_one (p : ℕ) [Fact p.Prime] (z : ℤ) (hz : z ≠ 0)
    (hzp : z.natAbs < p^2) : padicValInt p z ≤ 1 :=
  nat_padicVal_le_one p z.natAbs (Int.natAbs_pos.mpr hz) hzp

lemma square_difference_padicVal_le_one (p j k : ℕ) [Fact p.Prime]
    (hp : 3 ≤ p) (hj : 0 < j) (hk : 0 < k) (hjk : j ≠ k)
    (hsum : j+k < p^2) (hjunit : ¬ p ∣ j) :
    padicValRat p ((j : ℚ)^2 - (k : ℚ)^2) ≤ 1 := by
  have hd0 : (j : ℤ)-(k : ℤ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr (show (j : ℤ) ≠ k by exact_mod_cast hjk)
  have hs0 : (j : ℤ)+(k : ℤ) ≠ 0 := by positivity
  have hdv : padicValInt p ((j : ℤ)-(k : ℤ)) ≤ 1 := by
    apply int_padicVal_le_one p _ hd0
    exact lt_of_le_of_lt (by simpa using Int.natAbs_sub_le (j : ℤ) (k : ℤ)) hsum
  have hsv : padicValInt p ((j : ℤ)+(k : ℤ)) ≤ 1 := by
    apply int_padicVal_le_one p _ hs0
    simpa only [← Nat.cast_add, Int.natAbs_natCast] using hsum
  have hone : ¬ (p : ℤ) ∣ (j : ℤ)-(k : ℤ) ∨ ¬ (p : ℤ) ∣ (j : ℤ)+(k : ℤ) := by
    by_contra hh
    simp only [not_or, not_not] at hh
    have hh' := dvd_add hh.1 hh.2
    have hid : ((j : ℤ)-(k : ℤ))+((j : ℤ)+(k : ℤ)) = 2*(j : ℤ) := by ring
    rw [hid] at hh'
    have hh'' : p ∣ 2*j := by exact_mod_cast hh'
    rcases (Fact.out : p.Prime).dvd_mul.mp hh'' with hp2 | hpj
    · exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega) hp2
    · exact hjunit hpj
  have hval : padicValInt p (((j : ℤ)-(k : ℤ))*((j : ℤ)+(k : ℤ))) ≤ 1 := by
    rw [padicValInt.mul hd0 hs0]
    rcases hone with hd | hs
    · rw [padicValInt.eq_zero_of_not_dvd hd, zero_add]
      exact hsv
    · rw [padicValInt.eq_zero_of_not_dvd hs, add_zero]
      exact hdv
  have hid : ((j : ℚ)^2-(k : ℚ)^2) =
      (((j : ℤ)-(k : ℤ))*((j : ℤ)+(k : ℤ)) : ℤ) := by push_cast; ring
  rw [hid, padicValRat.of_int]
  exact_mod_cast hval

lemma ordinary_pole_not_dvd (p m N h : ℕ) (hp : p = 2*m+1) (a : Fin (m+1))
    (ha : 0 < a.val) (k : Fin h) (hk : k ∈ classMembers p m N h hp a) :
    ¬ p ∣ poleIndex N k := by
  intro hd
  have hc := congrArg Fin.val ((mem_filter.mp hk).2)
  simp only [poleClass, Nat.mod_eq_zero_of_dvd hd, Nat.sub_zero, min_eq_left (Nat.zero_le _)] at hc
  omega

lemma ordinary_difference_padicVal_le_one (p m N h : ℕ) [Fact p.Prime]
    (hp : p = 2*m+1) (hp3 : 3 ≤ p) (hK : 2*(N+h) < p^2)
    (a : Fin (m+1)) (ha : 0 < a.val) (k l : Fin h)
    (hk : k ∈ classMembers p m N h hp a) (hkl : k ≠ l) :
    padicValRat p (node N k-node N l) ≤ 1 := by
  have hdiff : node N k-node N l = -((poleIndex N k : ℚ)^2-(poleIndex N l : ℚ)^2) := by
    unfold node
    ring
  rw [hdiff, padicValRat.neg]
  apply square_difference_padicVal_le_one p _ _ hp3 (poleIndex_pos N k) (poleIndex_pos N l)
  · exact fun he => hkl (poleIndex_injective N h he)
  · have hklt := k.isLt
    have hllt := l.isLt
    unfold poleIndex
    omega
  · exact ordinary_pole_not_dvd p m N h hp a ha k hk

lemma prime_dvd_integer_valuation (p : ℕ) [Fact p.Prime] (z : ℤ) (hz : (p : ℤ) ∣ z) :
    (1 : WithTop ℚ) ≤ rationalPadicValuation p (z : ℚ) := by
  obtain ⟨t, rfl⟩ := hz
  push_cast
  exact rationalPadicValuation_prime_mul_int p t

lemma class_linear_factor_valuation (p m N h : ℕ) [Fact p.Prime]
    (hp : p = 2*m+1) (a : Fin (m+1)) (k : Fin h)
    (hk : k ∈ classMembers p m N h hp a) :
    (1 : WithTop ℚ) ≤ rationalPadicValuation p (node N k + (a.val : ℚ)^2) := by
  have hc := poleClass_square p m (poleIndex N k) hp
  rw [(mem_filter.mp hk).2] at hc
  have hz : (p : ℤ) ∣ (-((poleIndex N k : ℤ)^2)+(a.val : ℤ)^2) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    push_cast
    rw [hc]
    ring
  have hv := prime_dvd_integer_valuation p _ hz
  simpa only [Int.cast_add, Int.cast_neg, Int.cast_pow, Int.cast_natCast, node] using hv

lemma inverse_nat_lower (p j : ℕ) [Fact p.Prime] (hj : 0 < j) (hjp : j < p^2) :
    (-1 : WithTop ℚ) ≤ rationalPadicValuation p (j : ℚ)⁻¹ := by
  apply (rationalPadicValuation_lower_iff p _ (-1)).mpr
  right
  rw [padicValRat.inv, padicValRat.of_nat]
  have hv := nat_padicVal_le_one p j hj hjp
  exact_mod_cast (show (-1 : ℤ) ≤ -(padicValNat p j : ℤ) by omega)

lemma fifthHarmonic_lower_five (p j : ℕ) [Fact p.Prime] (hjp : j < p^2) :
    (-5 : WithTop ℚ) ≤ rationalPadicValuation p (fifthHarmonic j) := by
  unfold fifthHarmonic
  apply (rationalPadicValuation p).map_le_sum
  intro k hk
  apply (rationalPadicValuation_lower_iff p _ (-5)).mpr
  right
  rw [one_div, padicValRat.inv, padicValRat.pow, padicValRat.of_nat]
  have hv := nat_padicVal_le_one p (k+1) (by omega)
    (by have := mem_range.mp hk; omega)
  simp only [Int.cast_neg, Int.cast_mul, Int.cast_natCast]
  have hv' : (padicValNat p (k+1) : ℚ) ≤ 1 := by exact_mod_cast hv
  norm_num only [Nat.cast_ofNat]
  linarith

lemma localPoleConstant_lower (p j d : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (hj : 0 < j) (hjp : j < p^2) (hd : d ≤ 1)
    (hvj : (d : WithTop ℚ) ≤ rationalPadicValuation p (j : ℚ)) :
    (((4*(d : ℚ)-5) : ℚ) : WithTop ℚ) ≤ rationalPadicValuation p (localPoleConstant j) := by
  have hpow : ((4*(d : ℚ) : ℚ) : WithTop ℚ) ≤ rationalPadicValuation p ((j : ℚ)^4) := by
    rw [AddValuation.map_pow]
    have hh := nsmul_le_nsmul_right hvj 4
    rw [← WithTop.coe_natCast, ← WithTop.coe_nsmul] at hh
    simpa only [nsmul_eq_mul, Nat.cast_ofNat] using hh
  have hfirst : (((4*(d : ℚ)-5) : ℚ) : WithTop ℚ) ≤ rationalPadicValuation p
      (-(j : ℚ)^4*fifthHarmonic j) := by
    rw [AddValuation.map_mul, AddValuation.map_neg]
    have hh := add_le_add hpow (fifthHarmonic_lower_five p j hjp)
    change (((4*(d : ℚ) : ℚ) : WithTop ℚ) + ((-5 : ℚ) : WithTop ℚ)) ≤ _ at hh
    rw [← WithTop.coe_add] at hh
    simpa only [sub_eq_add_neg] using hh
  have hfour : rationalPadicValuation p (4 : ℚ) = 0 :=
    rationalPadicValuation_unit_below p 4 (by omega) (by omega)
  have hquarter : rationalPadicValuation p (1/4 : ℚ) = 0 := by
    simpa only [one_div] using rationalPadicValuation_inv_unit p 4 hfour
  have htwo : rationalPadicValuation p (2 : ℚ) = 0 :=
    rationalPadicValuation_unit_below p 2 (by omega) (by omega)
  have hlast : (-1 : WithTop ℚ) ≤ rationalPadicValuation p (1/(2*(j : ℚ))) := by
    rw [one_div, mul_inv_rev, AddValuation.map_mul,
      rationalPadicValuation_inv_unit p 2 htwo, add_zero]
    exact inverse_nat_lower p j hj hjp
  have hbound0 : (4*(d : ℚ)-5) ≤ 0 := by exact_mod_cast (show (4*(d : ℤ)-5) ≤ 0 by omega)
  have hbound1 : (4*(d : ℚ)-5) ≤ -1 := by exact_mod_cast (show (4*(d : ℤ)-5) ≤ -1 by omega)
  unfold localPoleConstant
  apply (rationalPadicValuation p).map_le_add
  · apply (rationalPadicValuation p).map_le_sub hfirst
    rw [hquarter]
    exact_mod_cast hbound0
  · exact le_trans (WithTop.coe_le_coe.mpr hbound1) hlast

lemma coeffLower_affine_bound (p : ℕ) [Fact p.Prime] (c d e : ℚ)
    (hc : (e : WithTop ℚ) ≤ rationalPadicValuation p c)
    (hd : (e : WithTop ℚ) ≤ rationalPadicValuation p d) :
    CoeffLower (rationalPadicValuation p) (X*C c+C d) e := by
  apply coeffLower_add_same
  · simpa using coeffLower_mul (rationalPadicValuation p)
      (coeffLower_X_zero p) (coeffLower_C _ c e hc)
  · exact coeffLower_C _ d e hd

theorem poleFunctional_lower_five (p j : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (hj : 0 < j) (hjp : j < p^2) :
    CoeffLower (rationalPadicValuation p) (poleFunctional j) (-5) := by
  rw [poleFunctional_affine]
  apply coeffLower_affine_bound
  · have hh := rationalPadicValuation_int_nonneg p ((j : ℤ)^4)
    push_cast at hh
    exact le_trans (WithTop.coe_le_coe.mpr (by norm_num)) hh
  · change ((-5 : ℚ) : WithTop ℚ) ≤ rationalPadicValuation p (localPoleConstant j)
    simpa only [Nat.cast_zero, mul_zero, zero_sub] using localPoleConstant_lower p j 0 hp hj hjp (by omega)
      (by simpa using rationalPadicValuation_int_nonneg p (j : ℤ))

theorem poleFunctional_lower_one (p j : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (hj : 0 < j) (hjp : j < p^2) (hdiv : p ∣ j) :
    CoeffLower (rationalPadicValuation p) (poleFunctional j) (-1) := by
  rw [poleFunctional_affine]
  apply coeffLower_affine_bound
  · have hh := rationalPadicValuation_int_nonneg p ((j : ℤ)^4)
    push_cast at hh
    exact le_trans (WithTop.coe_le_coe.mpr (by norm_num)) hh
  · change ((-1 : ℚ) : WithTop ℚ) ≤ rationalPadicValuation p (localPoleConstant j)
    simpa only [Nat.cast_one, mul_one, show (4 : ℚ)-5 = -1 by norm_num] using localPoleConstant_lower p j 1 hp hj hjp (by omega)
      (prime_dvd_integer_valuation p (j : ℤ) (by exact_mod_cast hdiv))

#print axioms poleFunctional_lower_five
#print axioms poleFunctional_lower_one
end Zeta5OuterArithmetic
