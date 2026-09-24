import SmallPrimeProducts
import SmallPrimeResidues

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5Local
open IsUltrametricDist

lemma factorial_valuation_balanced (p K j : ℕ) [Fact p.Prime] (hj : j ≤ 2*K) :
    padicValNat p j.factorial + padicValNat p (2*K-j).factorial ≤
      2*padicValNat p K.factorial + Nat.log p (2*K) := by
  by_cases h : K ≤ j
  · have hr : j-K ≤ K := by omega
    have he1 : K+(j-K)=j := by omega
    have he2 : K-(j-K)=2*K-j := by omega
    simpa only [he1, he2] using factorial_valuation_discrepancy p K (j-K) hr
  · have hr : K-j ≤ K := Nat.sub_le _ _
    have he1 : K+(K-j)=2*K-j := by omega
    have he2 : K-(K-j)=j := by omega
    simpa only [he1, he2, add_comm] using factorial_valuation_discrepancy p K (K-j) hr

lemma consecutive_reduced_product_norm (p n j : ℕ) [Fact p.Prime] (hj : j ≤ n) :
    ‖∏ i ∈ (Finset.range (n+1)).erase j, ((j : ℚ_[p])-i)‖ =
      ‖(j.factorial : ℚ_[p])‖ * ‖((n-j).factorial : ℚ_[p])‖ := by
  induction n generalizing j with
  | zero =>
    have : j=0 := by omega
    subst j
    simp
  | succ n ih =>
    by_cases h : j=n+1
    · subst j
      rw [Finset.range_add_one, Finset.erase_insert (by simp)]
      have he := Finset.prod_range_natCast_sub (R := ℚ_[p]) (n+1) (n+1)
      rw [he, ← Nat.descFactorial_eq_prod_range, Nat.descFactorial_self]
      simp
    · have hjn : j ≤ n := by omega
      rw [Finset.range_add_one, Finset.erase_insert_of_ne (Ne.symm h),
        Finset.prod_insert (by simp), norm_mul, ih j hjn]
      have he : (j : ℚ_[p])-((n+1 : ℕ) : ℚ_[p]) = -((n+1-j : ℕ) : ℚ_[p]) := by
        rw [Nat.cast_sub (by omega : j≤n+1)]
        push_cast
        ring
      rw [he, norm_neg]
      have hn : n+1-j = (n-j)+1 := by omega
      rw [hn, Nat.factorial_succ, Nat.cast_mul, norm_mul]
      ring

lemma factorial_ratio_balanced_norm (p K j : ℕ) [hp : Fact p.Prime] (hj : j ≤ 2*K) :
    ‖((K.factorial : ℚ_[p])^2)/(j.factorial*(2*K-j).factorial)‖ ≤
      (p : ℝ)^Nat.log p (2*K) := by
  have hk : (K.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero K
  have hjq : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hj' : ((2*K-j).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2*K-j)
  let q : ℚ := K.factorial^2/(j.factorial*(2*K-j).factorial)
  have hq : q ≠ 0 := div_ne_zero (pow_ne_zero _ hk) (mul_ne_zero hjq hj')
  have hv : -(Nat.log p (2*K) : ℤ) ≤ padicValRat p q := by
    dsimp [q]
    rw [padicValRat.div (pow_ne_zero _ hk) (mul_ne_zero hjq hj'),
      padicValRat.pow, padicValRat.mul hjq hj']
    simp only [padicValRat.of_nat]
    have h := factorial_valuation_balanced p K j hj
    omega
  have he : ((K.factorial : ℚ_[p])^2)/(j.factorial*(2*K-j).factorial) = (q : ℚ_[p]) := by
    simp [q]
  rw [he, Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hq),
    Padic.valuation_ratCast, ← zpow_natCast]
  exact (zpow_le_zpow_right₀ (by exact_mod_cast hp.out.one_le) (by omega))

lemma integer_difference_inv_norm (p B : ℕ) [hp : Fact p.Prime]
    (j i : ℤ) (hji : j≠i) (hbound : (j-i).natAbs ≤ B) :
    ‖(j : ℚ_[p])-(i : ℚ_[p])‖⁻¹ ≤ (p : ℝ)^Nat.log p B := by
  rw [← Int.cast_sub, ← norm_natAbs, padic_nat_inv_norm p _
    (Int.natAbs_ne_zero.mpr (sub_ne_zero.mpr hji))]
  exact pow_le_pow_right₀ (by exact_mod_cast hp.out.one_le)
    ((padicValNat_le_nat_log _).trans (Nat.log_mono_right hbound))

def smallPrimeRoots (K : ℕ) : Finset ℕ := (Finset.range (2*K+1)).erase K

def smallPrimeRoot (K j : ℕ) : ℚ := (j : ℚ)-K

lemma smallPrimeRoot_inj (K : ℕ) : Function.Injective (smallPrimeRoot K) := by
  intro i j h
  unfold smallPrimeRoot at h
  have h' : (i:ℚ)=(j:ℚ) := by linarith
  exact_mod_cast h'

lemma smallPrimeRoot_center_norm (p K j : ℕ) [hp : Fact p.Prime]
    (hj : j ∈ smallPrimeRoots K) :
    ‖reducedInverseProduct p (smallPrimeRoots K)
      (fun i => (smallPrimeRoot K i : ℚ_[p])) ((K.factorial:ℚ_[p])^2) j
      (smallPrimeRoot K j : ℚ_[p])‖ ≤ (p:ℝ)^Nat.log p (2*K) := by
  have hjK : j ≠ K := (Finset.mem_erase.mp hj).1
  have hjB : j ≤ 2*K := by have := Finset.mem_range.mp (Finset.mem_erase.mp hj).2; omega
  let v : ℕ → ℚ_[p] := fun i => (j:ℚ_[p])-i
  have hKmem : K ∈ (Finset.range (2*K+1)).erase j := by
    simp only [Finset.mem_erase, Finset.mem_range]
    omega
  have hp0 : (∏ i ∈ (Finset.range (2*K+1)).erase j, v i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    apply sub_ne_zero.mpr
    exact_mod_cast (Finset.ne_of_mem_erase hi).symm
  have he : reducedInverseProduct p (smallPrimeRoots K)
      (fun i => (smallPrimeRoot K i : ℚ_[p])) ((K.factorial:ℚ_[p])^2) j
      (smallPrimeRoot K j : ℚ_[p]) =
      (K.factorial:ℚ_[p])^2 * ((j:ℚ_[p])-K) /
        (∏ i ∈ (Finset.range (2*K+1)).erase j, v i) := by
    unfold reducedInverseProduct smallPrimeRoots smallPrimeRoot
    push_cast
    simp only [sub_sub_sub_cancel_right]
    rw [Finset.erase_right_comm]
    rw [← Finset.prod_erase_mul _ v hKmem]
    dsimp [v]
    have hj0 : (j:ℚ_[p])-(K:ℚ_[p]) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hjK)
    field_simp
  rw [he, norm_div, norm_mul]
  have hnorm : ‖∏ i ∈ (Finset.range (2*K+1)).erase j, v i‖ =
      ‖(j.factorial:ℚ_[p])‖*‖((2*K-j).factorial:ℚ_[p])‖ :=
    consecutive_reduced_product_norm p (2*K) j hjB
  rw [hnorm]
  have hjint : ‖(j:ℚ_[p])-(K:ℚ_[p])‖ ≤ 1 := by
    simpa only [Int.cast_sub, Int.cast_natCast] using Padic.norm_int_le_one (p:=p) ((j:ℤ)-K)
  have hb := factorial_ratio_balanced_norm p K j hjB
  rw [norm_div, norm_mul] at hb
  exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hjint (norm_nonneg _))
    (by positivity)).trans (by simpa only [mul_one] using hb)

#print axioms consecutive_reduced_product_norm
#print axioms factorial_ratio_balanced_norm
#print axioms integer_difference_inv_norm
#print axioms smallPrimeRoot_center_norm
end Zeta5Local
