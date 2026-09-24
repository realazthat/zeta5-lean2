import OuterPrimeLimit
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace Zeta5OuterAsymptotics
open Zeta5Parameters

theorem outer_prime_cell_bound (n M p : ℕ) (i : Fin 11)
    (ha : Admissible n M) (hpp : p.Prime)
    (hmem : p ∈ Finset.Ioc ⌊(outerCellLeft i:ℝ)*(K n:ℝ)⌋₊
      ⌊(outerCellRight i:ℝ)*(K n:ℝ)⌋₊) :
    -(localExponent n M p:ℝ) ≤
      (outerCellConstant i:ℝ)*(K n:ℝ)+(outerCellSlope i:ℝ)*(p:ℝ)+3+4*(M:ℝ) := by
  letI : Fact p.Prime := ⟨hpp⟩
  have hn : 0<n := by obtain ⟨hM,hK⟩ := ha; dsimp [K] at hK; nlinarith
  have hk : (0:ℚ)<K n := by dsimp [K]; positivity
  obtain ⟨hlo,hhi⟩ := Finset.mem_Ioc.mp hmem
  have hloR := Nat.lt_of_floor_lt hlo
  have hhiR := (Nat.le_floor_iff' hpp.ne_zero).mp hhi
  have hloQ : outerCellLeft i*(K n:ℚ)<(p:ℚ) := by exact_mod_cast hloR
  have hhiQ : (p:ℚ)≤outerCellRight i*(K n:ℚ) := by exact_mod_cast hhiR
  have hl : outerCellLeft i<(p:ℚ)/(K n:ℚ) := (lt_div_iff₀ hk).mpr hloQ
  have hr : (p:ℚ)/(K n:ℚ)≤outerCellRight i := (div_le_iff₀ hk).mpr hhiQ
  have hl3 : (1:ℚ)/3≤outerCellLeft i := by fin_cases i <;> norm_num [outerCellLeft]
  have houterQ : (K n:ℚ)<3*(p:ℚ) := by nlinarith
  have houter : K n<3*p := by exact_mod_cast houterQ
  have ho := actual_outer_localExponent_upper n M p ha houter
  rw [outerKernel_on_cells i _ hl hr] at ho
  have he : (K n:ℚ)*(outerCellConstant i+outerCellSlope i*((p:ℚ)/(K n:ℚ))) =
      outerCellConstant i*(K n:ℚ)+outerCellSlope i*(p:ℚ) := by field_simp
  rw [he] at ho
  exact_mod_cast ho

def outerLocalSum (n M : ℕ) : ℝ :=
  ∑ p ∈ Finset.Ioc ⌊(K n:ℝ)/3⌋₊ ⌊(37/20:ℝ)*(K n:ℝ)⌋₊ with p.Prime,
    -(localExponent n M p:ℝ)*Real.log p

/-- All actual outer-prime terms are bounded by the certified PNT model
plus a fixed multiple of theta, hence an asymptotically negligible error. -/
theorem outerLocalSum_le_model (n M : ℕ) (ha : Admissible n M) :
    outerLocalSum n M ≤ outerPrimeModel (K n:ℝ)+
      (3+4*(M:ℝ))*Chebyshev.theta ((37/20:ℝ)*(K n:ℝ)) := by
  have hk : (0:ℝ)≤K n := by positivity
  have hc : (0:ℝ)≤3+4*(M:ℝ) := by positivity
  unfold outerLocalSum
  rw [←outer_prime_partition _ hk]
  have hle : (∑ i : Fin 11, ∑ p ∈ Finset.Ioc ⌊(outerCellLeft i:ℝ)*(K n:ℝ)⌋₊
      ⌊(outerCellRight i:ℝ)*(K n:ℝ)⌋₊ with p.Prime, -(localExponent n M p:ℝ)*Real.log p) ≤
      ∑ i : Fin 11, ∑ p ∈ Finset.Ioc ⌊(outerCellLeft i:ℝ)*(K n:ℝ)⌋₊
        ⌊(outerCellRight i:ℝ)*(K n:ℝ)⌋₊ with p.Prime,
        (((outerCellConstant i:ℝ)*(K n:ℝ)+(outerCellSlope i:ℝ)*(p:ℝ))*Real.log p+
          (3+4*(M:ℝ))*Real.log p) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨hmem,hpp⟩ := Finset.mem_filter.mp hp
    have hb := outer_prime_cell_bound n M p i ha hpp hmem
    have hl : 0≤Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hpp.one_le)
    nlinarith [mul_le_mul_of_nonneg_right hb hl]
  have hlogs : (∑ p ∈ Finset.Ioc ⌊(K n:ℝ)/3⌋₊ ⌊(37/20:ℝ)*(K n:ℝ)⌋₊ with p.Prime,
      Real.log p) ≤ Chebyshev.theta ((37/20:ℝ)*(K n:ℝ)) := by
    rw [Chebyshev.theta_eq_sum_Icc]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hp,hpp⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _,(Finset.mem_Ioc.mp hp).2⟩,hpp⟩
    · intro p hp hnot
      exact Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_le)
  calc
    _ ≤ _ := hle
    _ = outerPrimeModel (K n:ℝ)+(3+4*(M:ℝ))*
        (∑ i : Fin 11, ∑ p ∈ Finset.Ioc ⌊(outerCellLeft i:ℝ)*(K n:ℝ)⌋₊
          ⌊(outerCellRight i:ℝ)*(K n:ℝ)⌋₊ with p.Prime, Real.log p) := by
      simp only [Finset.sum_add_distrib,←Finset.mul_sum,outerPrimeModel]
    _ = outerPrimeModel (K n:ℝ)+(3+4*(M:ℝ))*
        (∑ p ∈ Finset.Ioc ⌊(K n:ℝ)/3⌋₊ ⌊(37/20:ℝ)*(K n:ℝ)⌋₊ with p.Prime, Real.log p) := by
      rw [outer_prime_partition _ hk]
    _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left hlogs hc) _

#print axioms outerLocalSum_le_model
end Zeta5OuterAsymptotics
