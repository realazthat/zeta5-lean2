import InnerPrimeLimit
import OuterPrimeUpperLimit
import ScalarUniform

noncomputable section
open Filter Asymptotics
open scoped BigOperators Topology
namespace Zeta5InnerAsymptotics
open Zeta5Parameters

def innerErrorConstant (M : ℕ) : ℝ := 1000*((M:ℝ)+1)^2+4*(M:ℝ)

theorem inner_prime_cell_bound (n M p : ℕ) (i : Fin 143)
    (ha : Admissible n M) (hpp : p.Prime)
    (hmem : p ∈ Finset.Ioc ⌊(K n:ℝ)/(innerCellRight i:ℝ)⌋₊
      ⌊(K n:ℝ)/(innerCellLeft i:ℝ)⌋₊) :
    -(localExponent n M p:ℝ)-(p:ℝ)/2 ≤
      (innerCellSlope i:ℝ)*(K n:ℝ)+(innerCellConstant i:ℝ)*(p:ℝ)+innerErrorConstant M := by
  letI : Fact p.Prime := ⟨hpp⟩
  have hpq : (0:ℚ)<p := by exact_mod_cast hpp.pos
  have hlq : (0:ℚ)< innerCellLeft i := lt_of_lt_of_le (by norm_num) (innerCell_bounds i).1
  have hrq : (0:ℚ)< innerCellRight i := hlq.trans_le (innerCell_bounds i).2.1
  obtain ⟨hlo,hhi⟩ := Finset.mem_Ioc.mp hmem
  have hloR := Nat.lt_of_floor_lt hlo
  have hhiR := (Nat.le_floor_iff' hpp.ne_zero).mp hhi
  have hloQ : (K n:ℚ)/innerCellRight i<(p:ℚ) := by exact_mod_cast hloR
  have hhiQ : (p:ℚ)≤(K n:ℚ)/innerCellLeft i := by exact_mod_cast hhiR
  have hl : innerCellLeft i≤(K n:ℚ)/(p:ℚ) := by
    apply (le_div_iff₀ hpq).mpr
    have := (le_div_iff₀ hlq).mp hhiQ
    nlinarith
  have hr : (K n:ℚ)/(p:ℚ)< innerCellRight i := by
    apply (div_lt_iff₀ hpq).mpr
    have := (div_lt_iff₀ hrq).mp hloQ
    nlinarith
  have hi : 3*p≤K n := by
    have h3 := (innerCell_bounds i).1.trans hl
    have hh := (le_div_iff₀ hpq).mp h3
    exact_mod_cast hh
  have hc : K n<p*M := by
    have h20 := hr.trans_le (innerCell_bounds i).2.2
    have hh := (div_lt_iff₀ hpq).mp h20
    have hm : (20:ℚ)≤M := by exact_mod_cast (show 20≤M from by have := ha.1; omega)
    have hq : (K n:ℚ)<(p:ℚ)*(M:ℚ) := by nlinarith
    exact_mod_cast hq
  have hb := actual_inner_localExponent_upper n M p ha hc hi
  rw [innerKernel_on_cells i _ hl hr] at hb
  have he : (p:ℚ)*(innerCellSlope i*((K n:ℚ)/(p:ℚ))+innerCellConstant i)=
      innerCellSlope i*(K n:ℚ)+innerCellConstant i*(p:ℚ) := by field_simp
  rw [he] at hb
  unfold innerErrorConstant
  have hh : -(localExponent n M p:ℚ)-(p:ℚ)/2≤
      innerCellSlope i*(K n:ℚ)+innerCellConstant i*(p:ℚ)+1000*((M:ℚ)+1)^2+4*(M:ℚ) := by linarith
  have hhR : ((-(localExponent n M p:ℚ)-(p:ℚ)/2:ℚ):ℝ)≤
      ((innerCellSlope i*(K n:ℚ)+innerCellConstant i*(p:ℚ)+1000*((M:ℚ)+1)^2+4*(M:ℚ):ℚ):ℝ) :=
    Rat.cast_le.mpr hh
  push_cast at hhR
  linarith only [hhR]

def innerCorrectedLocalSum (n M : ℕ) : ℝ :=
  ∑ p ∈ Finset.Ioc ⌊(K n:ℝ)/20⌋₊ ⌊(K n:ℝ)/3⌋₊ with p.Prime,
    (-(localExponent n M p:ℝ)-(p:ℝ)/2)*Real.log p

theorem innerCorrectedLocalSum_le_model (n M : ℕ) (ha : Admissible n M) :
    innerCorrectedLocalSum n M ≤ innerPrimeModel (K n:ℝ)+
      innerErrorConstant M*Chebyshev.theta ((K n:ℝ)/3) := by
  have hk : (0:ℝ)≤K n := by positivity
  have hc : (0:ℝ)≤ innerErrorConstant M := by unfold innerErrorConstant; positivity
  unfold innerCorrectedLocalSum
  rw [←inner_prime_partition _ hk]
  have hle : (∑ i : Fin 143, ∑ p ∈ Finset.Ioc ⌊(K n:ℝ)/(innerCellRight i:ℝ)⌋₊
      ⌊(K n:ℝ)/(innerCellLeft i:ℝ)⌋₊ with p.Prime,
      (-(localExponent n M p:ℝ)-(p:ℝ)/2)*Real.log p) ≤
      ∑ i : Fin 143, ∑ p ∈ Finset.Ioc ⌊(K n:ℝ)/(innerCellRight i:ℝ)⌋₊
        ⌊(K n:ℝ)/(innerCellLeft i:ℝ)⌋₊ with p.Prime,
        (((innerCellSlope i:ℝ)*(K n:ℝ)+(innerCellConstant i:ℝ)*(p:ℝ))*Real.log p+
          innerErrorConstant M*Real.log p) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨hmem,hpp⟩ := Finset.mem_filter.mp hp
    have hb := inner_prime_cell_bound n M p i ha hpp hmem
    have hl : 0≤Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hpp.one_le)
    nlinarith [mul_le_mul_of_nonneg_right hb hl]
  have hlogs : (∑ p ∈ Finset.Ioc ⌊(K n:ℝ)/20⌋₊ ⌊(K n:ℝ)/3⌋₊ with p.Prime,
      Real.log p) ≤ Chebyshev.theta ((K n:ℝ)/3) := by
    rw [Chebyshev.theta_eq_sum_Icc]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hp,hpp⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _,(Finset.mem_Ioc.mp hp).2⟩,hpp⟩
    · intro p hp hnot
      exact Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_le)
  calc
    _ ≤ _ := hle
    _ = innerPrimeModel (K n:ℝ)+innerErrorConstant M*
        (∑ i : Fin 143, ∑ p ∈ Finset.Ioc ⌊(K n:ℝ)/(innerCellRight i:ℝ)⌋₊
          ⌊(K n:ℝ)/(innerCellLeft i:ℝ)⌋₊ with p.Prime, Real.log p) := by
      simp only [Finset.sum_add_distrib,←Finset.mul_sum,innerPrimeModel]
    _ = innerPrimeModel (K n:ℝ)+innerErrorConstant M*
        (∑ p ∈ Finset.Ioc ⌊(K n:ℝ)/20⌋₊ ⌊(K n:ℝ)/3⌋₊ with p.Prime, Real.log p) := by
      rw [inner_prime_partition _ hk]
    _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left hlogs hc) _

theorem inner_model_with_error_tendsto (M : ℕ) :
    Tendsto (fun n : ℕ =>
      (innerPrimeModel (K n:ℝ)+innerErrorConstant M*Chebyshev.theta ((K n:ℝ)/3))/(K n:ℝ)^2)
      atTop (𝓝 ((322437603634266857629:ℝ)/7535670527041937280000)) := by
  have h := innerPrimeModel_tendsto.add
    ((Zeta5PrimeSums.theta_over_square_tendsto (by norm_num : (0:ℝ)<1/3)).const_mul (innerErrorConstant M))
  have h' := h.comp K_tendsto_atTop
  simp only [one_div_mul_eq_div] at h'
  convert h' using 1
  · funext n
    dsimp only [Function.comp_def]
    ring
  · simp

theorem innerCorrectedLocalSum_eventually_upper (M : ℕ) (hM : 40≤M) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, innerCorrectedLocalSum n M/(K n:ℝ)^2≤
      322437603634266857629/7535670527041937280000+ε := by
  have ht := (inner_model_with_error_tendsto M).eventually (gt_mem_nhds (by linarith :
    (322437603634266857629:ℝ)/7535670527041937280000<322437603634266857629/7535670527041937280000+ε))
  filter_upwards [eventually_admissible M hM,ht] with n ha hn
  exact (div_le_div_of_nonneg_right (innerCorrectedLocalSum_le_model n M ha) (sq_nonneg _)).trans hn.le

#print axioms innerCorrectedLocalSum_eventually_upper
end Zeta5InnerAsymptotics
