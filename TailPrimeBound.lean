import PrimeRangePartition
import PrimeKernelMajorant
import OuterPrimeUpperLimit
import ScalarUniform

noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators
namespace Zeta5InnerAsymptotics
open Zeta5Parameters Zeta5PrimeSums

def tailErrorConstant (M : ℕ) : ℝ := 1000*((M:ℝ)+1)^2+4*(M:ℝ)

def tailPrimeModel (K : ℝ) (M : ℕ) : ℝ :=
  ∑ p∈Finset.Ioc ⌊K/(M:ℝ)⌋₊ ⌊K/20⌋₊ with p.Prime,
    (p:ℝ)*Zeta5RealKernel.tailMajorant (K/p)*Real.log p

lemma tail_prime_bound (n M p : ℕ) (ha : Admissible n M) (hpp : p.Prime)
    (hmem : p∈Finset.Ioc ⌊(K n:ℝ)/(M:ℝ)⌋₊ ⌊(K n:ℝ)/20⌋₊) :
    -(localExponent n M p:ℝ)-(p:ℝ)/2≤
      (p:ℝ)*Zeta5RealKernel.tailMajorant ((K n:ℝ)/p)+tailErrorConstant M := by
  letI : Fact p.Prime := ⟨hpp⟩
  have hm : (0:ℝ)<M := by exact_mod_cast (show 0<M from by have := ha.1; omega)
  obtain ⟨hlo,hhi⟩ := Finset.mem_Ioc.mp hmem
  have hloR := Nat.lt_of_floor_lt hlo
  have hhiR := (Nat.le_floor_iff' hpp.ne_zero).mp hhi
  have hcutR := (div_lt_iff₀ hm).mp hloR
  have hcut : K n<p*M := by exact_mod_cast hcutR
  have hinnerR : (3:ℝ)*p≤K n := by
    have hp0 : (0:ℝ)≤p := by positivity
    have hh := (le_div_iff₀ (by norm_num : (0:ℝ)<20)).mp hhiR
    nlinarith
  have hinner : 3*p≤K n := by exact_mod_cast hinnerR
  have hb := actual_inner_localExponent_upper n M p ha hcut hinner
  have hbR : -(localExponent n M p:ℝ) ≤
      (p:ℝ)*(innerKernel ((K n:ℚ)/p):ℝ)+(p:ℝ)/2+
        1000*((M:ℝ)+1)^2+4*(M:ℝ) := by
    have hh := (Rat.cast_le (K:=ℝ)).mpr hb
    push_cast at hh
    exact hh
  rw [Zeta5RealKernel.kernel_rat_cast] at hbR
  simp only [Rat.cast_div,Rat.cast_natCast] at hbR
  have hmajor : Zeta5RealKernel.kernel ((K n:ℝ)/p)≤
      Zeta5RealKernel.tailMajorant ((K n:ℝ)/p) := by
    rw [Zeta5RealKernel.kernel_decomposition]
    exact add_le_add_right (Zeta5RealKernel.remainder_bounds _).2 _
  have hh := mul_le_mul_of_nonneg_left hmajor (show (0:ℝ)≤p by positivity)
  unfold tailErrorConstant
  linarith

lemma tailCorrectedLocalSum_le_model (n M : ℕ) (ha : Admissible n M) :
    tailCorrectedLocalSum n M≤tailPrimeModel (K n:ℝ) M+
      tailErrorConstant M*Chebyshev.theta ((K n:ℝ)/20) := by
  have hc : 0≤tailErrorConstant M := by unfold tailErrorConstant; positivity
  have hle : tailCorrectedLocalSum n M≤
      ∑p∈Finset.Ioc ⌊(K n:ℝ)/(M:ℝ)⌋₊ ⌊(K n:ℝ)/20⌋₊ with p.Prime,
        ((p:ℝ)*Zeta5RealKernel.tailMajorant ((K n:ℝ)/p)*Real.log p+
          tailErrorConstant M*Real.log p) := by
    unfold tailCorrectedLocalSum
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨hmem,hpp⟩ := Finset.mem_filter.mp hp
    have hb := tail_prime_bound n M p ha hpp hmem
    have hl : 0≤Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hpp.one_le)
    nlinarith [mul_le_mul_of_nonneg_right hb hl]
  have hlogs : (∑p∈Finset.Ioc ⌊(K n:ℝ)/(M:ℝ)⌋₊ ⌊(K n:ℝ)/20⌋₊ with p.Prime,
      Real.log p)≤Chebyshev.theta ((K n:ℝ)/20) := by
    rw [Chebyshev.theta_eq_sum_Icc]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hp,hpp⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _,(Finset.mem_Ioc.mp hp).2⟩,hpp⟩
    · intro p hp _
      exact Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_le)
  calc
    _ ≤ _ := hle
    _ = tailPrimeModel (K n:ℝ) M+tailErrorConstant M*
        (∑p∈Finset.Ioc ⌊(K n:ℝ)/(M:ℝ)⌋₊ ⌊(K n:ℝ)/20⌋₊ with p.Prime,Real.log p) := by
      simp only [Finset.sum_add_distrib,←Finset.mul_sum,tailPrimeModel]
    _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left hlogs hc) _

lemma tail_model_with_error_tendsto (M : ℕ) (hM : 20≤M) :
    Tendsto (fun n : ℕ =>
      (tailPrimeModel (K n:ℝ) M+tailErrorConstant M*Chebyshev.theta ((K n:ℝ)/20))/(K n:ℝ)^2)
      atTop (𝓝 (∫ t in (20:ℝ)..(M:ℝ),Zeta5RealKernel.tailMajorant t/t^3)) := by
  have ht := tailMajorant_prime_sum_tendsto 20 (M:ℝ) (by norm_num) (by exact_mod_cast hM)
  have he := (theta_over_square_tendsto (by norm_num : (0:ℝ)<1/20)).const_mul
    (tailErrorConstant M)
  have h := (ht.add he).comp K_tendsto_atTop
  simp only [one_div_mul_eq_div,mul_zero,add_zero] at h
  convert h using 1
  funext n
  dsimp only [Function.comp_def,kernelPrimeSum,tailPrimeModel]
  ring

/-- The actual local-exponent contribution from K/M<p≤K/20 obeys the checked tail bound. -/
theorem tailCorrectedLocalSum_eventually_upper (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, tailCorrectedLocalSum n 100000/(K n:ℝ)^2≤
      -(6970198065777/125000000000000)+ε := by
  have hb := Zeta5RealKernel.tailMajorant_tail_upper
  have ht := (tail_model_with_error_tendsto 100000 (by norm_num)).eventually
    (gt_mem_nhds (by linarith :
      (∫ t in (20:ℝ)..100000,Zeta5RealKernel.tailMajorant t/t^3)<
        -(6970198065777/125000000000000)+ε))
  filter_upwards [eventually_admissible 100000 (by norm_num),ht] with n ha hn
  exact (div_le_div_of_nonneg_right (tailCorrectedLocalSum_le_model n 100000 ha)
    (sq_nonneg _)).trans hn.le

#print axioms tail_prime_bound
#print axioms tailCorrectedLocalSum_eventually_upper
end Zeta5InnerAsymptotics
