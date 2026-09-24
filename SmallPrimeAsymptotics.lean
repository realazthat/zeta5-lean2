import OuterPrimeUpperLimit

noncomputable section
open Filter Asymptotics
open scoped BigOperators Topology
namespace Zeta5SmallPrimeAsymptotics
open Zeta5Parameters Zeta5PrimeSums
set_option maxHeartbeats 1000000

/-- Literal small-prime contribution to the logarithm of the normalizer. -/
def smallLocalSum (n M : ℕ) : ℝ :=
  ∑ p ∈ Finset.Icc 0 ⌊(K n:ℝ)/(M:ℝ)⌋₊ with p.Prime,
    (-(localExponent n M p:ℝ))*Real.log p

def val24Cost : ℝ :=
  ∑ p ∈ Finset.Icc 0 24 with p.Prime, (padicValNat p 24:ℝ)*Real.log p

lemma val24_sum_le (B : ℕ) :
    (∑ p ∈ Finset.Icc 0 B with p.Prime, (padicValNat p 24:ℝ)*Real.log p) ≤ val24Cost := by
  let S := (Finset.Icc 0 B).filter Nat.Prime
  have he : (∑p∈S.filter (fun p => p≤24), (padicValNat p 24:ℝ)*Real.log p) =
      ∑p∈S, (padicValNat p 24:ℝ)*Real.log p := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hn
    have hgt : 24<p := by simpa only [Finset.mem_filter,hp,true_and,not_le] using hn
    rw [padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt (by norm_num) hgt)]
    simp
  change (∑p∈S, (padicValNat p 24:ℝ)*Real.log p)≤_
  rw [←he]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    have hh := Finset.mem_filter.mp hp
    have hpprime := (Finset.mem_filter.mp hh.1).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _,hh.2⟩,hpprime⟩
  · intro p hp hn
    have hpprime := (Finset.mem_filter.mp hp).2
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hpprime.one_le))

lemma nat_log_mul_log_le (p X : ℕ) (hp : p.Prime) (hX : X≠0) :
    (Nat.log p X:ℝ)*Real.log p ≤ Real.log X := by
  rw [←Real.log_pow]
  apply Real.log_le_log (pow_pos (by exact_mod_cast hp.pos) _)
  exact_mod_cast Nat.pow_log_le_self p hX

lemma smallLocalSum_le_model (n M : ℕ) (hn : 0<n) (hM : 0<M) :
    smallLocalSum n M ≤
      6*(h n:ℝ)*(Nat.primeCounting ⌊(K n:ℝ)/(M:ℝ)⌋₊:ℝ)*Real.log (5*(K n:ℝ))+
      (h n:ℝ)*val24Cost := by
  have hm : (0:ℝ)<M := by exact_mod_cast hM
  have hK : 0<K n := by unfold K; omega
  have he : smallLocalSum n M =
      6*(h n:ℝ)*(∑p∈Finset.Icc 0 ⌊(K n:ℝ)/(M:ℝ)⌋₊ with p.Prime,
        (Nat.log p (5*K n):ℝ)*Real.log p)+
      (h n:ℝ)*(∑p∈Finset.Icc 0 ⌊(K n:ℝ)/(M:ℝ)⌋₊ with p.Prime,
        (padicValNat p 24:ℝ)*Real.log p) := by
    unfold smallLocalSum
    rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    have hpbound := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
    have hpreal : (p:ℝ)≤(K n:ℝ)/(M:ℝ) := (Nat.le_floor_iff (by positivity)).mp hpbound
    have hsmall : p*M≤K n := by exact_mod_cast (le_div_iff₀ hm).mp hpreal
    rw [localExponent,if_pos hsmall]
    simp only [Int.cast_sub,Int.cast_mul,Int.cast_neg,Int.cast_natCast,Int.cast_ofNat]
    ring
  rw [he]
  apply add_le_add
  · have hs : (∑p∈Finset.Icc 0 ⌊(K n:ℝ)/(M:ℝ)⌋₊ with p.Prime,
        (Nat.log p (5*K n):ℝ)*Real.log p) ≤
        (Nat.primeCounting ⌊(K n:ℝ)/(M:ℝ)⌋₊:ℝ)*Real.log (5*(K n:ℝ)) := by
      calc
        _ ≤ ∑p∈Finset.Icc 0 ⌊(K n:ℝ)/(M:ℝ)⌋₊ with p.Prime, Real.log (5*(K n:ℝ)) := by
          apply Finset.sum_le_sum
          intro p hp
          simpa only [Nat.cast_mul,Nat.cast_ofNat] using
            nat_log_mul_log_le p (5*K n) (Finset.mem_filter.mp hp).2 (by omega)
        _ = _ := by
          rw [Finset.sum_const,←Nat.primesLE_eq_filter_Icc_zero,
            Nat.primesLE_card_eq_primeCounting,nsmul_eq_mul]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs (by positivity : 0≤6*(h n:ℝ))
  · exact mul_le_mul_of_nonneg_left (val24_sum_le _) (Nat.cast_nonneg _)

lemma log_scale_ratio_tendsto (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    Tendsto (fun x : ℝ => Real.log (a*x)/Real.log (b*x)) atTop (𝓝 1) := by
  have hbtop : Tendsto (fun x : ℝ => Real.log (b*x)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_id.const_mul_atTop hb)
  have ht := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1:ℝ)) atTop (𝓝 1)).add
    ((tendsto_const_nhds : Tendsto (fun _ : ℝ => Real.log (a/b)) atTop (𝓝 (Real.log (a/b)))).div_atTop hbtop)
  simp only [add_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ),hbtop.eventually (eventually_ne_atTop 0)] with x hx hlog
  have he : a*x=(a/b)*(b*x) := by field_simp
  rw [he,Real.log_mul (div_ne_zero ha.ne' hb.ne') (mul_ne_zero hb.ne' hx.ne')]
  field_simp
  ring

lemma primeCounting_log_tendsto (M : ℝ) (hM : 0<M) :
    Tendsto (fun x : ℝ => (Nat.primeCounting ⌊x/M⌋₊:ℝ)*Real.log (5*x)/x)
      atTop (𝓝 (1/M)) := by
  obtain ⟨f,hf,hfeq⟩ := pi_alt
  have hf0 : Tendsto f atTop (𝓝 0) := (isLittleO_one_iff ℝ).mp hf
  have hxtop : Tendsto (fun x : ℝ => x/M) atTop atTop := tendsto_id.atTop_div_const hM
  have ht := (((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1:ℝ)) atTop (𝓝 1)).add (hf0.comp hxtop)).mul
    (log_scale_ratio_tendsto 5 (1/M) (by norm_num) (by positivity))).div_const M
  simp only [add_zero,one_mul] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  rw [hfeq]
  have he : (1/M)*x=x/M := by ring
  rw [he]
  field_simp
  simp only [Function.comp_def]
  ring

lemma small_model_tendsto (M : ℕ) (hM : 0<M) :
    Tendsto (fun n : ℕ =>
      (6*(h n:ℝ)*(Nat.primeCounting ⌊(K n:ℝ)/(M:ℝ)⌋₊:ℝ)*Real.log (5*(K n:ℝ))+
        (h n:ℝ)*val24Cost)/(K n:ℝ)^2)
      atTop (𝓝 (6*(37/40:ℝ)/(M:ℝ))) := by
  have hm : (0:ℝ)<M := by exact_mod_cast hM
  have hmain := ((primeCounting_log_tendsto (M:ℝ) hm).comp K_tendsto_atTop).const_mul (6*(37/40:ℝ))
  have herr := tendsto_const_nhds.div_atTop K_tendsto_atTop (a := (37/40:ℝ)*val24Cost)
  have ht := hmain.add herr
  simp only [add_zero] at ht
  have hce : 6*(37/40:ℝ)*(1/(M:ℝ))=6*(37/40:ℝ)/(M:ℝ) := by ring
  rw [hce] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  dsimp only [Function.comp_def]
  have hKn : (K n:ℝ)≠0 := by exact_mod_cast (show K n≠0 by unfold K; omega)
  have he : (h n:ℝ)=(37/40:ℝ)*(K n:ℝ) := by simp [h,K]; ring
  rw [he]
  field_simp [hKn]
  <;> ring

/-- The entire small-prime contribution costs at most 6λ/M asymptotically,
including the exceptional primes dividing 24. -/
theorem smallLocalSum_eventually_upper (M : ℕ) (hM : 40≤M) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,
      smallLocalSum n M/(K n:ℝ)^2 ≤ 6*(37/40:ℝ)/(M:ℝ)+ε := by
  have ht := (small_model_tendsto M (by omega)).eventually
    (gt_mem_nhds (by linarith : 6*(37/40:ℝ)/(M:ℝ)<6*(37/40:ℝ)/(M:ℝ)+ε))
  filter_upwards [eventually_gt_atTop (0:ℕ),ht] with n hn hmodel
  exact (div_le_div_of_nonneg_right (smallLocalSum_le_model n M hn (by omega))
    (sq_nonneg _)).trans hmodel.le

#print axioms smallLocalSum_eventually_upper
end Zeta5SmallPrimeAsymptotics
