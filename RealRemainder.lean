import RealNormalization

noncomputable section
open Filter
open scoped Topology

namespace Zeta5Construction

def realDeterminantRemainder (K : ℝ) : ℝ :=
  (37/40)*(Real.sqrt 2+Real.log 4096+18+Real.log 652)/K +
    (37/40)*(Real.log (K+1)/K)+(22*(37/40))*(Real.log K/K)

lemma realDeterminantRemainder_tendsto :
    Tendsto realDeterminantRemainder atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x/x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hlog' : Tendsto (fun x : ℝ => Real.log (x+1)/x) atTop (𝓝 0) := by
    have hs : Tendsto (fun x : ℝ => x+1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_id
    have hh := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp hs
    simpa only [Function.comp_def, pow_one, one_mul, add_neg_cancel_right] using hh
  have hc := (tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop).const_div_atTop
    ((37/40)*(Real.sqrt 2+Real.log 4096+18+Real.log 652))
  unfold realDeterminantRemainder
  simpa only [id_eq, mul_zero, add_zero] using
    (hc.add (hlog'.const_mul (37/40))).add (hlog.const_mul (22*(37/40)))

lemma forty_mul_nat_tendsto :
    Tendsto (fun n : ℕ => (40*n:ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)

lemma realDeterminantRemainder_nat_tendsto :
    Tendsto (fun n : ℕ => realDeterminantRemainder (40*n)) atTop (𝓝 0) :=
  realDeterminantRemainder_tendsto.comp forty_mul_nat_tendsto

end Zeta5Construction

