import PrimeSums

noncomputable section
open Filter Asymptotics MeasureTheory Set
open scoped Topology
namespace Zeta5PrimeSums
set_option maxHeartbeats 800000

lemma theta_harmonic_integral_tendsto (u v : ℝ) (hu : 0<u) (huv : u≤v) :
    Tendsto (fun x : ℝ => ∫ t in u..v, (Chebyshev.theta (x*t)/x)/t^2)
      atTop (𝓝 (Real.log (v/u))) := by
  have hv : 0<v := hu.trans_le huv
  have hlim : Tendsto (fun x : ℝ => ∫ t in u..v, (Chebyshev.theta (x*t)/x)/t^2)
      atTop (𝓝 (∫ t in u..v, (1:ℝ)/t)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun t : ℝ => Real.log 4/t)
    · exact Filter.Eventually.of_forall fun x =>
        ((((Chebyshev.theta_mono.measurable.comp (measurable_const.mul measurable_id)).div_const x).div
          (measurable_id.pow_const 2)).aestronglyMeasurable)
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
      apply Filter.Eventually.of_forall
      intro t ht
      have ht0 : 0<t := hu.trans (by simpa only [uIoc_of_le huv] using ht : t∈Ioc u v).1
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0≤(Chebyshev.theta (x*t)/x)/t^2)]
      have hθ := Chebyshev.theta_le_log4_mul_x (by positivity : 0≤x*t)
      apply (div_le_iff₀ (sq_pos_of_pos ht0)).mpr
      apply (div_le_iff₀ hx).mpr
      exact hθ.trans_eq (by field_simp)
    · exact ((continuousOn_const.div continuousOn_id (fun t ht =>
        ne_of_gt (hu.trans_le (uIcc_of_le huv ▸ ht).1))).intervalIntegrable)
    · apply Filter.Eventually.of_forall
      intro t ht
      have ht0 : 0<t := hu.trans (by simpa only [uIoc_of_le huv] using ht : t∈Ioc u v).1
      have h := (scaled_asymptotic_ratio chebyshev_asymptotic ht0).div_const (t^2)
      have he : t/t^2=(1:ℝ)/t := by field_simp
      simpa only [mul_comm, he] using h
  simpa only [integral_one_div_of_pos hu hv] using hlim

lemma prime_harmonic_abel (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    (∑ p ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ with p.Prime, Real.log p/(p:ℝ)) =
      Chebyshev.theta b/b-Chebyshev.theta a/a+
        ∫ t in a..b, Chebyshev.theta t/t^2 := by
  have hderiv (t : ℝ) (ht : t∈Icc a b) :
      HasDerivAt (fun t : ℝ => t⁻¹) (-(t^2)⁻¹) t := by
    exact hasDerivAt_inv (ne_of_gt (ha.trans_le ht.1))
  have hd : IntegrableOn (deriv (fun t : ℝ => t⁻¹)) (Icc a b) := by
    have hc : ContinuousOn (fun t : ℝ => -(t^2)⁻¹) (Icc a b) :=
      ((continuousOn_id.pow 2).inv₀ (fun t ht => pow_ne_zero _
        (ne_of_gt (ha.trans_le ht.1)))).neg
    apply hc.integrableOn_Icc.congr_fun
    · intro t ht
      exact (hderiv t ht).deriv.symm
    · exact measurableSet_Icc
  have h := sum_mul_eq_sub_sub_integral_mul
    (c:=fun n : ℕ => if n.Prime then Real.log n else 0)
    (f:=fun t : ℝ => t⁻¹) ha.le hab
    (fun t ht => (hderiv t ht).differentiableAt) hd
  simp only [mul_ite,mul_zero,←Finset.sum_filter,
    ←Chebyshev.theta_eq_sum_Icc] at h
  have hi : (∫ t in Ioc a b, deriv (fun t : ℝ => t⁻¹) t*Chebyshev.theta t) =
      -(∫ t in a..b, Chebyshev.theta t/t^2) := by
    rw [intervalIntegral.integral_of_le hab,←integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [(hderiv t (Ioc_subset_Icc_self ht)).deriv]
    simp only [neg_mul,mul_neg,div_eq_mul_inv,mul_comm]
  rw [hi] at h
  simpa only [div_eq_mul_inv,mul_comm,sub_neg_eq_add] using h

lemma prime_harmonic_sum_tendsto (u v : ℝ) (hu : 0<u) (huv : u≤v) :
    Tendsto (fun x : ℝ => ∑ p ∈ Finset.Ioc ⌊u*x⌋₊ ⌊v*x⌋₊ with p.Prime,
      Real.log p/(p:ℝ)) atTop (𝓝 (Real.log (v/u))) := by
  have hv : 0<v := hu.trans_le huv
  have hend (c : ℝ) (hc : 0<c) :
      Tendsto (fun x : ℝ => Chebyshev.theta (c*x)/(c*x)) atTop (𝓝 1) := by
    have h := (scaled_asymptotic_ratio chebyshev_asymptotic hc).div_const c
    simpa only [div_div, mul_comm, div_self hc.ne'] using h
  have h := ((hend v hv).sub (hend u hu)).add (theta_harmonic_integral_tendsto u v hu huv)
  simp only [sub_self,zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  rw [prime_harmonic_abel (u*x) (v*x) (by positivity) (mul_le_mul_of_nonneg_right huv hx.le)]
  congr 1
  rw [mul_comm u x,mul_comm v x,←intervalIntegral.smul_integral_comp_mul_left _ x]
  simp only [smul_eq_mul]
  rw [←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht0 : 0<t := hu.trans_le (by simpa only [uIcc_of_le huv] using ht : t∈Icc u v).1
  field_simp

#print axioms prime_harmonic_sum_tendsto
end Zeta5PrimeSums
