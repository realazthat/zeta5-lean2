import PrimeFloor
import FloorIntegral
import InnerTailBound

noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace Zeta5PrimeSums
set_option maxHeartbeats 800000

def kernelPrimeSum (a b : ℝ) (f : ℝ→ℝ) (K : ℝ) : ℝ :=
  (∑ p ∈ Finset.Ioc ⌊K/b⌋₊ ⌊K/a⌋₊ with p.Prime,
    (p:ℝ)*f (K/p)*Real.log p)/K^2

lemma kernelPrimeSum_add (a b : ℝ) (f g : ℝ→ℝ) (K : ℝ) :
    kernelPrimeSum a b (fun t => f t+g t) K = kernelPrimeSum a b f K+kernelPrimeSum a b g K := by
  simp only [kernelPrimeSum,mul_add,add_mul,Finset.sum_add_distrib,add_div]
lemma kernelPrimeSum_sub (a b : ℝ) (f g : ℝ→ℝ) (K : ℝ) :
    kernelPrimeSum a b (fun t => f t-g t) K = kernelPrimeSum a b f K-kernelPrimeSum a b g K := by
  simp only [kernelPrimeSum,mul_sub,sub_mul,Finset.sum_sub_distrib,sub_div]
lemma kernelPrimeSum_const_mul (a b c : ℝ) (f : ℝ→ℝ) (K : ℝ) :
    kernelPrimeSum a b (fun t => c*f t) K = c*kernelPrimeSum a b f K := by
  unfold kernelPrimeSum
  rw [←mul_div_assoc,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  ring

lemma kernelPrimeSum_linear (a b c K : ℝ) :
    kernelPrimeSum a b (fun t => c*t) K = c*kernelPrimeSum a b id K :=
  kernelPrimeSum_const_mul a b c id K
lemma kernelPrimeSum_const (a b c K : ℝ) :
    kernelPrimeSum a b (fun _ => c) K = c*kernelPrimeSum a b (fun _ => 1) K := by
  simpa only [mul_one] using kernelPrimeSum_const_mul a b c (fun _ => 1) K

lemma kernelPrimeSum_id_tendsto (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    Tendsto (kernelPrimeSum a b id) atTop (𝓝 (1/a-1/b)) := by
  unfold kernelPrimeSum
  simpa only [id_eq,one_mul,add_zero,zero_mul,zero_div] using
    reciprocal_affine_prime_sum_tendsto chebyshev_asymptotic 1 0 a b ha hab

lemma kernelPrimeSum_one_tendsto (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    Tendsto (kernelPrimeSum a b (fun _ => 1)) atTop (𝓝 (((1/a)^2-(1/b)^2)/2)) := by
  unfold kernelPrimeSum
  simpa only [id_eq,one_mul,zero_add,zero_mul,mul_one] using
    reciprocal_affine_prime_sum_tendsto chebyshev_asymptotic 0 1 a b ha hab

lemma kernelPrimeSum_square_tendsto (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    Tendsto (kernelPrimeSum a b (fun t => t^2)) atTop (𝓝 (Real.log (b/a))) := by
  have hb : 0<b := ha.trans_le hab
  have h := prime_harmonic_sum_tendsto (1/b) (1/a) (one_div_pos.mpr hb)
    (one_div_le_one_div_of_le ha hab)
  have hlog : (1/a)/(1/b)=b/a := by field_simp
  rw [hlog] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with K hK
  unfold kernelPrimeSum
  simp only [one_div_mul_eq_div]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  have hp0 : (p:ℝ)≠0 := by exact_mod_cast (Finset.mem_filter.mp hp).2.ne_zero
  field_simp

lemma kernelPrimeSum_floor_tendsto (a b c : ℝ) (ha : 0<a) (hab : a≤b) (hc : 0≤c) :
    Tendsto (kernelPrimeSum a b (fun t => t*(⌊c*t⌋:ℝ))) atTop
      (𝓝 (floorPrimeConstant a b c)) := by
  apply (floor_prime_sum_tendsto a b c ha hab hc).congr'
  apply Filter.Eventually.of_forall
  intro K
  unfold kernelPrimeSum
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  have hp0 : (p:ℝ)≠0 := by exact_mod_cast (Finset.mem_filter.mp hp).2.ne_zero
  field_simp

lemma tailMajorant_expansion (t : ℝ) : Zeta5RealKernel.tailMajorant t =
    (407/400:ℝ)*t^2+(37/10)*t+(13/8)-(37/20)*(t*(⌊t⌋:ℝ))+
      (111/10)*(t*(⌊(3/40)*t⌋:ℝ)) := by
  unfold Zeta5RealKernel.tailMajorant Zeta5RealKernel.linearPart Int.fract
  ring

def tailMajorantPrimeConstant (a b : ℝ) : ℝ :=
  (407/400)*Real.log (b/a)+(37/10)*(1/a-1/b)+
  (13/8)*(((1/a)^2-(1/b)^2)/2)-(37/20)*floorPrimeConstant a b 1+
  (111/10)*floorPrimeConstant a b (3/40)

lemma tailMajorant_prime_sum_constant_tendsto (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    Tendsto (kernelPrimeSum a b Zeta5RealKernel.tailMajorant) atTop
      (𝓝 (tailMajorantPrimeConstant a b)) := by
  have h := (((((kernelPrimeSum_square_tendsto a b ha hab).const_mul (407/400)).add
    ((kernelPrimeSum_id_tendsto a b ha hab).const_mul (37/10))).add
    ((kernelPrimeSum_one_tendsto a b ha hab).const_mul (13/8))).sub
    ((kernelPrimeSum_floor_tendsto a b 1 ha hab (by norm_num)).const_mul (37/20))).add
    ((kernelPrimeSum_floor_tendsto a b (3/40) ha hab (by norm_num)).const_mul (111/10))
  change Tendsto _ atTop (𝓝 (tailMajorantPrimeConstant a b)) at h
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro K
  have he : Zeta5RealKernel.tailMajorant = (fun t : ℝ =>
      (407/400)*t^2+(37/10)*t+(13/8)-(37/20)*(t*(⌊t⌋:ℝ))+
      (111/10)*(t*(⌊(3/40)*t⌋:ℝ))) := funext tailMajorant_expansion
  rw [he]
  simp only [kernelPrimeSum_add,kernelPrimeSum_sub,kernelPrimeSum_const_mul,kernelPrimeSum_linear,one_mul,id_eq]
  rw [kernelPrimeSum_const a b (13/8) K]

lemma tailMajorantPrimeConstant_eq_integral (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    tailMajorantPrimeConstant a b = ∫ t in a..b, Zeta5RealKernel.tailMajorant t/t^3 := by
  have hb : 0<b := ha.trans_le hab
  have hn (n : ℕ) : IntervalIntegrable (fun t : ℝ => 1/t^n) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div (continuousOn_id.pow n)
    intro t ht
    exact pow_ne_zero _ (ne_of_gt (ha.trans_le (uIcc_of_le hab ▸ ht).1))
  have h1 := hn 1
  simp only [pow_one] at h1
  have h2 := hn 2
  have h3 := hn 3
  have hf1 := Zeta5RealKernel.floor_div_square_intervalIntegrable a b 1 ha hab (by norm_num)
  simp only [one_mul] at hf1
  have hf3 := Zeta5RealKernel.floor_div_square_intervalIntegrable a b (3/40) ha hab (by norm_num)
  have he : (fun t : ℝ => Zeta5RealKernel.tailMajorant t/t^3) =
      (fun t : ℝ => (407/400)*(1/t)+(37/10)*(1/t^2)+(13/8)*(1/t^3)-
        (37/20)*((⌊t⌋:ℝ)/t^2)+(111/10)*((⌊(3/40)*t⌋:ℝ)/t^2)) := by
    funext t
    rw [tailMajorant_expansion]
    by_cases ht : t=0
    · simp [ht]
    · field_simp
  rw [he,
    intervalIntegral.integral_add
      ((((h1.const_mul (407/400)).add (h2.const_mul (37/10))).add
        (h3.const_mul (13/8))).sub (hf1.const_mul (37/20))) (hf3.const_mul (111/10)),
    intervalIntegral.integral_sub
      (((h1.const_mul (407/400)).add (h2.const_mul (37/10))).add
        (h3.const_mul (13/8))) (hf1.const_mul (37/20)),
    intervalIntegral.integral_add
      ((h1.const_mul (407/400)).add (h2.const_mul (37/10))) (h3.const_mul (13/8)),
    intervalIntegral.integral_add (h1.const_mul (407/400)) (h2.const_mul (37/10))]
  simp only [intervalIntegral.integral_const_mul]
  have hi3 := affine_kernel_integral 0 1 a b ha hb
  simp only [zero_mul,zero_add,one_mul] at hi3
  have hf1eq := Zeta5RealKernel.floor_div_square_integral a b 1 ha hab (by norm_num)
  simp only [one_mul] at hf1eq
  rw [integral_one_div_of_pos ha hb,Zeta5RealKernel.inverse_square_integral a b ha hb,
    hi3,hf1eq,Zeta5RealKernel.floor_div_square_integral a b (3/40) ha hab (by norm_num)]
  simp only [tailMajorantPrimeConstant,floorPrimeConstant,floorPrimeCut,one_mul]

/-- Exact compact-tail PNT limit for the floor majorant, without enumerating its jumps. -/
theorem tailMajorant_prime_sum_tendsto (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    Tendsto (kernelPrimeSum a b Zeta5RealKernel.tailMajorant) atTop
      (𝓝 (∫ t in a..b, Zeta5RealKernel.tailMajorant t/t^3)) := by
  rw [←tailMajorantPrimeConstant_eq_integral a b ha hab]
  exact tailMajorant_prime_sum_constant_tendsto a b ha hab

#print axioms tailMajorant_prime_sum_tendsto

end Zeta5PrimeSums
