import FloorIndicators
import PrimeHarmonic

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace Zeta5RealKernel
set_option maxHeartbeats 800000

lemma inverse_square_intervalIntegrable (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    IntervalIntegrable (fun t : ℝ => 1/t^2) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_const.div (continuousOn_id.pow 2)
  intro t ht
  exact pow_ne_zero _ (ne_of_gt (ha.trans_le (uIcc_of_le hab ▸ ht).1))

lemma inverse_square_integral (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    (∫ t in a..b, (1:ℝ)/t^2)=1/a-1/b := by
  have h := Zeta5PrimeSums.affine_kernel_integral 1 0 a b ha hb
  have he : (fun t : ℝ => (1*t+0)/t^3)=(fun t : ℝ => 1/t^2) := by
    funext t
    by_cases ht : t=0
    · simp [ht]
    · field_simp; ring
  rw [he] at h
  simpa only [one_mul,zero_mul,zero_div,add_zero] using h

lemma floor_indicator_intervalIntegrable (a b c j : ℝ) (ha : 0<a) (hab : a≤b) :
    IntervalIntegrable (fun t => (if j≤c*t then (1:ℝ) else 0)/t^2) volume a b := by
  have he : (fun t : ℝ => (if j≤c*t then (1:ℝ) else 0)/t^2) =
      {t : ℝ | j≤c*t}.indicator (fun t => 1/t^2) := by
    funext t
    simp only [Set.indicator,Set.mem_setOf_eq]
    split_ifs <;> simp
  rw [he]
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
  exact (inverse_square_intervalIntegrable a b ha hab).1.indicator
    (measurableSet_le measurable_const (measurable_const.mul measurable_id))

lemma floor_indicator_integral (a b c j : ℝ) (ha : 0<a) (hab : a≤b)
    (hc : 0<c) (hj : 0<j) (hjb : j≤c*b) :
    (∫ t in a..b, (if j≤c*t then (1:ℝ) else 0)/t^2) =
      max (1/b) (min (1/a) (c/j))-1/b := by
  have hb : 0<b := ha.trans_le hab
  have hd : 0<j/c := div_pos hj hc
  have hdb : j/c≤b := (div_le_iff₀ hc).mpr (by simpa only [mul_comm] using hjb)
  have he : (fun t : ℝ => (if j≤c*t then (1:ℝ) else 0)/t^2) =
      (Ici (j/c)).indicator (fun t => 1/t^2) := by
    funext t
    simp only [Set.indicator,mem_Ici]
    simp only [div_le_iff₀ hc,mul_comm t c]
    split_ifs <;> simp
  rw [he,intervalIntegral.integral_of_le hab,setIntegral_indicator measurableSet_Ici]
  have hrec : 1/(j/c)=c/j := by field_simp
  rcases le_total (j/c) a with h | h
  · have hs : Ioc a b∩Ici (j/c)=Ioc a b := by
      ext t
      simp only [mem_inter_iff,mem_Ioc,mem_Ici]
      constructor
      · exact And.left
      · intro ht
        exact ⟨ht,h.trans ht.1.le⟩
    rw [hs,←intervalIntegral.integral_of_le hab,inverse_square_integral a b ha hb]
    have hmin : 1/a≤c/j := by rw [←hrec]; exact one_div_le_one_div_of_le hd h
    rw [min_eq_left hmin,max_eq_right (one_div_le_one_div_of_le ha hab)]
  · have hs : Ioc a b∩Ici (j/c)=Icc (j/c) b ∩ Ioi a := by
      ext t
      simp only [mem_inter_iff,mem_Ioc,mem_Icc,mem_Ici,mem_Ioi]
      tauto
    have hs' : ∫ t in Ioc a b∩Ici (j/c), (1:ℝ)/t^2 =
        ∫ t in Ioc (j/c) b, (1:ℝ)/t^2 := by
      by_cases heq : j/c=a
      · subst a
        have heSet : Ioc (j/c) b ∩ Ici (j/c) = Ioc (j/c) b := by
          ext t
          simp only [mem_inter_iff,mem_Ioc,mem_Ici]
          constructor
          · exact And.left
          · intro ht; exact ⟨ht,ht.1.le⟩
        rw [heSet]
      · have hlt : a<j/c := lt_of_le_of_ne h (Ne.symm heq)
        have hx : Ioc a b∩Ici (j/c)=Icc (j/c) b := by
          ext t
          simp only [mem_inter_iff,mem_Ioc,mem_Ici,mem_Icc]
          constructor
          · intro ht
            exact ⟨ht.2,ht.1.2⟩
          · intro ht
            exact ⟨⟨hlt.trans_le ht.1,ht.2⟩,ht.1⟩
        rw [hx,integral_Icc_eq_integral_Ioc]
    rw [hs',←intervalIntegral.integral_of_le hdb,inverse_square_integral (j/c) b hd hb,hrec]
    have hmin : c/j≤1/a := by rw [←hrec]; exact one_div_le_one_div_of_le ha h
    have hmax : 1/b≤c/j := by rw [←hrec]; exact one_div_le_one_div_of_le hd hdb
    rw [min_eq_right hmin,max_eq_right hmax]

lemma floor_div_square_integral (a b c : ℝ) (ha : 0<a) (hab : a≤b) (hc : 0<c) :
    (∫ t in a..b, (⌊c*t⌋:ℝ)/t^2) =
      ∑ j ∈ Finset.Icc 1 ⌊c*b⌋₊, (max (1/b) (min (1/a) (c/(j:ℝ)))-1/b) := by
  calc
    _ = ∫ t in a..b, ∑ j ∈ Finset.Icc 1 ⌊c*b⌋₊,
        (if (j:ℝ)≤c*t then (1:ℝ) else 0)/t^2 := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t∈Icc a b := uIcc_of_le hab ▸ ht
      dsimp only
      rw [floor_scaled_finite_indicators c t b hc.le (ha.le.trans ht'.1) ht'.2,Finset.sum_div]
    _ = ∑ j ∈ Finset.Icc 1 ⌊c*b⌋₊, ∫ t in a..b,
        (if (j:ℝ)≤c*t then (1:ℝ) else 0)/t^2 := by
      rw [intervalIntegral.integral_finset_sum]
      intro j hj
      exact floor_indicator_intervalIntegrable a b c j ha hab
    _ = _ := by
      have hb : 0<b := ha.trans_le hab
      apply Finset.sum_congr rfl
      intro j hj
      obtain ⟨hj1,hjb⟩ := Finset.mem_Icc.mp hj
      apply floor_indicator_integral a b c j ha hab hc (by exact_mod_cast hj1)
      exact (Nat.le_floor_iff (by positivity : 0≤c*b)).mp hjb

lemma floor_div_square_intervalIntegrable (a b c : ℝ) (ha : 0<a) (hab : a≤b) (hc : 0≤c) :
    IntervalIntegrable (fun t => (⌊c*t⌋:ℝ)/t^2) volume a b := by
  have h := IntervalIntegrable.sum (Finset.Icc 1 ⌊c*b⌋₊) (fun j hj =>
    floor_indicator_intervalIntegrable a b c j ha hab)
  apply h.congr
  intro t ht
  have ht' : t∈Icc a b := Ioc_subset_Icc_self (uIoc_of_le hab ▸ ht)
  simp only [Finset.sum_apply]
  rw [floor_scaled_finite_indicators c t b hc (ha.le.trans ht'.1) ht'.2,Finset.sum_div]

#print axioms floor_div_square_integral
end Zeta5RealKernel
