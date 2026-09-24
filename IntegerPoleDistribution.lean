import AnalyticTranslation
import IntegerPoleRecurrence

namespace Zeta5Local
open Finset
variable {p : ℕ} [Fact p.Prime]

/-- The functional applied to the residue-class pole with integer numerator
`w`: an integer pole when `p ∣ w`, otherwise a convergent analytic far pole. -/
noncomputable def residuePoleValue (Y : ℚ_[p]) (w : ℤ) : ℚ_[p] :=
  if (p : ℤ) ∣ w then integerPoleValue Y (w / p)
  else analyticPoleValue ((w : ℚ_[p]) / p)

lemma farInteger_inverse_norm (w : ℤ) (hw : ¬(p : ℤ) ∣ w) :
    ‖((w : ℚ_[p]) / p)⁻¹‖ = (p : ℝ)⁻¹ := by
  have hp := (Fact.out : p.Prime)
  have hn : ‖(w : ℚ_[p])‖ = 1 := by
    apply le_antisymm (Padic.norm_int_le_one w)
    apply le_of_not_gt
    intro h
    exact hw ((Padic.norm_intCast_lt_one_iff (p := p) (k := w)).mp h)
  rw [norm_inv, norm_div, hn, Padic.norm_p]
  field_simp

lemma residuePoleValue_increment (hp7 : 7 ≤ p) (Y : ℚ_[p]) (w : ℤ) (hw : w ≠ 0) :
    residuePoleValue Y w - residuePoleValue Y (w - p) =
      ((w : ℚ_[p]) / p)⁻¹ ^ 5 := by
  have hp := (Fact.out : p.Prime)
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpq0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hdiv : ((p : ℤ) ∣ w - p) ↔ (p : ℤ) ∣ w := by
    constructor
    · intro h; simpa using dvd_add h (dvd_refl (p : ℤ))
    · intro h; exact dvd_sub h (dvd_refl (p : ℤ))
  unfold residuePoleValue
  by_cases h : (p : ℤ) ∣ w
  · rw [if_pos h, if_pos (hdiv.mpr h)]
    have he : (w - p) / p = w / p - 1 := by
      rw [Int.sub_ediv_of_dvd _ (dvd_refl (p : ℤ)), Int.ediv_self hp0]
    rw [he, integerPoleValue_increment Y _]
    · congr 2
      apply (eq_div_iff hpq0).mpr
      exact_mod_cast Int.ediv_mul_cancel h
    · intro hz
      have he := Int.ediv_mul_cancel h
      rw [hz, zero_mul] at he
      exact hw he.symm
  · rw [if_neg h, if_neg (fun hh => h (hdiv.mp hh))]
    have hs : ‖((w : ℚ_[p]) / p)⁻¹‖ < 1 := by
      rw [farInteger_inverse_norm w h]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
    have hs0 : (w : ℚ_[p]) / p ≠ 0 := div_ne_zero (by exact_mod_cast hw) hpq0
    have he : ((w - p : ℤ) : ℚ_[p]) / p = (w : ℚ_[p]) / p - 1 := by
      push_cast
      field_simp
    rw [he]
    have ht := analyticPoleValue_translation hp7 ((w : ℚ_[p]) / p) hs0 hs
    linear_combination -ht


/-- A finite moving window telescopes to its two endpoints. -/
lemma residueWindow_increment (f : ℤ → ℚ_[p]) (m : ℕ) (r : ℤ) :
    (∑ a ∈ range m, f (r - a)) - (∑ a ∈ range m, f (r - 1 - a)) =
      f r - f (r - m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, sum_range_succ]
    have he : r - 1 - m = r - (m + 1 : ℕ) := by omega
    rw [he]
    linear_combination ih

noncomputable def distributedIntegerPole (Y : ℚ_[p]) (r : ℤ) : ℚ_[p] :=
  (p : ℚ_[p])⁻¹ ^ 5 * ∑ a ∈ range p, residuePoleValue Y (r - a)

lemma distributedIntegerPole_increment (hp7 : 7 ≤ p) (Y : ℚ_[p])
    (r : ℤ) (hr : r ≠ 0) :
    distributedIntegerPole Y r - distributedIntegerPole Y (r - 1) =
      (r : ℚ_[p])⁻¹ ^ 5 := by
  rw [distributedIntegerPole, distributedIntegerPole, ← mul_sub,
    residueWindow_increment, residuePoleValue_increment hp7 Y r hr]
  have hpq0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hrq0 : (r : ℚ_[p]) ≠ 0 := by exact_mod_cast hr
  field_simp

lemma distributedIntegerPole_zero (Y : ℚ_[p]) :
    distributedIntegerPole Y 0 = (p : ℚ_[p])⁻¹ ^ 5 * (-Y + distributionConstant p) := by
  have hp := (Fact.out : p.Prime)
  unfold distributedIntegerPole
  rw [sum_range_eq_add_Ico _ hp.pos]
  simp only [Nat.cast_zero, sub_zero, residuePoleValue, dvd_zero, if_true,
    Int.zero_ediv, integerPoleValue_zero]
  congr 2
  unfold distributionConstant
  apply sum_congr rfl
  intro a ha
  have hapos := (mem_Ico.mp ha).1
  have hap := (mem_Ico.mp ha).2
  have hnot : ¬(p : ℤ) ∣ -(a : ℤ) := by
    intro h
    have hd : p ∣ a := by exact_mod_cast (dvd_neg.mp h)
    exact (Nat.not_dvd_of_pos_of_lt hapos hap) hd
  simp [hnot, neg_div]

lemma distributedIntegerPole_neg_one (Y : ℚ_[p]) :
    distributedIntegerPole Y (-1) = distributedIntegerPole Y 0 := by
  have hp := (Fact.out : p.Prime)
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have he : residuePoleValue Y 0 = residuePoleValue Y (-(p : ℤ)) := by
    simp [residuePoleValue, Int.neg_ediv, Int.ediv_self hp0]
  have hw := residueWindow_increment (residuePoleValue Y) p 0
  simp only [zero_sub, zero_sub, Int.reduceNeg, he, sub_self] at hw
  have hwin := sub_eq_zero.mp hw
  unfold distributedIntegerPole
  congr 1
  simpa only [zero_sub] using hwin.symm

/-- The actual residue-class distribution law for every integer pole,
including the convergent far-pole terms. This is the simple-pole part of
Lemma 3.2; `rationalTauFunctional_distribution` supplies its polynomial part. -/
theorem integerPole_distribution (hp7 : 7 ≤ p) (X : ℚ_[p]) :
    distributedIntegerPole ((p : ℚ_[p]) ^ 5 * X + distributionConstant p) =
      integerPoleValue X := by
  apply integerPoleValue_unique
  · rw [distributedIntegerPole_zero]
    have hpq0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    field_simp
    ring
  · rw [distributedIntegerPole_neg_one, distributedIntegerPole_zero]
    have hpq0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    field_simp
    ring
  · exact distributedIntegerPole_increment hp7 _

#print axioms integerPole_distribution
end Zeta5Local
