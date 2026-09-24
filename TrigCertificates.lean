import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta5TrigCertificates

structure Box where
  sl : ℚ
  sh : ℚ
  cl : ℚ
  ch : ℚ

def Bounds (a : ℝ) (b : Box) : Prop :=
  (b.sl : ℝ) ≤ Real.sin a ∧ Real.sin a ≤ b.sh ∧
    (b.cl : ℝ) ≤ Real.cos a ∧ Real.cos a ≤ b.ch

def initialCheck (q : ℚ) (b : Box) : Bool := decide (
  0 ≤ q ∧ 0 ≤ q/2-(q/2)^3/6 ∧
  b.sl ≤ q-q^3/6 ∧ q ≤ b.sh ∧
  b.cl ≤ 1-q^2/2 ∧ 1-2*(q/2-(q/2)^3/6)^2 ≤ b.ch)

def stepCheck (b c : Box) : Bool := decide (
  0 ≤ b.sl ∧ 0 ≤ b.cl ∧
  c.sl ≤ 2*b.sl*b.cl ∧ 2*b.sh*b.ch ≤ c.sh ∧
  c.cl ≤ b.cl^2-b.sh^2 ∧ b.ch^2-b.sl^2 ≤ c.ch)

def chainCheck (b : Box) : List Box → Bool
  | [] => true
  | c :: cs => stepCheck b c && chainCheck c cs

def endpoint (b : Box) : List Box → Box
  | [] => b
  | c :: cs => endpoint c cs

theorem initial_sound (q : ℚ) (b : Box) (h : initialCheck q b = true) :
    Bounds (q : ℝ) b := by
  have hq : 0 ≤ q ∧ 0 ≤ q/2-(q/2)^3/6 ∧
      b.sl ≤ q-q^3/6 ∧ q ≤ b.sh ∧
      b.cl ≤ 1-q^2/2 ∧ 1-2*(q/2-(q/2)^3/6)^2 ≤ b.ch := by
    simpa only [initialCheck, decide_eq_true_eq] using h
  have hr : (0 : ℝ) ≤ q ∧ 0 ≤ (q : ℝ)/2-((q : ℝ)/2)^3/6 ∧
      (b.sl : ℝ) ≤ (q : ℝ)-(q : ℝ)^3/6 ∧ (q : ℝ) ≤ b.sh ∧
      (b.cl : ℝ) ≤ 1-(q : ℝ)^2/2 ∧
      1-2*((q : ℝ)/2-((q : ℝ)/2)^3/6)^2 ≤ b.ch := by exact_mod_cast hq
  refine ⟨hr.2.2.1.trans (Real.sin_ge_sub_cube hr.1),
    (Real.sin_le hr.1).trans hr.2.2.2.1,
    hr.2.2.2.2.1.trans Real.one_sub_sq_div_two_le_cos, ?_⟩
  have hs := Real.sin_ge_sub_cube (show (0 : ℝ) ≤ (q : ℝ)/2 from
    div_nonneg hr.1 (by norm_num))
  have hsq := mul_self_le_mul_self hr.2.1 hs
  have hc : Real.cos (q : ℝ) = 1-2*Real.sin ((q : ℝ)/2)^2 := by
    simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using
      Real.cos_two_mul_eq_one_sub ((q : ℝ)/2)
  rw [hc]
  nlinarith [hr.2.2.2.2.2]

theorem step_sound {a : ℝ} {b c : Box} (hb : Bounds a b)
    (h : stepCheck b c = true) : Bounds (2*a) c := by
  have hq : 0 ≤ b.sl ∧ 0 ≤ b.cl ∧
      c.sl ≤ 2*b.sl*b.cl ∧ 2*b.sh*b.ch ≤ c.sh ∧
      c.cl ≤ b.cl^2-b.sh^2 ∧ b.ch^2-b.sl^2 ≤ c.ch := by
    simpa only [stepCheck, decide_eq_true_eq] using h
  have hr : (0 : ℝ) ≤ b.sl ∧ (0 : ℝ) ≤ b.cl ∧
      (c.sl : ℝ) ≤ 2*(b.sl : ℝ)*b.cl ∧ 2*(b.sh : ℝ)*b.ch ≤ c.sh ∧
      (c.cl : ℝ) ≤ (b.cl : ℝ)^2-(b.sh : ℝ)^2 ∧
      (b.ch : ℝ)^2-(b.sl : ℝ)^2 ≤ c.ch := by exact_mod_cast hq
  rcases hb with ⟨hsl, hsh, hcl, hch⟩
  have hs0 : 0 ≤ Real.sin a := hr.1.trans hsl
  have hc0 : 0 ≤ Real.cos a := hr.2.1.trans hcl
  have hsh0 : (0 : ℝ) ≤ b.sh := hs0.trans hsh
  have hch0 : (0 : ℝ) ≤ b.ch := hc0.trans hch
  have hpL := mul_le_mul hsl hcl hr.2.1 hs0
  have hpU := mul_le_mul hsh hch hc0 hsh0
  have hsL := mul_self_le_mul_self hr.1 hsl
  have hsU := mul_self_le_mul_self hs0 hsh
  have hcL := mul_self_le_mul_self hr.2.1 hcl
  have hcU := mul_self_le_mul_self hc0 hch
  unfold Bounds
  rw [Real.sin_two_mul, Real.cos_two_mul']
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [hr.2.2.1, hr.2.2.2.1,
    hr.2.2.2.2.1, hr.2.2.2.2.2]

theorem chain_sound (a : ℝ) (b : Box) (bs : List Box) (hb : Bounds a b)
    (h : chainCheck b bs = true) : Bounds (2^bs.length*a) (endpoint b bs) := by
  induction bs generalizing a b with
  | nil => simpa [endpoint] using hb
  | cons c cs ih =>
    have hh : stepCheck b c = true ∧ chainCheck c cs = true := by
      simpa only [chainCheck, Bool.and_eq_true] using h
    have hi := ih (2*a) c (step_sound hb hh.1) hh.2
    simpa only [endpoint, List.length_cons, pow_succ, mul_assoc] using hi

theorem bounds_of_check (q : ℚ) (b : Box) (bs : List Box)
    (h : (initialCheck q b && chainCheck b bs) = true) :
    Bounds (2^bs.length*(q : ℝ)) (endpoint b bs) := by
  have hh : initialCheck q b = true ∧ chainCheck b bs = true := by
    simpa only [Bool.and_eq_true] using h
  exact chain_sound _ _ _ (initial_sound q b hh.1) hh.2

end Zeta5TrigCertificates
