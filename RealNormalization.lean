import MatrixIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section
open scoped BigOperators

namespace Zeta5Construction

lemma log_nat_succ_sub_log_le {n : ℕ} (hn : 0 < n) :
    Real.log (n+1 : ℝ) - Real.log (n : ℝ) ≤ 1 / (n : ℝ) := by
  have hp : (0 : ℝ) < n := by exact_mod_cast hn
  have h := Real.log_le_sub_one_of_pos (div_pos (by positivity : (0:ℝ)<n+1) hp)
  rw [Real.log_div (by positivity) hp.ne'] at h
  convert h using 1 <;> field_simp <;> ring

lemma log_nat_succ_sub_log_ge {n : ℕ} (hn : 0 < n) :
    1 / (n+1 : ℝ) ≤ Real.log (n+1 : ℝ) - Real.log (n : ℝ) := by
  have hp : (0 : ℝ) < n := by exact_mod_cast hn
  have h := Real.log_le_sub_one_of_pos (div_pos hp (by positivity : (0:ℝ)<n+1))
  rw [Real.log_div hp.ne' (by positivity)] at h
  have he : (n : ℝ)/(n+1)-1 = -(1/(n+1)) := by field_simp <;> ring
  rw [he] at h
  linarith

lemma log_factorial_lower {n : ℕ} (hn : 0 < n) :
    (n : ℝ)*Real.log n - n + 1 ≤ Real.log (n.factorial : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hp : (0 : ℝ) < n := by exact_mod_cast hn
    have hstep := mul_le_mul_of_nonneg_left
      (log_nat_succ_sub_log_le hn) hp.le
    have hn0 : (n : ℝ) ≠ 0 := hp.ne'
    rw [mul_one_div_cancel hn0] at hstep
    rw [Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity)]
    push_cast
    nlinarith

lemma log_factorial_upper {n : ℕ} (hn : 0 < n) :
    Real.log (n.factorial : ℝ) ≤
      (n : ℝ)*Real.log n - n + Real.log n + 1 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hp : (0 : ℝ) < n := by exact_mod_cast hn
    have hstep := mul_le_mul_of_nonneg_left
      (log_nat_succ_sub_log_ge hn) (by positivity : (0:ℝ)≤n+1)
    have he : (n+1 : ℝ)*(1/(n+1)) = 1 := by field_simp
    rw [he] at hstep
    rw [Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity)]
    push_cast
    nlinarith

/-- The elementary summed-factorial bound used in (6.15). -/
lemma sum_even_log_factorial_lower {h : ℕ} (hh : 0 < h) :
    (h:ℝ)^2*Real.log (2*h) - 3/2*(h:ℝ)^2 - 2*h*Real.log (2*h) ≤
      ∑ i ∈ Finset.range (h-1), Real.log ((2*(i+1)).factorial : ℝ) := by
  induction h, hh using Nat.le_induction with
  | base =>
    norm_num
    have : 0 ≤ Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
    linarith
  | succ h hh ih =>
    have hp : (0 : ℝ) < h := by exact_mod_cast hh
    have hpred : h-1+1=h := by omega
    have hs : h+1-1 = (h-1)+1 := by omega
    rw [hs, Finset.sum_range_succ, hpred]
    have hf := log_factorial_lower (by omega : 0 < 2*h)
    have hl := log_nat_succ_sub_log_le hh
    have hge : (1:ℝ) ≤ h := by exact_mod_cast hh
    have hm := mul_le_mul_of_nonneg_left hl
      (show (0:ℝ) ≤ (h:ℝ)^2-1 by nlinarith)
    have ht : ((h:ℝ)^2-1)*(1/(h:ℝ)) ≤ h := by
      rw [mul_one_div]
      apply (div_le_iff₀ hp).mpr
      nlinarith
    have hlog : 0 ≤ Real.log (2*(h:ℝ)) :=
      Real.log_nonneg (by nlinarith)
    rw [Real.log_mul (by norm_num) hp.ne'] at hlog
    have hn : (0:ℝ)<h+1 := by positivity
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat] at hf ⊢
    rw [Real.log_mul (by norm_num) hp.ne'] at hf
    rw [Real.log_mul (by norm_num) hn.ne']
    rw [Real.log_mul (by norm_num) hp.ne'] at ih
    nlinarith

lemma log_normalizingScalar (N h : ℕ) :
    Real.log (normalizingScalar N h : ℝ) =
      2*h*Real.log ((N+h).factorial : ℝ) + (h-1:ℕ)*Real.log 4 -
        12*h*Real.log (N.factorial : ℝ) -
          2*∑ i ∈ Finset.range (h-1), Real.log ((2*(i+1)).factorial : ℝ) := by
  unfold normalizingScalar
  push_cast
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_prod (by intros; positivity)]
  simp only [Real.log_pow]
  simp only [← Finset.mul_sum]
  push_cast
  ring

/-- The entire quadratic contribution of the normalizing scalar. -/
def normalizationMainTerm (N h : ℝ) : ℝ :=
  2*h*(N+h)*Real.log (N+h) - 2*h*(N+h) -
    12*h*N*Real.log N + 12*h*N -
      2*h^2*Real.log (2*h) + 3*h^2

/-- Equation (6.15) before introducing the fixed ratios α and lam. -/
theorem log_normalizingScalar_upper {N h : ℕ} (hN : 0 < N) (hh : 0 < h) :
    Real.log (normalizingScalar N h : ℝ) ≤
      normalizationMainTerm N h + 6*h*Real.log (N+h) + 6*h := by
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have hhp : (0:ℝ)<h := by exact_mod_cast hh
  have hKp : (0:ℝ)<N+h := by positivity
  have hK := log_factorial_upper (by omega : 0 < N+h)
  have hNf := log_factorial_lower hN
  have hsum := sum_even_log_factorial_lower hh
  have hK' := mul_le_mul_of_nonneg_left hK (by positivity : (0:ℝ)≤2*h)
  have hN' := mul_le_mul_of_nonneg_left hNf (by positivity : (0:ℝ)≤12*h)
  have hlh : Real.log (h:ℝ) ≤ Real.log (N+h:ℝ) :=
    Real.log_le_log hhp (by linarith)
  have hl2 : Real.log (2:ℝ) ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2) using 1 <;> norm_num
  have hl2p : 0 ≤ Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
  have hl4 : Real.log (4:ℝ) = 2*Real.log 2 := by
    have he : (4:ℝ) = 2^2 := by norm_num
    rw [he, Real.log_pow]
    norm_num
  have hpred : ((h-1:ℕ):ℝ) = h-1 := by
    rw [Nat.cast_sub hh, Nat.cast_one]
  have herr : (h-1:ℝ)*Real.log 4 + 4*h*Real.log (2*h) ≤
      4*h*Real.log (N+h) + 6*h := by
    rw [hl4, Real.log_mul (by norm_num) hhp.ne']
    have ha := mul_le_mul_of_nonneg_left hlh (by positivity : (0:ℝ)≤4*h)
    have hb := mul_le_mul_of_nonneg_left hl2 (by positivity : (0:ℝ)≤6*h)
    nlinarith
  rw [log_normalizingScalar, hpred]
  unfold normalizationMainTerm
  push_cast at hK' ⊢
  nlinarith

/-- The constant C* in (6.3), kept general in the fixed ratios. -/
def normalizationConstant (α lam : ℝ) : ℝ :=
  -2*lam + 12*α*lam*(1-Real.log α) + 3*lam^2 - 2*lam^2*Real.log (2*lam)

lemma normalizationMainTerm_ratios {α lam K : ℝ}
    (hα : 0 < α) (hlam : 0 < lam) (hK : 0 < K) (hs : α+lam=1) :
    normalizationMainTerm (α*K) (lam*K) =
      (2*lam-12*α*lam-2*lam^2)*K^2*Real.log K + normalizationConstant α lam*K^2 := by
  have he : α*K+lam*K=K := by nlinarith
  unfold normalizationMainTerm normalizationConstant
  rw [he, Real.log_mul hα.ne' hK.ne']
  rw [show 2*(lam*K)=(2*lam)*K by ring,
    Real.log_mul (by positivity) hK.ne']
  ring

/-- Source (6.15), with any positive rationally fixed N/K and h/K. -/
theorem log_normalizingScalar_upper_ratios {N h : ℕ} {α lam K : ℝ}
    (hN : 0 < N) (hh : 0 < h) (hα : 0 < α) (hlam : 0 < lam) (hK : 0 < K)
    (hs : α+lam=1) (hNr : (N:ℝ)=α*K) (hhr : (h:ℝ)=lam*K) :
    Real.log (normalizingScalar N h : ℝ) ≤
      (2*lam-12*α*lam-2*lam^2)*K^2*Real.log K + normalizationConstant α lam*K^2 +
        6*h*Real.log K + 6*h := by
  have hu := log_normalizingScalar_upper hN hh
  have he : (N:ℝ)+h=K := by rw [hNr, hhr]; nlinarith
  rw [he] at hu
  rw [hNr, hhr, normalizationMainTerm_ratios hα hlam hK hs] at hu
  simpa only [hhr] using hu

lemma log_normalizedDeterminant (N h : ℕ) :
    Real.log ((normalizedDeterminant N h).eval₂ (Rat.castHom ℝ) zetaSeries) =
      Real.log (normalizingScalar N h : ℝ) +
        Real.log ((determinant N h).eval₂ (Rat.castHom ℝ) zetaSeries) := by
  have hs : (0:ℝ)<(normalizingScalar N h:ℝ) := by
    exact_mod_cast normalizingScalar_pos N h
  unfold normalizedDeterminant
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C]
  exact Real.log_mul hs.ne' (determinant_eval_pos N h).ne'

/-- Cancellation of all K² log K terms in (6.14)–(6.15). -/
theorem log_normalizedDeterminant_upper {N h : ℕ} {α lam K E R : ℝ}
    (hN : 0 < N) (hh : 0 < h) (hα : 0 < α) (hlam : 0 < lam) (hK : 0 < K)
    (hs : α+lam=1) (hNr : (N:ℝ)=α*K) (hhr : (h:ℝ)=lam*K)
    (hdet : Real.log ((determinant N h).eval₂ (Rat.castHom ℝ) zetaSeries) ≤
      2*h*(h+6*N-K)*Real.log K + E*K^2 + R) :
    Real.log ((normalizedDeterminant N h).eval₂ (Rat.castHom ℝ) zetaSeries) ≤
      (E+normalizationConstant α lam)*K^2 + R + 6*h*Real.log K + 6*h := by
  have hnorm := log_normalizingScalar_upper_ratios hN hh hα hlam hK hs hNr hhr
  rw [log_normalizedDeterminant]
  have hc : (2*lam-12*α*lam-2*lam^2)*K^2*Real.log K +
      2*(h:ℝ)*(h+6*N-K)*Real.log K = 0 := by
    rw [hNr, hhr]
    ring
  linarith

#print axioms log_normalizingScalar_upper_ratios
#print axioms log_normalizedDeterminant_upper

end Zeta5Construction
