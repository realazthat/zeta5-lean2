import GramScaling
import ExternalField
import WeightBounds

noncomputable section
open scoped BigOperators
open MeasureTheory Set

namespace Zeta5Construction

lemma log_realDenominator_scaled (m : ℕ) {K t : ℝ} (hK : 0 < K) (ht : 0 < t) :
    Real.log ((realDenominator m).eval ((K*Real.sqrt t)^2)) =
      2*m*Real.log K + ∑ i ∈ Finset.range m,
        Real.log (t+(((i+1:ℕ):ℝ)/K)^2) := by
  rw [realDenominator_eval, Real.log_prod (by intros; positivity)]
  have he (i : ℕ) :
      Real.log ((K*Real.sqrt t)^2+(i+1:ℝ)^2) =
        2*Real.log K+Real.log (t+(((i+1:ℕ):ℝ)/K)^2) := by
    have ha : (K*Real.sqrt t)^2+(i+1:ℝ)^2 =
        K^2*(t+(((i+1:ℕ):ℝ)/K)^2) := by
      rw [mul_pow, Real.sq_sqrt ht.le]
      push_cast
      field_simp
    rw [ha, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    norm_num
  simp only [he, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

lemma log_integralWeight_upper {y : ℝ} (hy : 0 < y) :
    Real.log (integralWeight y) ≤ Real.log 8192+5*Real.log (1+y)-2*Real.pi*y := by
  have hu := Real.log_le_log (integralWeight_pos hy) (integralWeight_upper hy)
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_exp] at hu
  norm_num at hu
  linarith

lemma log_scaledGramWeight (N h : ℕ) {K t : ℝ} (hK : 0 < K) (ht : 0 < t) :
    Real.log (scaledGramWeight N h K t) =
      Real.log K-Real.log 2-(1/2)*Real.log t +
        6*Real.log ((realDenominator N).eval ((K*Real.sqrt t)^2)) -
        Real.log ((realDenominator (N+h)).eval ((K*Real.sqrt t)^2)) +
        Real.log (integralWeight (K*Real.sqrt t)) := by
  have hy : 0 < K*Real.sqrt t := by positivity
  have hDN := realDenominator_eval_pos N (K*Real.sqrt t)
  have hDK := realDenominator_eval_pos (N+h) (K*Real.sqrt t)
  have hw := integralWeight_pos hy
  unfold scaledGramWeight gramWeight
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_pow, Real.log_rpow]
  ring

/-- A logarithmic form of the pointwise bound yielding (6.13). -/
theorem log_scaledGramWeight_upper {N h : ℕ} {K t : ℝ}
    (hN : 0 < N) (hh : 0 < h) (hK : K=(N+h:ℕ)) (ht : 0 < t) :
    Real.log (scaledGramWeight N h K t) ≤
      Real.log 4096+12+(12*N-2*K+18)*Real.log K-
        (1/2)*Real.log t+5*Real.log (1+Real.sqrt t)-K*externalField ((N:ℝ)/K) t := by
  have hKp : 0 < K := by rw [hK]; positivity
  have hK1 : 1 ≤ K := by rw [hK]; exact_mod_cast (by omega : 1 ≤ N+h)
  have hNK : (N:ℝ) ≤ K := by rw [hK]; exact_mod_cast (by omega : N ≤ N+h)
  have hNr := denominator_riemann_error ht hKp hN hNK
  have hKr := denominator_riemann_error ht hKp (by omega : 0 < N+h) (by rw [hK])
  have hKdiv : ((N+h:ℕ):ℝ)/K=1 := by rw [← hK]; exact div_self hKp.ne'
  rw [hKdiv] at hKr
  have hy : 0 < K*Real.sqrt t := by positivity
  have hw := log_integralWeight_upper hy
  have hlog : Real.log (1+K*Real.sqrt t) ≤ Real.log K+Real.log (1+Real.sqrt t) := by
    rw [← Real.log_mul hKp.ne' (by positivity)]
    apply Real.log_le_log (by positivity)
    nlinarith [Real.sqrt_nonneg t]
  have hc : Real.log (8192:ℝ)-Real.log 2=Real.log 4096 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  rw [log_scaledGramWeight N h hKp ht,
    log_realDenominator_scaled N hKp ht, log_realDenominator_scaled (N+h) hKp ht]
  unfold externalField
  push_cast at hK ⊢
  have hmult := mul_le_mul_of_nonneg_left hlog (by norm_num : (0:ℝ)≤5)
  simp only [Nat.cast_add, Nat.cast_one] at hNr hKr
  rw [← hK]
  nlinarith [hNr.2, hKr.1]

lemma scaledGramWeight_pos (N h : ℕ) {K t : ℝ} (hK : 0 < K) (ht : 0 < t) :
    0 < scaledGramWeight N h K t := by
  unfold scaledGramWeight
  exact mul_pos (mul_pos (by positivity) (Real.rpow_pos_of_pos ht _))
    (gramWeight_pos N h (by positivity))

/-- The pointwise weight estimate after y=K√t, with its K power in exponential form. -/
theorem scaledGramWeight_upper {N h : ℕ} {K t : ℝ}
    (hN : 0 < N) (hh : 0 < h) (hK : K=(N+h:ℕ)) (ht : 0 < t) :
    scaledGramWeight N h K t ≤
      4096*Real.exp 12*t^(-(1/2:ℝ))*(1+Real.sqrt t)^5*
        Real.exp ((12*N-2*K+18)*Real.log K-K*externalField ((N:ℝ)/K) t) := by
  have hKp : 0 < K := by rw [hK]; positivity
  have hu := Real.exp_le_exp.mpr (log_scaledGramWeight_upper hN hh hK ht)
  rw [Real.exp_log (scaledGramWeight_pos N h hKp ht)] at hu
  have ht' : Real.exp (-(1/2:ℝ)*Real.log t) = t^(-(1/2:ℝ)) := by
    rw [Real.rpow_def_of_pos ht]
    congr 1
    ring
  have h5 : Real.exp (5*Real.log (1+Real.sqrt t)) = (1+Real.sqrt t)^5 := by
    rw [show (5:ℝ)=(5:ℕ) by norm_num, Real.exp_nat_mul, Real.exp_log (by positivity)]
  have he : Real.exp (Real.log 4096+12+(12*N-2*K+18)*Real.log K-
        (1/2)*Real.log t+5*Real.log (1+Real.sqrt t)-K*externalField ((N:ℝ)/K) t) =
      Real.exp (Real.log 4096)*Real.exp 12*Real.exp (-(1/2:ℝ)*Real.log t)*
        Real.exp (5*Real.log (1+Real.sqrt t))*
          Real.exp ((12*N-2*K+18)*Real.log K-K*externalField ((N:ℝ)/K) t) := by
    repeat rw [← Real.exp_add]
    congr 1
    ring
  rw [he, Real.exp_log (by norm_num), ht', h5] at hu
  exact hu

#print axioms scaledGramWeight_upper

end Zeta5Construction
