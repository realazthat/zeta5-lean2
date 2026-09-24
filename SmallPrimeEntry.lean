import SmallPrimeActual
import SmallPrimeBinomial

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5Local
open Polynomial IsUltrametricDist

/-- The signed pullback numerator corresponding to f_i f_j / D_K. -/
noncomputable def smallPrimeEntryNumerator (K N i j : ℕ) : ℚ[X] :=
  C ((-1:ℚ)^K) * X^5 * (smallPrimeF N i * smallPrimeF N j).comp (-(X^2))

lemma smallPrimeF_natDegree_le (N i : ℕ) : (smallPrimeF N i).natDegree ≤ 3*N+i := by
  unfold smallPrimeF
  apply Polynomial.natDegree_mul_le.trans
  rw [smallPrimeQ_natDegree]
  have hd : (C (((N.factorial:ℚ)^6)⁻¹) * Zeta5Construction.denominator N^3).natDegree ≤ 3*N := by
    apply (Polynomial.natDegree_C_mul_le _ _).trans
    rw [(smallPrimeDenominator_monic N).natDegree_pow, smallPrimeDenominator_natDegree]
  omega

lemma smallPrimeEntryNumerator_degree (K N h : ℕ) (i j : Fin h) :
    (smallPrimeEntryNumerator K N i j).natDegree ≤ 12*N+4*h+1 := by
  unfold smallPrimeEntryNumerator
  have hF := add_le_add (smallPrimeF_natDegree_le N i) (smallPrimeF_natDegree_le N j)
  have hmul := Polynomial.natDegree_mul_le (p:=smallPrimeF N i) (q:=smallPrimeF N j)
  have hc := Polynomial.natDegree_comp_le (p:=smallPrimeF N i*smallPrimeF N j) (q:=-(X^2:ℚ[X]))
  have hX : (-(X^2:ℚ[X])).natDegree = 2 := by simp
  rw [hX] at hc
  have htop := Polynomial.natDegree_mul_le
    (p:=C ((-1:ℚ)^K)*X^5) (q:=(smallPrimeF N i*smallPrimeF N j).comp (-(X^2)))
  have hfive : (C ((-1:ℚ)^K)*X^5).natDegree ≤ 5 := by
    exact (Polynomial.natDegree_C_mul_le _ _).trans_eq (by simp)
  have hi := i.isLt
  have hj := j.isLt
  omega

lemma smallPrimeEntryNumerator_integerValued (p K N i j n : ℕ) [Fact p.Prime] :
    ‖(((smallPrimeEntryNumerator K N i j).eval (n:ℚ):ℚ):ℚ_[p])‖ ≤ 1 := by
  simp only [smallPrimeEntryNumerator, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_comp, Polynomial.eval_neg]
  push_cast
  rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have hn : ‖(n:ℚ_[p])‖ ≤ 1 := by simpa using Padic.norm_int_le_one (p:=p) (n:ℤ)
  have hi := smallPrimeF_integerValued p N i n
  have hj := smallPrimeF_integerValued p N j n
  exact (mul_le_mul (pow_le_one₀ (norm_nonneg _) hn)
    (mul_le_mul hi hj (norm_nonneg _) (by norm_num : (0:ℝ)≤1))
    (by positivity) (by norm_num : (0:ℝ)≤1)).trans_eq (by norm_num)

/-- The entrywise bound used in (3.12), before taking the determinant. -/
theorem smallPrime_entry_coeff_norm (p K N h : ℕ) [hp : Fact p.Prime]
    (hK : 0<K) (hsize : 12*N+4*h+2 ≤ 5*K) (i j : Fin h) (n : ℕ) :
    ‖((smallPrimeTauPolynomial K (smallPrimeEntryNumerator K N i j)).coeff n : ℚ_[p])‖ ≤
      (p:ℝ)^(6*Nat.log p (5*K)+padicValNat p 24) := by
  have hb := smallPrimeTauPolynomial_coeff_norm p K (12*N+4*h+1) hK
    (smallPrimeEntryNumerator K N i j) (smallPrimeEntryNumerator_degree K N h i j)
    (fun m => smallPrimeEntryNumerator_integerValued p K N i j m) n
  apply hb.trans
  apply pow_le_pow_right₀ (by exact_mod_cast hp.out.one_le)
  have hmax : max (2*K) (12*N+4*h+1+1) ≤ 5*K := by omega
  have hlog := Nat.log_mono_right (b:=p) hmax
  omega

#print axioms smallPrimeEntryNumerator_integerValued
#print axioms smallPrime_entry_coeff_norm
end Zeta5Local
