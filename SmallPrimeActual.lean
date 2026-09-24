import SmallPrimeFactorials
import SmallPrimeQuotient
import PartialFractions
import SmallPrimePole

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5Local
open Polynomial IsUltrametricDist

noncomputable def smallPrimeQuotient (K : ℕ) (A : ℚ[X]) : ℚ[X] :=
  (C ((K.factorial:ℚ)^2)*A) / Lagrange.nodal (smallPrimeRoots K) (smallPrimeRoot K)

/-- The quotient-value bound in Lemma 3.3 for the actual consecutive nonzero poles. -/
theorem smallPrimeQuotient_norm (p K d : ℕ) [hp : Fact p.Prime]
    (hK : 0<K) (A : ℚ[X]) (hdeg : A.natDegree ≤ d)
    (hA : ∀ n : ℕ, ‖((A.eval (n:ℚ):ℚ):ℚ_[p])‖ ≤ 1) (n : ℕ) :
    ‖(((smallPrimeQuotient K A).eval (n:ℚ):ℚ):ℚ_[p])‖ ≤
      (p:ℝ)^(Nat.log p (2*K) + max (Nat.log p d) (Nat.log p (2*K))) := by
  apply polynomial_norm_of_nat_tail p (smallPrimeQuotient K A) _ K _ n
  intro x hxK
  let r : ℕ → ℚ_[p] := fun i => (smallPrimeRoot K i : ℚ_[p])
  let A' : ℚ_[p] → ℚ_[p] := fun x => A.eval₂ (Rat.castHom ℚ_[p]) x
  have hnonempty : (smallPrimeRoots K).Nonempty := by
    refine ⟨0, ?_⟩
    simp only [smallPrimeRoots, Finset.mem_erase, Finset.mem_range]
    omega
  have hbound (j) (hj : j∈smallPrimeRoots K) : j≤2*K := by
    have := Finset.mem_range.mp (Finset.mem_erase.mp hj).2
    omega
  have hx (j) (hj : j∈smallPrimeRoots K) : (x:ℚ_[p]) ≠ r j := by
    dsimp [r, smallPrimeRoot]
    push_cast
    intro he
    have he' : (x:ℚ)=(j:ℚ)-K := by exact_mod_cast he
    have hjB := hbound j hj
    have : (K:ℚ)<x := by exact_mod_cast hxK
    have : (j:ℚ)≤2*K := by exact_mod_cast hjB
    linarith
  have hsep (j) (hj : j∈smallPrimeRoots K) (i) (hi : i∈smallPrimeRoots K)
      (hji : j≠i) : r j ≠ r i ∧ ‖r j-r i‖⁻¹ ≤ (p:ℝ)^Nat.log p (2*K) := by
    have hjB := hbound j hj
    have hiB := hbound i hi
    have hji' : (j:ℤ)≠(i:ℤ) := by exact_mod_cast hji
    have habs : ((j:ℤ)-i).natAbs ≤ 2*K := by omega
    have hn := integer_difference_inv_norm p (2*K) j i hji' habs
    constructor
    · intro he
      apply hji
      apply smallPrimeRoot_inj K
      exact Rat.cast_injective (α:=ℚ_[p]) he
    · simpa only [r, smallPrimeRoot, Rat.cast_sub, Rat.cast_natCast,
        sub_sub_sub_cancel_right, Int.cast_natCast] using hn
  have hAval (j) (hj : j∈smallPrimeRoots K) : ‖A' (r j)‖ ≤ 1 := by
    have h := integerValued_norm_on_padicInt p A 1 (by norm_num) hA ((j:ℤ_[p])-K)
    simpa only [A', r, smallPrimeRoot, Rat.cast_sub, Rat.cast_natCast,
      PadicInt.coe_sub, PadicInt.coe_natCast] using h
  have hLip (j) (hj : j∈smallPrimeRoots K) :
      ‖A' (x:ℚ_[p])-A' (r j)‖ ≤ (p:ℝ)^Nat.log p d * ‖(x:ℚ_[p])-r j‖ := by
    have h := integerValued_lipschitz p A 1 d hdeg (by norm_num) hA
      (x:ℤ_[p]) ((j:ℤ_[p])-K)
    simpa only [A', r, smallPrimeRoot, Rat.cast_sub, Rat.cast_natCast,
      PadicInt.coe_sub, PadicInt.coe_natCast, one_mul, mul_one, mul_comm] using h
  have hf := partial_fraction_eval₂ (Rat.castHom ℚ_[p])
    (C ((K.factorial:ℚ)^2)*A) (smallPrimeRoots K) (smallPrimeRoot K)
    (smallPrimeRoot_inj K).injOn (x:ℚ_[p]) hx
  have hpart : (smallPrimeQuotient K A).eval₂ (Rat.castHom ℚ_[p]) (x:ℚ_[p]) =
      (K.factorial:ℚ_[p])^2*A' x / (∏ i∈smallPrimeRoots K, ((x:ℚ_[p])-r i)) -
      ∑ i∈smallPrimeRoots K, A' (r i) *
        reducedInverseProduct p (smallPrimeRoots K) r ((K.factorial:ℚ_[p])^2) i (r i) /
        ((x:ℚ_[p])-r i) := by
    have heval (i) : A' (r i) = ((A.eval (smallPrimeRoot K i):ℚ):ℚ_[p]) := by
      exact Polynomial.eval₂_at_apply (Rat.castHom ℚ_[p]) _
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Rat.coe_castHom,
      Rat.cast_pow, Rat.cast_natCast, Lagrange.nodal, Polynomial.eval₂_finsetProd,
      Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C,
      Polynomial.eval_mul, Polynomial.eval_C, Rat.cast_mul, Rat.cast_div,
      Rat.cast_prod, Rat.cast_sub] at hf
    apply eq_sub_iff_add_eq.mpr
    calc
      _ = (smallPrimeQuotient K A).eval₂ (Rat.castHom ℚ_[p]) (x:ℚ_[p]) +
          ∑ i∈smallPrimeRoots K,
            ((K.factorial:ℚ_[p])^2 * ((A.eval (smallPrimeRoot K i):ℚ):ℚ_[p]) /
              ∏ j∈(smallPrimeRoots K).erase i, (r i-r j)) / ((x:ℚ_[p])-r i) := by
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        rw [heval]
        unfold reducedInverseProduct
        ring
      _ = _ := by
        simpa only [smallPrimeQuotient, Lagrange.nodal, A', r] using hf.symm
  have hb := partialFraction_polynomial_norm p (smallPrimeRoots K) r
    ((K.factorial:ℚ_[p])^2) A' (x:ℚ_[p])
    ((smallPrimeQuotient K A).eval₂ (Rat.castHom ℚ_[p]) (x:ℚ_[p]))
    ((p:ℝ)^Nat.log p (2*K)) ((p:ℝ)^Nat.log p (2*K)) ((p:ℝ)^Nat.log p d)
    hnonempty (by positivity) (by positivity) (by positivity) hx hsep
    (fun j hj => smallPrimeRoot_center_norm p K j hj) hAval hLip hpart
  have he := Polynomial.eval₂_at_apply (p := smallPrimeQuotient K A)
    (Rat.castHom ℚ_[p]) (x:ℚ)
  simp only [Rat.coe_castHom, Rat.cast_natCast] at he
  rw [he] at hb
  convert hb using 1
  rw [pow_add]
  congr 1
  exact (show Monotone (fun k : ℕ => (p:ℝ)^k) from
    fun a b hab => pow_le_pow_right₀ (by exact_mod_cast hp.out.one_le) hab).map_max

lemma smallPrimeQuotient_degree (K : ℕ) (A : ℚ[X]) :
    (smallPrimeQuotient K A).natDegree ≤ A.natDegree := by
  unfold smallPrimeQuotient
  rw [← Polynomial.divByMonic_eq_div _ (Lagrange.nodal_monic (s:=smallPrimeRoots K) (v:=smallPrimeRoot K)),
    Polynomial.natDegree_divByMonic _ (Lagrange.nodal_monic (s:=smallPrimeRoots K) (v:=smallPrimeRoot K))]
  exact (Nat.sub_le _ _).trans (Polynomial.natDegree_C_mul_le _ _)

lemma smallPrimeQuotient_tau_norm (p K d : ℕ) [hp : Fact p.Prime]
    (hK : 0<K) (A : ℚ[X]) (hdeg : A.natDegree ≤ d)
    (hA : ∀ n : ℕ, ‖((A.eval (n:ℚ):ℚ):ℚ_[p])‖ ≤ 1) :
    ‖(rationalTauFunctional (smallPrimeQuotient K A) : ℚ_[p])‖ ≤
      (p:ℝ)^(6*Nat.log p (max (2*K) (d+1)) + padicValNat p 24) := by
  have hb := rationalTauFunctional_integerValued_norm p (smallPrimeQuotient K A)
    ((p:ℝ)^(Nat.log p (2*K) + max (Nat.log p d) (Nat.log p (2*K)))) d
    ((smallPrimeQuotient_degree K A).trans hdeg) (by positivity)
    (smallPrimeQuotient_norm p K d hK A hdeg hA)
  rw [show (24:ℚ_[p])=(24:ℕ) by norm_num, padic_nat_inv_norm p 24 (by norm_num),
    ← pow_add, ← pow_add] at hb
  apply hb.trans
  apply pow_le_pow_right₀ (by exact_mod_cast hp.out.one_le)
  have hL := Nat.log_mono_right (le_max_left (2*K) (d+1)) (b:=p)
  have hd := Nat.log_mono_right (le_max_right (2*K) (d+1)) (b:=p)
  have hd' := Nat.log_mono_right (show d≤max (2*K) (d+1) by omega) (b:=p)
  omega

noncomputable def smallPrimeResidue (K : ℕ) (A : ℚ[X]) (j : ℕ) : ℚ :=
  (K.factorial:ℚ)^2 * A.eval (smallPrimeRoot K j) /
    ∏ i∈(smallPrimeRoots K).erase j, (smallPrimeRoot K j-smallPrimeRoot K i)

lemma smallPrimeResidue_norm (p K : ℕ) [Fact p.Prime] (A : ℚ[X])
    (hA : ∀ n : ℕ, ‖((A.eval (n:ℚ):ℚ):ℚ_[p])‖ ≤ 1)
    (j : ℕ) (hj : j∈smallPrimeRoots K) :
    ‖(smallPrimeResidue K A j : ℚ_[p])‖ ≤ (p:ℝ)^Nat.log p (2*K) := by
  have ha := integerValued_norm_on_padicInt p A 1 (by norm_num) hA ((j:ℤ_[p])-K)
  have heval := Polynomial.eval₂_at_apply (p:=A) (Rat.castHom ℚ_[p]) (smallPrimeRoot K j)
  simp only [Rat.coe_castHom, smallPrimeRoot, Rat.cast_sub, Rat.cast_natCast] at heval
  simp only [PadicInt.coe_sub, PadicInt.coe_natCast] at ha
  rw [heval] at ha
  have he : (smallPrimeResidue K A j : ℚ_[p]) =
      ((A.eval (smallPrimeRoot K j):ℚ):ℚ_[p]) * reducedInverseProduct p (smallPrimeRoots K)
        (fun i => (smallPrimeRoot K i : ℚ_[p])) ((K.factorial:ℚ_[p])^2) j
        (smallPrimeRoot K j : ℚ_[p]) := by
    unfold smallPrimeResidue reducedInverseProduct
    push_cast
    ring
  rw [he, norm_mul]
  exact (mul_le_mul ha (smallPrimeRoot_center_norm p K j hj)
    (norm_nonneg _) (by norm_num : (0:ℝ)≤1)).trans_eq (one_mul _)

/-- The actual extended τ polynomial for the rational function in Lemma 3.3. -/
noncomputable def smallPrimeTauPolynomial (K : ℕ) (A : ℚ[X]) : ℚ[X] :=
  C (rationalTauFunctional (smallPrimeQuotient K A)) +
    ∑ j∈smallPrimeRoots K, C (smallPrimeResidue K A j)*poleValue ((j:ℤ)-K)

/-- Lemma 3.3 in coefficient-norm form, valid for every prime including 2 and 3. -/
theorem smallPrimeTauPolynomial_coeff_norm (p K d : ℕ) [hp : Fact p.Prime]
    (hK : 0<K) (A : ℚ[X]) (hdeg : A.natDegree ≤ d)
    (hA : ∀ n : ℕ, ‖((A.eval (n:ℚ):ℚ):ℚ_[p])‖ ≤ 1) (n : ℕ) :
    ‖((smallPrimeTauPolynomial K A).coeff n : ℚ_[p])‖ ≤
      (p:ℝ)^(6*Nat.log p (max (2*K) (d+1)) + padicValNat p 24) := by
  unfold smallPrimeTauPolynomial
  rw [Polynomial.coeff_add]
  push_cast
  apply (norm_add_le_max _ _).trans
  apply max_le
  · by_cases hn : n=0
    · subst n
      simpa only [Polynomial.coeff_C_zero] using smallPrimeQuotient_tau_norm p K d hK A hdeg hA
    · simp [Polynomial.coeff_C, hn]
  · rw [Polynomial.finsetSum_coeff]
    push_cast
    apply norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro j hj
    rw [Polynomial.coeff_C_mul]
    push_cast
    rw [norm_mul]
    have hjB : j≤2*K := by have := Finset.mem_range.mp (Finset.mem_erase.mp hj).2; omega
    have hr : -(K:ℤ)≤(j:ℤ)-K ∧ (j:ℤ)-K≤K := by omega
    have hb := mul_le_mul (smallPrimeResidue_norm p K A hA j hj)
      (poleValue_coeff_norm p K ((j:ℤ)-K) hr n) (norm_nonneg _) (by positivity)
    apply hb.trans
    rw [← pow_add]
    apply pow_le_pow_right₀ (by exact_mod_cast hp.out.one_le)
    have hL := Nat.log_mono_right (le_max_left (2*K) (d+1)) (b:=p)
    have hK' : K≤max (2*K) (d+1) := by omega
    have hk := Nat.log_mono_right hK' (b:=p)
    omega

#print axioms smallPrimeQuotient_norm
#print axioms smallPrimeTauPolynomial_coeff_norm
end Zeta5Local
