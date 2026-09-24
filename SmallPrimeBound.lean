import SmallPrimePullback
import SmallPrimeEntry
import InnerNormBridge

noncomputable section
open scoped BigOperators
open Polynomial Matrix
namespace Zeta5SmallPrimeDeterminant
open Zeta5Local Zeta5Construction Zeta5NumeratorFunctional Zeta5BasisTransfer Zeta5Outer

def qNumerator (N i j : ℕ) : ℚ[X] :=
  C ((((N.factorial:ℚ)^6)⁻¹)^2)*(denominator N^5*(smallPrimeQ i*smallPrimeQ j))

lemma smallPrimeEntry_eq_full (N h i j : ℕ) :
    smallPrimeEntryNumerator (N+h) N i j=fullSmallPrimeNumerator N h (qNumerator N i j) := by
  have he : denominator N*qNumerator N i j=smallPrimeF N i*smallPrimeF N j := by
    simp only [qNumerator,smallPrimeF,map_pow]
    ring
  rw [fullSmallPrimeNumerator,he]
  rfl

lemma smallPrimeMatrix_entry (N h : ℕ) (i j : Fin h) :
    smallPrimeMatrix N h i j=
      smallPrimeTauPolynomial (N+h) (smallPrimeEntryNumerator (N+h) N i j) := by
  rw [smallPrimeEntry_eq_full,smallPrimeTauPolynomial_full_pullback]
  simp only [smallPrimeMatrix,gram,qFunctional,Matrix.smul_apply,smul_eq_mul,
    LinearMap.comp_apply,LinearMap.mulLeft_apply]
  have hl := (numeratorFunctional N h polynomialFunctional).map_smul
    ((((N.factorial:ℚ)^6)⁻¹)^2) (denominator N^5*(smallPrimeQ i*smallPrimeQ j))
  simp only [smul_eq_C_mul,RingHom.id_apply] at hl
  rw [qNumerator,hl]
  have hs : entryScalar N h=((N+h).factorial:ℚ)^2*((((N.factorial:ℚ)^6)⁻¹)^2) := by
    simp only [entryScalar,←inv_pow,←pow_mul]
    norm_num
    ring
  rw [hs,map_mul,mul_assoc]

lemma smallPrimeMatrix_coeffLower (p N h : ℕ) [Fact p.Prime]
    (hK : 0<N+h) (hsize : 12*N+4*h+2≤5*(N+h)) (i j : Fin h) :
    CoeffLower (rationalPadicValuation p) (smallPrimeMatrix N h i j)
      (-((6*Nat.log p (5*(N+h))+padicValNat p 24:ℕ):ℚ)) := by
  have hb := Zeta5InnerNormBridge.coeffLower_of_cast_norm p (smallPrimeMatrix N h i j)
    (-((6*Nat.log p (5*(N+h))+padicValNat p 24:ℕ):ℤ)) (by
      intro k
      rw [smallPrimeMatrix_entry]
      simpa only [neg_neg,zpow_natCast] using smallPrime_entry_coeff_norm p (N+h) N h hK hsize i j k)
  simpa only [Int.cast_neg,Int.cast_natCast] using hb

/-- Equation (3.12), for every prime including two and three. -/
theorem normalizedDeterminant_small_prime_bound (p N h : ℕ) [Fact p.Prime]
    (hh : 0<h) (hsize : 12*N+4*h+2≤5*(N+h)) :
    CoeffLower (rationalPadicValuation p) (normalizedDeterminant N h)
      (-(h:ℚ)*(6*Nat.log p (5*(N+h))+padicValNat p 24)) := by
  let b : ℚ := (6*Nat.log p (5*(N+h))+padicValNat p 24:ℕ)
  have hm : ∀i j : Fin h, CoeffLower (rationalPadicValuation p)
      (smallPrimeMatrix N h i j) (-b/2+-b/2) := by
    intro i j
    convert smallPrimeMatrix_coeffLower p N h (by omega) hsize i j using 1 <;> dsimp [b] <;> ring
  have hd := weighted_det_bound (rationalPadicValuation p) (smallPrimeMatrix N h)
    (fun _ : Fin h => -b/2) hm
  rw [smallPrimeMatrix_det N h hh] at hd
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hd
  convert hd using 1 <;> dsimp [b] <;> push_cast <;> ring

open Zeta5Parameters in
/-- The actual small-prime branch of the paper's signed normalization exponent. -/
theorem actual_small_localExponent_bound (n M p : ℕ) [Fact p.Prime]
    (hn : 0<n) (hsmall : p*M≤K n) (k : ℕ)
    (hk : (normalizedDeterminant (N n) (Zeta5Parameters.h n)).coeff k≠0) :
    localExponent n M p ≤ padicValRat p
      ((normalizedDeterminant (N n) (Zeta5Parameters.h n)).coeff k) := by
  have hb := normalizedDeterminant_small_prime_bound p (N n) (Zeta5Parameters.h n)
    (by dsimp [Zeta5Parameters.h]; omega)
    (by dsimp [N,Zeta5Parameters.h]; omega)
  have hv := ((rationalPadicValuation_lower_iff p _ _).mp (hb k)).resolve_left hk
  rw [localExponent,if_pos hsmall]
  have hK : N n+Zeta5Parameters.h n=K n := by dsimp [N,Zeta5Parameters.h,K]; omega
  rw [hK] at hv
  have hvi : -(Zeta5Parameters.h n:ℤ)*(6*(Nat.log p (5*K n):ℤ)+(padicValNat p 24:ℤ)) ≤
      padicValRat p ((normalizedDeterminant (N n) (Zeta5Parameters.h n)).coeff k) := by
    apply (Int.cast_le (R:=ℚ)).mp
    simpa only [Int.cast_neg,Int.cast_mul,Int.cast_add,Int.cast_natCast,Int.cast_ofNat] using hv
  nlinarith [hvi]

#print axioms smallPrimeMatrix_entry
#print axioms normalizedDeterminant_small_prime_bound
#print axioms actual_small_localExponent_bound
end Zeta5SmallPrimeDeterminant
