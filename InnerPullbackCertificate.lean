import FullPullbackCertificate
import InnerDiskPadic

namespace Zeta5InnerDisk
open Polynomial Zeta5Construction Zeta5Local

noncomputable def innerEntryNumerator (N m : ℕ) (ν κ : Fin (m+1) → ℕ) : ℚ[X] :=
  denominator N^5 * (Zeta5InnerRowFactors.rowPolynomial m ν).map (Int.castRingHom ℚ) *
    (Zeta5InnerRowFactors.rowPolynomial m κ).map (Int.castRingHom ℚ)

lemma denPullback_map_rat (K : ℕ) :
    (denPullback K).map (Int.castRingHom ℚ) = (denominator K).comp (-(X^2)) := by
  simp only [denPullback, Polynomial.map_comp, Zeta5InnerFactorization.integerDenominator_map,
    Polynomial.map_neg, Polynomial.map_pow, Polynomial.map_X]

lemma numeratorPullback_map_rat (N m : ℕ) (ν κ : Fin (m+1) → ℕ) :
    (numeratorPullback N m ν κ).map (Int.castRingHom ℚ) =
      X^5*(denominator N*innerEntryNumerator N m ν κ).comp (-(X^2)) := by
  simp only [numeratorPullback, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, denPullback_map_rat, rowPullback, Polynomial.map_comp,
    Polynomial.map_neg, innerEntryNumerator, mul_comp, pow_comp]
  ring

lemma map_int_rat_padic {p : ℕ} [Fact p.Prime] (P : ℤ[X]) :
    (P.map (Int.castRingHom ℚ)).map (Rat.castHom ℚ_[p]) = padicMap (p := p) P := by
  rw [Polynomial.map_map]
  congr 1

lemma denPullback_map_padic {p : ℕ} [Fact p.Prime] (K : ℕ) :
    padicMap (p := p) (denPullback K) =
      ((denominator K).comp (-(X^2))).map (Rat.castHom ℚ_[p]) := by
  rw [←map_int_rat_padic, denPullback_map_rat]

lemma numeratorPullback_map_padic {p : ℕ} [Fact p.Prime]
    (N m : ℕ) (ν κ : Fin (m+1) → ℕ) :
    padicMap (p := p) (numeratorPullback N m ν κ) =
      (X^5*(denominator N*innerEntryNumerator N m ν κ).comp (-(X^2))).map
        (Rat.castHom ℚ_[p]) := by
  rw [←map_int_rat_padic, numeratorPullback_map_rat]

/-- The integer disk numerator and full denominator have exactly the
canonical affine μ-to-τ presentation, with the canceled residues zero. -/
theorem innerPullback_affine_certificate {p : ℕ} [Fact p.Prime]
    (N h m : ℕ) (ν κ : Fin (m+1) → ℕ) (c : ℤ) :
    (padicMap (p := p) (numeratorPullback N m ν κ)).comp (C (p:ℚ_[p])*X+C (c:ℚ_[p])) =
      (padicMap (p := p) (denPullback (N+h))).comp (C (p:ℚ_[p])*X+C (c:ℚ_[p])) *
        ((actualPullbackPolynomial N h (innerEntryNumerator N m ν κ)).map (Rat.castHom ℚ_[p])).comp
          (C (p:ℚ_[p])*X+C (c:ℚ_[p])) +
      ∑ ib : Fin (N+h) × Bool,
        C ((fullPullbackResidue N h (innerEntryNumerator N m ν κ) ib.1 : ℚ_[p])/(p:ℚ_[p])) *
          (C (p:ℚ_[p])*((actualSignedCofactor 0 (N+h) ib).map (Rat.castHom ℚ_[p])).comp
            (C (p:ℚ_[p])*X+C (c:ℚ_[p]))) := by
  rw [numeratorPullback_map_padic, denPullback_map_padic]
  simpa only [add_comm] using fullPullback_affine_certificate N h
    (innerEntryNumerator N m ν κ) (c:ℚ_[p]) (p:ℚ_[p])
    (by exact_mod_cast (Fact.out : p.Prime).ne_zero)

#print axioms innerPullback_affine_certificate
end Zeta5InnerDisk
