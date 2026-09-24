import ActualPullbackCertificate

namespace Zeta5Local
open Polynomial Zeta5Construction

lemma tailDenominator_zero (h : ℕ) : tailDenominator 0 h = denominator h := by
  simpa [denominator] using (denominator_split 0 h).symm

/-- Residues at the canceled poles are zero. The surviving residues retain
exactly the normalization of the actual μ-to-τ presentation. -/
noncomputable def fullPullbackResidue (N h : ℕ) (A : ℚ[X]) : Fin (N+h) → ℚ :=
  Fin.addCases (fun _ : Fin N => 0) (actualPullbackResidue N A)

lemma fullSignedRoot_tail (N h : ℕ) (i : Fin h) (b : Bool) :
    actualSignedRoot 0 (Fin.natAdd N i, b) = actualSignedRoot N (i,b) := by
  have he : Zeta5Construction.poleIndex 0 (Fin.natAdd N i) =
      Zeta5Construction.poleIndex N i := by
    simp only [Zeta5Construction.poleIndex, Fin.val_natAdd]
    omega
  simp only [actualSignedRoot, he]

lemma fullSignedCofactor_tail (N h : ℕ) (i : Fin h) (b : Bool) :
    actualSignedCofactor 0 (N+h) (Fin.natAdd N i,b) =
      (denominator N).comp (-(X^2)) * actualSignedCofactor N h (i,b) := by
  have hf := actualSigned_factor 0 (N+h) (Fin.natAdd N i,b)
  rw [tailDenominator_zero, fullSignedRoot_tail] at hf
  have ht := actualSigned_factor N h (i,b)
  have hd : (denominator (N+h)).comp (-(X^2)) =
      (X-C (actualSignedRoot N (i,b))) *
        ((denominator N).comp (-(X^2)) * actualSignedCofactor N h (i,b)) := by
    rw [denominator_split, mul_comp, ht]
    ring
  exact mul_left_cancel₀ (monic_X_sub_C (actualSignedRoot N (i,b))).ne_zero
    (hf.symm.trans hd)

lemma fullPullback_residue_sum {R : Type*} [AddCommMonoid R]
    (N h : ℕ) (A : ℚ[X]) (f : ℚ → Fin (N+h) × Bool → R)
    (hf : ∀ ib, f 0 ib = 0) :
    (∑ ib : Fin (N+h) × Bool, f (fullPullbackResidue N h A ib.1) ib) =
      ∑ ib : Fin h × Bool, f (actualPullbackResidue N A ib.1) (Fin.natAdd N ib.1,ib.2) := by
  rw [Fintype.sum_prod_type, Fin.sum_univ_add, Fintype.sum_prod_type]
  simp [fullPullbackResidue, hf]

/-- Restoring all canceled signed poles gives a certificate with full
D_(N+h) denominator and the unchanged canonical polynomial quotient. -/
theorem fullPullback_certificate (N h : ℕ) (A : ℚ[X]) :
    X^5*(denominator N*A).comp (-(X^2)) =
      (denominator (N+h)).comp (-(X^2))*actualPullbackPolynomial N h A +
      ∑ ib : Fin (N+h) × Bool,
        C (fullPullbackResidue N h A ib.1)*actualSignedCofactor 0 (N+h) ib := by
  rw [fullPullback_residue_sum N h A (fun c ib => C c*actualSignedCofactor 0 (N+h) ib)
    (by intro ib; simp)]
  simp_rw [fullSignedCofactor_tail]
  have he := actualPullback_certificate N h A
  rw [denominator_split, mul_comp, mul_comp]
  calc
    X^5*((denominator N).comp (-(X^2))*A.comp (-(X^2))) =
        (denominator N).comp (-(X^2))*(X^5*A.comp (-(X^2))) := by ring
    _ = _ := by
      rw [he, mul_add, Finset.mul_sum]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro ib hib
        ring

lemma fullPullback_factor (N h : ℕ) (ib : Fin (N+h) × Bool) :
    (denominator (N+h)).comp (-(X^2)) =
      (X-C (actualSignedRoot 0 ib))*actualSignedCofactor 0 (N+h) ib := by
  simpa only [tailDenominator_zero] using actualSigned_factor 0 (N+h) ib


section FieldMap
variable {F : Type*} [Field F] [CharZero F]

/-- The restored certificate after a characteristic-zero field embedding. -/
theorem fullPullback_map_certificate (N h : ℕ) (A : ℚ[X]) :
    (X^5*(denominator N*A).comp (-(X^2))).map (Rat.castHom F) =
      ((denominator (N+h)).comp (-(X^2))).map (Rat.castHom F) *
        (actualPullbackPolynomial N h A).map (Rat.castHom F) +
      ∑ ib : Fin (N+h) × Bool, C (fullPullbackResidue N h A ib.1 : F)*
        (actualSignedCofactor 0 (N+h) ib).map (Rat.castHom F) := by
  have he := congrArg (Polynomial.map (Rat.castHom F)) (fullPullback_certificate N h A)
  simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sum,
    Polynomial.map_C, Rat.coe_castHom] using he

/-- Exact field-valued local affine certificate. Each residue acquires
precisely one inverse factor of the affine scale. -/
theorem fullPullback_affine_certificate (N h : ℕ) (A : ℚ[X]) (a b : F) (hb : b ≠ 0) :
    ((X^5*(denominator N*A).comp (-(X^2))).map (Rat.castHom F)).comp (C a+C b*X) =
      (((denominator (N+h)).comp (-(X^2))).map (Rat.castHom F)).comp (C a+C b*X) *
        ((actualPullbackPolynomial N h A).map (Rat.castHom F)).comp (C a+C b*X) +
      ∑ ib : Fin (N+h) × Bool, C ((fullPullbackResidue N h A ib.1 : F)/b)*
        (C b*((actualSignedCofactor 0 (N+h) ib).map (Rat.castHom F)).comp (C a+C b*X)) :=
  presentation_affine_identity _ _ _ Finset.univ _ _ a b hb
    (fullPullback_map_certificate N h A)

theorem fullPullback_affine_factor (N h : ℕ) (ib : Fin (N+h) × Bool)
    (a b : F) (hb : b ≠ 0) :
    (((denominator (N+h)).comp (-(X^2))).map (Rat.castHom F)).comp (C a+C b*X) =
      (X-C ((((actualSignedRoot 0 ib : ℚ) : F)-a)/b)) *
        (C b*((actualSignedCofactor 0 (N+h) ib).map (Rat.castHom F)).comp (C a+C b*X)) := by
  have he := congrArg (Polynomial.map (Rat.castHom F)) (fullPullback_factor N h ib)
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, Rat.coe_castHom] at he
  have hf := presentation_affine_factor _ _ (actualSignedRoot 0 ib : F) a b hb he
  exact hf
end FieldMap


/-- Integer roots with the same sign convention as `actualSignedRoot`. -/
def actualSignedIntegerRoot (N : ℕ) {h : ℕ} (ib : Fin h × Bool) : ℤ :=
  if ib.2 = true then -(Zeta5Construction.poleIndex N ib.1 : ℤ)
  else (Zeta5Construction.poleIndex N ib.1 : ℤ)

lemma actualSignedIntegerRoot_cast (N : ℕ) {h : ℕ} (ib : Fin h × Bool) :
    (actualSignedIntegerRoot N ib : ℚ) = actualSignedRoot N ib := by
  simp [actualSignedIntegerRoot, actualSignedRoot]

lemma fullSignedIntegerRoot_tail (N h : ℕ) (i : Fin h) (b : Bool) :
    actualSignedIntegerRoot 0 (Fin.natAdd N i,b) = actualSignedIntegerRoot N (i,b) := by
  have he : Zeta5Construction.poleIndex 0 (Fin.natAdd N i) =
      Zeta5Construction.poleIndex N i := by
    simp only [Zeta5Construction.poleIndex, Fin.val_natAdd]
    omega
  simp only [actualSignedIntegerRoot, he]

section PadicDistribution
variable {p : ℕ} [Fact p.Prime]

lemma fullPullback_pole_value_sum (N h : ℕ) (A : ℚ[X]) (Y : ℚ_[p]) (a : ℕ) :
    (∑ ib : Fin (N+h) × Bool, ((fullPullbackResidue N h A ib.1 : ℚ_[p])/(p : ℚ_[p]))*
      residuePoleValue Y (actualSignedIntegerRoot 0 ib-a)) =
    ∑ i : Fin h, ((actualPullbackResidue N A i : ℚ_[p])/(p : ℚ_[p]))*
      (residuePoleValue Y ((Zeta5Construction.poleIndex N i : ℤ)-a) +
       residuePoleValue Y (-(Zeta5Construction.poleIndex N i : ℤ)-a)) := by
  rw [fullPullback_residue_sum N h A
    (fun c ib => ((c : ℚ_[p])/(p : ℚ_[p]))*
      residuePoleValue Y (actualSignedIntegerRoot 0 ib-a)) (by intro ib; simp)]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [actualSignedIntegerRoot, Bool.false_eq_true, if_false, if_true]
  apply Finset.sum_congr rfl
  intro i hi
  have he : Zeta5Construction.poleIndex 0 (Fin.natAdd N i) =
      Zeta5Construction.poleIndex N i := by
    simp only [Zeta5Construction.poleIndex, Fin.val_natAdd]
    omega
  rw [he]
  ring

/-- The actual distribution formula indexed by every pole of the full
D_K denominator. The added poles contribute zero, including in near disks. -/
theorem fullPullback_padic_distribution (hp7 : 7 ≤ p)
    (N h : ℕ) (A : ℚ[X]) (x : ℚ_[p]) :
    (Zeta5NumeratorFunctional.numeratorFunctional N h Zeta5Construction.polynomialFunctional A).eval₂
      (Rat.castHom ℚ_[p]) x =
    (p : ℚ_[p])⁻¹^4 * ∑ a ∈ Finset.range p,
      ((rationalTauFunctional ((actualPullbackPolynomial N h A).comp
        (C (a : ℚ)+C (p : ℚ)*X)) : ℚ_[p]) +
        ∑ ib : Fin (N+h) × Bool, ((fullPullbackResidue N h A ib.1 : ℚ_[p])/(p : ℚ_[p]))*
          residuePoleValue ((p : ℚ_[p])^5*x+distributionConstant p)
            (actualSignedIntegerRoot 0 ib-a)) := by
  simp_rw [fullPullback_pole_value_sum]
  exact numeratorFunctional_padic_distribution hp7 N h A x
end PadicDistribution

#print axioms fullPullback_certificate
#print axioms fullPullback_affine_certificate
#print axioms fullPullback_padic_distribution
end Zeta5Local
