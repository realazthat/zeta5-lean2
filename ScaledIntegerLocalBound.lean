import LocalDiskValue

namespace Zeta5Local
open Polynomial
variable {p : ℕ} [Fact p.Prime]
variable {ι : Type*} [DecidableEq ι]

/-- Scalar form of the full normalized local theorem, indexed by the
original integer poles. Its conclusion is literally a local summand of the
actual distribution formula. -/
theorem scaled_integer_presentation_bound (hp7 : 7 ≤ p)
    (N E P A₀ A₁ V : Polynomial ℚ_[p]) (u α β y : ℚ_[p])
    (s near : Finset ι) (hne : near ⊆ s) (R : ι → ℤ) (a : ℤ)
    (c : ι → ℚ_[p]) (Ei : ι → Polynomial ℚ_[p])
    (hα : α ≠ 0) (hβ : β ≠ 0)
    (hN : N = C α*(A₀+C (p : ℚ_[p])*A₁))
    (hE : E = C β*poleDenominator near (fun i => ((R i-a : ℤ) : ℚ_[p])/(p : ℚ_[p]))*
      (C u+C (p : ℚ_[p])*V))
    (hEi : ∀ i ∈ s, E = (X-C (((R i-a : ℤ) : ℚ_[p])/(p : ℚ_[p])))*Ei i)
    (hidentity : N = E*P + ∑ i ∈ s, C (c i)*Ei i)
    (hA₀ : ∀ n, ‖A₀.coeff n‖ ≤ 1) (hA₁ : ∀ n, ‖A₁.coeff n‖ ≤ 1)
    (hV : ∀ n, ‖V.coeff n‖ ≤ 1) (hu : ‖u‖ = 1)
    (hnear : ∀ i ∈ s, i ∈ near ↔ (p : ℤ) ∣ R i-a)
    (hr : ∀ i ∈ near, ‖((R i-a : ℤ) : ℚ_[p])/(p : ℚ_[p])‖ ≤ 1)
    (hinj : Set.InjOn (fun i => ((R i-a : ℤ) : ℚ_[p])/(p : ℚ_[p])) near)
    (hsep : ∀ i ∈ near, ∀ j ∈ near.erase i,
      ‖((R i-a : ℤ) : ℚ_[p])/(p : ℚ_[p])-((R j-a : ℤ) : ℚ_[p])/(p : ℚ_[p])‖ = 1)
    (hd : ∀ i ∈ near, poleIndex ((R i-a)/(p : ℤ)) < p)
    (hy : ‖y‖ ≤ 1) (hdeg : A₀.natDegree ≤ p+1) :
    ‖(β/α)*(tauPolynomial P + ∑ i ∈ s, c i*residuePoleValue y (R i-a))‖ ≤ 1 := by
  have hfar (i : ι) (hi : i ∈ s\near) :
      1 < ‖((R i-a : ℤ) : ℚ_[p])/(p : ℚ_[p])‖ := by
    have hn : ¬(p : ℤ) ∣ R i-a := fun h => (Finset.mem_sdiff.mp hi).2
      ((hnear i (Finset.mem_sdiff.mp hi).1).mpr h)
    have he : ‖((R i-a : ℤ) : ℚ_[p])/(p : ℚ_[p])‖ = (p : ℝ) :=
      inv_injective (by simpa only [norm_inv] using farInteger_inverse_norm (R i-a) hn)
    rw [he]
    exact_mod_cast (Fact.out : p.Prime).one_lt
  have hh := normalized_disk_value_integral P s near hne (fun i => R i-a) c (C y)
    0 (β/α) (by norm_num) hnear (fun n =>
      scaled_presentation_local_bound hp7 N E P A₀ A₁ V u α β s near hne
        (fun i => ((R i-a : ℤ) : ℚ_[p])/(p : ℚ_[p])) c Ei
        (fun i => poleIndex ((R i-a)/(p : ℤ))) (C y)
        hα hβ hN hE hEi hidentity hA₀ hA₁ hV hu hr hinj hsep hfar hd
        (integralCoeffs_C hy) hdeg n)
  simpa only [eval_C] using hh

#print axioms scaled_integer_presentation_bound
end Zeta5Local
