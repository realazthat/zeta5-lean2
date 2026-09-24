import NearPoleSeries
import Mathlib.Analysis.SpecificLimits.Normed

namespace Zeta5Local
open Polynomial Filter Topology
variable {p : ℕ} [Fact p.Prime]

/-- Integral polynomial coefficients are precisely polynomials lifted from
Z_p. This packages the elementary closure operations without coefficient sums. -/
lemma integralCoeffs_iff_lifts (P : Polynomial ℚ_[p]) :
    (∀ n, ‖P.coeff n‖ ≤ 1) ↔ P ∈ Polynomial.lifts (PadicInt.subring p).subtype := by
  rw [Polynomial.lifts_iff_coeff_lifts]
  constructor
  · intro h n
    exact ⟨⟨P.coeff n, h n⟩, rfl⟩
  · intro h n
    obtain ⟨a, ha⟩ := h n
    rw [← ha]
    exact a.property

lemma integralCoeffs_mul {A B : Polynomial ℚ_[p]}
    (hA : ∀ n, ‖A.coeff n‖ ≤ 1) (hB : ∀ n, ‖B.coeff n‖ ≤ 1) :
    ∀ n, ‖(A * B).coeff n‖ ≤ 1 :=
  (integralCoeffs_iff_lifts _).mpr ((Polynomial.lifts _).mul_mem
    ((integralCoeffs_iff_lifts _).mp hA) ((integralCoeffs_iff_lifts _).mp hB))

lemma integralCoeffs_add {A B : Polynomial ℚ_[p]}
    (hA : ∀ n, ‖A.coeff n‖ ≤ 1) (hB : ∀ n, ‖B.coeff n‖ ≤ 1) :
    ∀ n, ‖(A + B).coeff n‖ ≤ 1 :=
  (integralCoeffs_iff_lifts _).mpr ((Polynomial.lifts _).add_mem
    ((integralCoeffs_iff_lifts _).mp hA) ((integralCoeffs_iff_lifts _).mp hB))

lemma integralCoeffs_C {a : ℚ_[p]} (ha : ‖a‖ ≤ 1) :
    ∀ n, ‖(C a).coeff n‖ ≤ 1 := by
  intro n
  rw [coeff_C]
  split_ifs
  · exact ha
  · norm_num

lemma integralCoeffs_pow {A : Polynomial ℚ_[p]}
    (hA : ∀ n, ‖A.coeff n‖ ≤ 1) (j : ℕ) :
    ∀ n, ‖(A ^ j).coeff n‖ ≤ 1 :=
  (integralCoeffs_iff_lifts _).mpr ((Polynomial.lifts _).pow_mem
    ((integralCoeffs_iff_lifts _).mp hA) j)

/-- Any finite product of far linear (or polynomial) factors is a unit
constant plus p times an integral polynomial. -/
theorem farUnit_product_form {ι : Type*} (s : Finset ι)
    (u : ι → ℚ_[p]) (V : ι → Polynomial ℚ_[p])
    (hu : ∀ i ∈ s, ‖u i‖ = 1) (hV : ∀ i ∈ s, ∀ n, ‖(V i).coeff n‖ ≤ 1) :
    ∃ W : Polynomial ℚ_[p], (∀ n, ‖W.coeff n‖ ≤ 1) ∧
      (∏ i ∈ s, (C (u i) + C (p : ℚ_[p]) * V i)) =
        C (∏ i ∈ s, u i) + C (p : ℚ_[p]) * W := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨W, hW, he⟩ := ih (fun k hk => hu k (Finset.mem_insert_of_mem hk))
      (fun k hk => hV k (Finset.mem_insert_of_mem hk))
    have hiu := hu i (Finset.mem_insert_self i s)
    have hiv := hV i (Finset.mem_insert_self i s)
    have hsunit : ‖∏ k ∈ s, u k‖ = 1 := by
      rw [norm_prod]
      exact Finset.prod_eq_one (fun k hk => hu k (Finset.mem_insert_of_mem hk))
    refine ⟨C (u i) * W + C (∏ k ∈ s, u k) * V i + C (p : ℚ_[p]) * (V i * W), ?_, ?_⟩
    · exact integralCoeffs_add
        (integralCoeffs_add (integralCoeffs_mul (integralCoeffs_C hiu.le) hW)
          (integralCoeffs_mul (integralCoeffs_C hsunit.le) hiv))
        (integralCoeffs_mul (integralCoeffs_C Padic.norm_p_lt_one.le)
          (integralCoeffs_mul hiv hW))
    · rw [Finset.prod_insert hi, Finset.prod_insert hi, he, map_mul]
      ring

/-- The whole numerator is retained in every term. Consequently a common
power of p dividing that numerator is never lost by partial fractions. -/
noncomputable def farUnitExpansion (A V : Polynomial ℚ_[p]) (u : ℚ_[p])
    (j : ℕ) : Polynomial ℚ_[p] := C (u⁻¹ ^ (j + 1)) * A * (-V) ^ j

lemma farUnitExpansion_integral (A V : Polynomial ℚ_[p]) (u : ℚ_[p])
    (hA : ∀ n, ‖A.coeff n‖ ≤ 1) (hV : ∀ n, ‖V.coeff n‖ ≤ 1)
    (hu : ‖u‖ = 1) (j n : ℕ) : ‖(farUnitExpansion A V u j).coeff n‖ ≤ 1 := by
  apply integralCoeffs_mul _ _ n
  · apply integralCoeffs_mul _ hA
    apply integralCoeffs_C
    simp [norm_pow, norm_inv, hu]
  · apply integralCoeffs_pow
    intro k
    simpa only [coeff_neg, norm_neg] using hV k

lemma farUnitExpansion_zero_degree (A V : Polynomial ℚ_[p]) (u : ℚ_[p]) :
    (farUnitExpansion A V u 0).natDegree ≤ A.natDegree := by
  simp only [farUnitExpansion, zero_add, pow_one, pow_zero, mul_one]
  exact natDegree_C_mul_le _ _

/-- Geometric expansion of an arbitrary far-unit denominator. No degree
restriction is imposed on later terms, and equality is an actual convergent
p-adic sum, not merely a formal symbolic expansion. -/
theorem farUnitExpansion_hasSum (A V : Polynomial ℚ_[p]) (u x : ℚ_[p])
    (hV : ∀ n, ‖V.coeff n‖ ≤ 1) (hu : ‖u‖ = 1) (hx : ‖x‖ ≤ 1) :
    HasSum (fun j => (p : ℚ_[p]) ^ j * (farUnitExpansion A V u j).eval x)
      (A.eval x / (u + p * V.eval x)) := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hq : ‖-(p : ℚ_[p]) * V.eval x / u‖ < 1 := by
    rw [norm_div, norm_mul, norm_neg, hu, div_one]
    exact (mul_le_of_le_one_right (norm_nonneg _) (integral_polynomial_eval V x hV hx)).trans_lt
      Padic.norm_p_lt_one
  have hh := (hasSum_geometric_of_norm_lt_one hq).mul_left (A.eval x / u)
  convert! hh using 1
  · funext j
    simp only [farUnitExpansion, eval_mul, eval_C, eval_pow, eval_neg,
      div_pow, mul_pow, pow_succ]
    ring
  · have hd : 1 - -(p : ℚ_[p]) * V.eval x / u ≠ 0 := by
      apply sub_ne_zero.mpr
      intro h
      rw [← h] at hq
      simpa using hq
    field_simp
    ring

/-- The same expansion with its complete near-pole denominator. -/
theorem farUnitExpansion_ratio_hasSum (A V T : Polynomial ℚ_[p]) (u x : ℚ_[p])
    (hV : ∀ n, ‖V.coeff n‖ ≤ 1) (hu : ‖u‖ = 1) (hx : ‖x‖ ≤ 1) :
    HasSum (fun j => (p : ℚ_[p]) ^ j *
      ((farUnitExpansion A V u j).eval x / T.eval x))
      (A.eval x / (T.eval x * (u + p * V.eval x))) := by
  have hh := (farUnitExpansion_hasSum A V u x hV hu hx).mul_right (T.eval x)⁻¹
  convert! hh using 1
  · funext j
    simp only [div_eq_mul_inv]
    ring
  · simp only [div_eq_mul_inv, mul_inv_rev]
    ring

/-- Lemma 3.1 applies directly to the whole-numerator expansion of a
far-unit denominator. Only the initial numerator degree matters. -/
theorem farUnitNearPoleSeries_integral {ι : Type*} [DecidableEq ι] (hp7 : 7 ≤ p)
    (A V : Polynomial ℚ_[p]) (u : ℚ_[p]) (s : Finset ι) (r : ι → ℚ_[p])
    (d : ι → ℕ) (Y : Polynomial ℚ_[p])
    (hA : ∀ n, ‖A.coeff n‖ ≤ 1) (hV : ∀ n, ‖V.coeff n‖ ≤ 1) (hu : ‖u‖ = 1)
    (hr : ∀ i, ‖r i‖ ≤ 1)
    (hsep : ∀ i ∈ s, ∀ j ∈ s.erase i, ‖r i - r j‖ = 1)
    (hd : ∀ i ∈ s, d i < p) (hY : ∀ n, ‖Y.coeff n‖ ≤ 1)
    (hdeg : A.natDegree ≤ p + 1) (n : ℕ) :
    ‖(nearPolePolynomialSeries (farUnitExpansion A V u) s r d Y).coeff n‖ ≤ 1 := by
  apply nearPolePolynomialSeries_integral hp7 _ s r d Y
    (farUnitExpansion_integral A V u hA hV hu) hr hsep hd hY
    ((farUnitExpansion_zero_degree A V u).trans hdeg) n

#print axioms farUnitExpansion_hasSum
#print axioms farUnitNearPoleSeries_integral
end Zeta5Local
