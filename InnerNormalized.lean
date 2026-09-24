import InnerExponentMatch
import OuterNormalized
import ActualInnerDiskBound

noncomputable section
namespace Zeta5InnerNormalized
open Zeta5Parameters Zeta5Construction Zeta5Outer Zeta5OuterNormalized Zeta5InnerDeterminant

lemma inner_geometry (n M p : ℕ) [Fact p.Prime] (ha : Admissible n M)
    (hsmall : K n<p*M) : 7≤p ∧ p%2=1 ∧ K n≤M*p := by
  have hcutoff : K n≤M*p := by nlinarith
  have hl := Zeta5InnerDegrees.prime_large n M p ha hcutoff
  have hM := ha.1
  have hp7 : 7≤p := by omega
  have hodd := (Fact.out:p.Prime).eq_two_or_odd.resolve_left (by omega)
  exact ⟨hp7,by omega,hcutoff⟩

lemma inner_localExponent_bound_of_entries (n M p : ℕ) [Fact p.Prime]
    (ha : Admissible n M) (hsmall : K n<p*M) (hinner : 3*p≤K n)
    (hentries : ∀ i j, CoeffLower (rationalPadicValuation p) (classMatrix n M p i j)
      (rowWeight n M p i+rowWeight n M p j)) (k : ℕ)
    (hk : (normalizedDeterminant (N n) (h n)).coeff k≠0) :
    localExponent n M p≤padicValRat p ((normalizedDeterminant (N n) (h n)).coeff k) := by
  obtain ⟨hp7,hodd,hcutoff⟩ := inner_geometry n M p ha hsmall
  have hd := determinant_bound_of_entries n M p ha (by omega) hodd hinner hentries
  have hn := determinant_coeff_ne_zero_of_normalized (N n) (h n) k hk
  have he : (innerExponent n M p:ℚ)≤(padicValRat p ((determinant (N n) (h n)).coeff k):ℚ) :=
    ((rationalPadicValuation_lower_iff p _ _).mp (hd k)).resolve_left hn
  rw [localExponent,if_neg (by omega),if_pos hinner,normalizedDeterminant_coeff_valuation p _ _ _ hk]
  have hei : innerExponent n M p≤padicValRat p ((determinant (N n) (h n)).coeff k) := by exact_mod_cast he
  omega

#print axioms inner_localExponent_bound_of_entries

/-- The inner-prime coefficient estimate for the actual normalized determinant.
All disk estimates, basis weights, and distribution identities are discharged. -/
theorem actual_inner_localExponent_bound (n M p : ℕ) [Fact p.Prime]
    (ha : Admissible n M) (hsmall : K n<p*M) (hinner : 3*p≤K n) (k : ℕ)
    (hk : (normalizedDeterminant (N n) (h n)).coeff k≠0) :
    localExponent n M p≤padicValRat p ((normalizedDeterminant (N n) (h n)).coeff k) := by
  obtain ⟨hp7,hodd,hcutoff⟩ := inner_geometry n M p ha hsmall
  apply inner_localExponent_bound_of_entries n M p ha hsmall hinner ?_ k hk
  apply Zeta5InnerSources.classMatrix_weighted_of_disk_bounds n M p ha hp7 hodd hinner hcutoff
  intro i j x hx c
  apply Zeta5InnerDisk.actual_disk_bound n M ha hp7 hodd hinner hcutoff i j (x:ℚ_[p]) ?_ c
  rcases hx with rfl | rfl <;> norm_num

#print axioms actual_inner_localExponent_bound
end Zeta5InnerNormalized
