import ScaledIntegerLocalBound
import InnerPullbackCertificate
import InnerDiskRoots
import InnerExponentMatch
import ActualDiskValue

noncomputable section
open scoped BigOperators
open Polynomial
namespace Zeta5InnerDisk
open Zeta5Local Zeta5Parameters Zeta5InnerBasis Zeta5InnerDeterminant
variable {p : ℕ} [Fact p.Prime]

lemma fullRoot_eq_integerRoot {K : ℕ} (j : Fin K×Bool) :
    fullRoot j=actualSignedIntegerRoot 0 j := by
  apply Int.cast_injective (α := ℚ)
  rw [fullRoot_eq_actualSignedRoot, actualSignedIntegerRoot_cast]

lemma denNear_padic_eq_local (K : ℕ) (a : ℤ) :
    padicMap (p := p) (denNear K p a) = poleDenominator (fullNear K p a)
      (fun j => ((fullRoot j-a:ℤ):ℚ_[p])/(p:ℚ_[p])) := by
  rw [denNear_padic_eq_full]
  unfold poleDenominator
  apply Finset.prod_congr rfl
  intro j hj
  dsimp only
  rw [fullNearRoot_eq_local a hj]
  simp only [fullLocalRoot, Int.cast_sub]

/-- The actual cleared μ-presentation satisfies the canonical normalized
local estimate whenever its near roots satisfy the explicit separation and
harmonic-index conditions. -/
theorem inner_disk_normalized_bound (hp7 : 7≤p) (N h m : ℕ)
    (ν κ : Fin (m+1)→ℕ) (a : ℤ) (y : ℚ_[p]) (hy : ‖y‖≤1)
    (hsep : ∀i∈fullNear (N+h) p a, ∀j∈(fullNear (N+h) p a).erase i,
      ‖((fullNearRoot p a i:ℚ_[p])-(fullNearRoot p a j:ℚ_[p]))‖=1)
    (hd : ∀i∈fullNear (N+h) p a, Zeta5Local.poleIndex (fullNearRoot p a i)<p)
    (hdeg : (leadingNumerator (numeratorNear N m p a ν κ)
      (numeratorFar N m p a ν κ)).natDegree≤p+1) :
    ‖((p:ℚ_[p])^denExponent (N+h) p a/(p:ℚ_[p])^numeratorExponent N m p a ν κ)*
      (tauPolynomial (((actualPullbackPolynomial N h (innerEntryNumerator N m ν κ)).map
        (Rat.castHom ℚ_[p])).comp (C (p:ℚ_[p])*X+C (a:ℚ_[p])))+
       ∑ib : Fin (N+h)×Bool, ((fullPullbackResidue N h (innerEntryNumerator N m ν κ) ib.1:ℚ_[p])/(p:ℚ_[p]))*
          residuePoleValue y (actualSignedIntegerRoot 0 ib-a))‖≤1 := by
  have hp0 : (p:ℚ_[p])≠0 := by exact_mod_cast (Fact.out:p.Prime).ne_zero
  have he := scaled_integer_presentation_bound hp7
    ((padicMap (numeratorPullback N m ν κ)).comp (C (p:ℚ_[p])*X+C (a:ℚ_[p])))
    ((padicMap (denPullback (N+h))).comp (C (p:ℚ_[p])*X+C (a:ℚ_[p])))
    (((actualPullbackPolynomial N h (innerEntryNumerator N m ν κ)).map
      (Rat.castHom ℚ_[p])).comp (C (p:ℚ_[p])*X+C (a:ℚ_[p])))
    (padicMap (leadingNumerator (numeratorNear N m p a ν κ) (numeratorFar N m p a ν κ)))
    (padicMap (higherNumerator p (numeratorNear N m p a ν κ) (numeratorFar N m p a ν κ)))
    (padicMap (farRemainder p (denFar (N+h) p a)))
    ((denFar (N+h) p a).coeff 0:ℚ_[p])
    ((p:ℚ_[p])^numeratorExponent N m p a ν κ) ((p:ℚ_[p])^denExponent (N+h) p a) y
    Finset.univ (fullNear (N+h) p a) (Finset.subset_univ _) fullRoot a
    (fun ib => (fullPullbackResidue N h (innerEntryNumerator N m ν κ) ib.1:ℚ_[p])/(p:ℚ_[p]))
    (fun ib => C (p:ℚ_[p])*((actualSignedCofactor 0 (N+h) ib).map (Rat.castHom ℚ_[p])).comp
      (C (p:ℚ_[p])*X+C (a:ℚ_[p])))
    (pow_ne_zero _ hp0) (pow_ne_zero _ hp0)
    (numerator_disk_split_padic N m a ν κ)
    (by rw [denominator_disk_split_padic, denNear_padic_eq_local])
    (by
      intro ib hib
      rw [denPullback_map_padic]
      have hf := fullPullback_affine_factor N h ib (a:ℚ_[p]) (p:ℚ_[p]) hp0
      simpa only [add_comm, ←fullLocalRoot_eq_actual, fullLocalRoot, Int.cast_sub] using hf)
    (innerPullback_affine_certificate N h m ν κ a)
    (padicMap_integral _) (padicMap_integral _) (padicMap_integral _)
    (denominator_constant_norm (N+h) a)
    (by intro ib hib; simp only [fullNear, Finset.mem_filter, Finset.mem_univ, true_and])
    (by
      intro ib hib
      simpa only [fullLocalRoot, Int.cast_sub] using fullLocalRoot_near_integral a hib)
    (by
      intro ib hib jb hjb hEq
      apply fullNearRoots_injective (N+h) a hib hjb
      dsimp only
      rw [fullNearRoot_eq_local a hib, fullNearRoot_eq_local a hjb]
      simpa only [fullLocalRoot, Int.cast_sub] using hEq)
    (by
      intro ib hib jb hjb
      have hh := hsep ib hib jb hjb
      rw [fullNearRoot_eq_local a hib,
        fullNearRoot_eq_local a (Finset.mem_erase.mp hjb).2] at hh
      simpa only [fullLocalRoot, Int.cast_sub] using hh)
    (by intro ib hib; exact hd ib hib)
    hy (natDegree_map_le.trans hdeg)
  simpa only [fullRoot_eq_integerRoot] using he

lemma distributionParameter_value_integral (hp7 : 7≤p) (x : ℚ_[p]) (hx : ‖x‖≤1) :
    ‖(p:ℚ_[p])^5*x+distributionConstant p‖≤1 := by
  apply (IsUltrametricDist.norm_add_le_max _ _).trans
  apply max_le
  · rw [norm_mul, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) Padic.norm_p_lt_one.le)
      (norm_nonneg _) hx
  · exact distributionConstant_integral hp7

theorem actual_disk_normalized_bound (n M : ℕ) (ha : Admissible n M)
    (hp7 : 7≤p) (hodd : p%2=1) (hinner : 3*p≤K n) (hcutoff : K n≤M*p)
    (i j : RowIndex n M p) (x : ℚ_[p]) (hx : ‖x‖≤1) (c : Fin p) :
    ‖((p:ℚ_[p])^denExponent (K n) p c.val /
        (p:ℚ_[p])^numeratorExponent (N n) ((p-1)/2) p c.val
          (rowOrder n M p i) (rowOrder n M p j))*
      Zeta5InnerDistributionBound.diskValue (N n) (Zeta5Parameters.h n)
        (Zeta5Construction.denominator (N n)^5*
          ((row n M p i).map (Int.castRingHom ℚ)*(row n M p j).map (Int.castRingHom ℚ)))
        x c.val‖≤1 := by
  have hNK : N n+Zeta5Parameters.h n=K n := by dsimp [N,Zeta5Parameters.h,K]; omega
  have hc0 : (0:ℤ)≤c.val := by exact_mod_cast Nat.zero_le c.val
  have hcp : (c.val:ℤ)<p := by exact_mod_cast c.isLt
  have hs : ∀ib∈fullNear (N n+Zeta5Parameters.h n) p (c.val:ℤ),
      ∀jb∈(fullNear (N n+Zeta5Parameters.h n) p (c.val:ℤ)).erase ib,
      ‖((fullNearRoot p (c.val:ℤ) ib:ℚ_[p])-(fullNearRoot p (c.val:ℤ) jb:ℚ_[p]))‖=1 := by
    rw [hNK]
    intro ib hib jb hjb
    exact actual_fullNearRoots_separated n M ha hcutoff hc0 hcp hib hjb
  have hd : ∀ib∈fullNear (N n+Zeta5Parameters.h n) p (c.val:ℤ),
      Zeta5Local.poleIndex (fullNearRoot p (c.val:ℤ) ib)<p := by
    rw [hNK]
    intro ib hib
    exact actual_fullNearRoot_index n M ha hcutoff hc0 hcp hib
  have he := inner_disk_normalized_bound hp7 (N n) (Zeta5Parameters.h n) ((p-1)/2)
    (rowOrder n M p i) (rowOrder n M p j) (c.val:ℤ)
    ((p:ℚ_[p])^5*x+distributionConstant p) (distributionParameter_value_integral hp7 x hx)
    hs hd (actual_leadingNumerator_degree_all n M p ha (by omega) hodd hinner hcutoff i j c.val c.isLt)
  simp only [Int.cast_natCast] at he
  rw [actual_full_disk_value, hNK] at he
  have hrows : innerEntryNumerator (N n) ((p-1)/2) (rowOrder n M p i) (rowOrder n M p j)=
      Zeta5Construction.denominator (N n)^5*
        ((row n M p i).map (Int.castRingHom ℚ)*(row n M p j).map (Int.castRingHom ℚ)) := by
    rw [row_product n M p i, row_product n M p j]
    simp only [innerEntryNumerator, Zeta5InnerRowFactors.rowPolynomial, mul_assoc]
  rw [hrows] at he
  exact he

/-- Every actual inner-prime residue disk has the source exponent used in
the determinant weight argument. -/
theorem actual_disk_bound (n M : ℕ) (ha : Admissible n M)
    (hp7 : 7≤p) (hodd : p%2=1) (hinner : 3*p≤K n) (hcutoff : K n≤M*p)
    (i j : RowIndex n M p) (x : ℚ_[p]) (hx : ‖x‖≤1) (c : Fin p) :
    ‖Zeta5InnerDistributionBound.diskValue (N n) (Zeta5Parameters.h n)
        (Zeta5Construction.denominator (N n)^5*
          ((row n M p i).map (Int.castRingHom ℚ)*(row n M p j).map (Int.castRingHom ℚ)))
        x c.val‖≤(p:ℝ)^(-(Zeta5InnerSources.sourceExponent n M p hodd i j c+4)) := by
  have he := Zeta5InnerExponentMatch.norm_of_p_scaled_norm p _ _ _
    (actual_disk_normalized_bound n M ha hp7 hodd hinner hcutoff i j x hx c)
  have hexp := Zeta5InnerExponentMatch.actual_disk_exponent_eq_source n M p hodd i j c
  convert! he using 1
  congr 1
  omega

#print axioms inner_disk_normalized_bound
#print axioms actual_disk_bound
end Zeta5InnerDisk
