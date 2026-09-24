import InnerDiskDegrees
import NearPoleSeries

noncomputable section
open scoped BigOperators
open Polynomial
namespace Zeta5InnerDisk
open Zeta5ResidueFactorization Zeta5InnerFactorization Zeta5InnerRoots Zeta5Local
open Zeta5Parameters Zeta5InnerBasis
variable {p : ℕ} [Fact p.Prime]

def padicMap (P : ℤ[X]) : Polynomial ℚ_[p] := P.map (Int.castRingHom ℚ_[p])

lemma padicMap_integral (P : ℤ[X]) (n : ℕ) : ‖(padicMap (p := p) P).coeff n‖ ≤ 1 := by
  rw [padicMap, coeff_map]
  exact Padic.norm_int_le_one _

lemma denominator_constant_norm (K : ℕ) (c : ℤ) :
    ‖((denFar K p c).coeff 0 : ℚ_[p])‖ = 1 := by
  apply le_antisymm (Padic.norm_int_le_one _)
  apply le_of_not_gt
  intro h
  exact denominator_constant_unit K p c ((Padic.norm_intCast_lt_one_iff).mp h)

theorem numerator_disk_split_padic (N m : ℕ) (c : ℤ) (ν κ : Fin (m+1) → ℕ) :
    (padicMap (p := p) (numeratorPullback N m ν κ)).comp (C (p:ℚ_[p])*X+C (c:ℚ_[p])) =
      C ((p:ℚ_[p])^(numeratorExponent N m p c ν κ))*
        (padicMap (leadingNumerator (numeratorNear N m p c ν κ) (numeratorFar N m p c ν κ))+
          C (p:ℚ_[p])*padicMap (higherNumerator p (numeratorNear N m p c ν κ) (numeratorFar N m p c ν κ))) := by
  have he := congrArg (Polynomial.map (Int.castRingHom ℚ_[p])) (numerator_disk_split N m p c ν κ)
  simpa only [Polynomial.map_comp, Polynomial.map_mul, Polynomial.map_add,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_pow, map_pow, Int.coe_castRingHom, map_intCast, Int.cast_natCast,
    shift, padicMap] using he

theorem denominator_disk_split_padic (K : ℕ) (c : ℤ) :
    (padicMap (p := p) (denPullback K)).comp (C (p:ℚ_[p])*X+C (c:ℚ_[p])) =
      C ((p:ℚ_[p])^denExponent K p c)*padicMap (denNear K p c)*
        (C ((denFar K p c).coeff 0 : ℚ_[p])+C (p:ℚ_[p])*padicMap (farRemainder p (denFar K p c))) := by
  have he := congrArg (Polynomial.map (Int.castRingHom ℚ_[p])) (denominator_disk_split K p c)
  simpa only [Polynomial.map_comp, Polynomial.map_mul, Polynomial.map_add,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_pow, map_pow, Int.coe_castRingHom, map_intCast, Int.cast_natCast,
    shift, padicMap] using he

lemma near_constant_eq_neg_root {c r : ℤ} (hr : (p:ℤ)∣c-r) :
    (c-r)/(p:ℤ) = -nearRoot p c r := by
  have hpz : (p:ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  apply mul_left_cancel₀ hpz
  have h1 := Int.mul_ediv_cancel' hr
  have h2 := nearRoot_mul hr
  linear_combination h1+h2

lemma denNear_padic_eq_poleDenominator (K : ℕ) (c : ℤ) :
    padicMap (p := p) (denNear K p c) =
      poleDenominator (nearIndices (signedIndices K) signedRoot p c)
        (fun j => (nearRoot p c (signedRoot j) : ℚ_[p])) := by
  unfold padicMap denNear nearPolynomial poleDenominator
  rw [Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro j hj
  rw [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
    near_constant_eq_neg_root (Finset.mem_filter.mp hj).2]
  simp [sub_eq_add_neg]

/-- The leading numerator degree and coefficient-integrality hypotheses of
the canonical local coefficient theorem hold for the actual CRT rows. -/
theorem actual_leadingNumerator_padic_degree (n M : ℕ) (ha : Admissible n M)
    (hp : 3≤p) (hodd : p%2=1) (hinner : 3*p≤K n) (hcutoff : K n≤M*p)
    (i j : Σ a, Fin (dimension n M p a)) (c : Fin ((p-1)/2+1)) :
    (padicMap (p := p) (leadingNumerator
      (numeratorNear (N n) ((p-1)/2) p c.val (rowOrder n M p i) (rowOrder n M p j))
      (numeratorFar (N n) ((p-1)/2) p c.val (rowOrder n M p i) (rowOrder n M p j)))).natDegree ≤ p+1 :=
  natDegree_map_le.trans (actual_leadingNumerator_degree n M p ha hp hodd hinner hcutoff i j c)

/-- The exact rational identity on the residue disk, including a possibly
negative power of p. It is valid even at denominator zeros by field division. -/
theorem disk_quotient_eval (N K m : ℕ) (c : ℤ) (ν κ : Fin (m+1) → ℕ) (x : ℚ_[p]) :
    (padicMap (p := p) (numeratorPullback N m ν κ)).eval ((p:ℚ_[p])*x+c) /
      (padicMap (p := p) (denPullback K)).eval ((p:ℚ_[p])*x+c) =
      (p:ℚ_[p])^((numeratorExponent N m p c ν κ:ℤ)-(denExponent K p c:ℤ))*
        ((padicMap (leadingNumerator (numeratorNear N m p c ν κ) (numeratorFar N m p c ν κ))).eval x+
          (p:ℚ_[p])*(padicMap (higherNumerator p (numeratorNear N m p c ν κ) (numeratorFar N m p c ν κ))).eval x) /
        ((padicMap (denNear K p c)).eval x*
          (((denFar K p c).coeff 0:ℚ_[p])+(p:ℚ_[p])*(padicMap (farRemainder p (denFar K p c))).eval x)) := by
  have hn := congrArg (fun P : Polynomial ℚ_[p] => P.eval x) (numerator_disk_split_padic (p := p) N m c ν κ)
  have hd := congrArg (fun P : Polynomial ℚ_[p] => P.eval x) (denominator_disk_split_padic (p := p) K c)
  simp only [eval_comp, eval_mul, eval_add, eval_C, eval_X] at hn hd
  rw [hn, hd]
  have hp0 : (p:ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [zpow_sub₀ hp0]
  simp only [zpow_natCast, div_eq_mul_inv, mul_inv_rev]
  ring

lemma nearRoots_injective (K : ℕ) (c : ℤ) :
    Set.InjOn (fun j => (nearRoot p c (signedRoot j):ℚ_[p]))
      (nearIndices (signedIndices K) signedRoot p c : Set (ℕ×Bool)) := by
  intro i hi j hj he
  have hi' := Finset.mem_filter.mp hi
  have hj' := Finset.mem_filter.mp hj
  apply signedRoot_inj K hi'.1 hj'.1
  exact nearRoot_injective hi'.2 hj'.2 (Int.cast_inj.mp he)

lemma nearRoots_integral (K : ℕ) (c : ℤ) (j : ℕ×Bool) :
    ‖(nearRoot p c (signedRoot j):ℚ_[p])‖ ≤ 1 := Padic.norm_int_le_one _

lemma actual_nearRoot_index (n M : ℕ) (ha : Admissible n M) (hcutoff : K n≤M*p)
    {c : ℤ} (hc0 : 0≤c) (hcp : c<p) {j : ℕ×Bool}
    (hj : j∈nearIndices (signedIndices (K n)) signedRoot p c) :
    Zeta5Local.poleIndex (nearRoot p c (signedRoot j))<p := by
  have hl := Zeta5InnerDegrees.prime_large n M p ha hcutoff
  have hm := ha.1
  have hj' := Finset.mem_filter.mp hj
  exact nearRoot_poleIndex_lt (Fact.out : p.Prime).pos hcutoff (by omega) hc0 hcp
    (signedRoot_bound (K n) j hj'.1) hj'.2

lemma actual_nearRoots_separated (n M : ℕ) (ha : Admissible n M) (hcutoff : K n≤M*p)
    {c : ℤ} (hc0 : 0≤c) (hcp : c<p) {i j : ℕ×Bool}
    (hi : i∈nearIndices (signedIndices (K n)) signedRoot p c)
    (hj : j∈(nearIndices (signedIndices (K n)) signedRoot p c).erase i) :
    ‖((nearRoot p c (signedRoot i):ℚ_[p])-(nearRoot p c (signedRoot j):ℚ_[p]))‖=1 := by
  have hj0 := (Finset.mem_erase.mp hj).2
  have hi' := Finset.mem_filter.mp hi
  have hj' := Finset.mem_filter.mp hj0
  have hne : signedRoot i≠signedRoot j := by
    intro he
    exact (Finset.mem_erase.mp hj).1 (signedRoot_inj (K n) hi'.1 hj'.1 he).symm
  exact (Zeta5InnerDegrees.actual_near_root_bounds n M p ha hcutoff hc0 hcp
    (signedRoot_bound (K n) i hi'.1) (signedRoot_bound (K n) j hj'.1) hi'.2 hj'.2 hne).2

#print axioms disk_quotient_eval
#print axioms numerator_disk_split_padic
#print axioms denominator_disk_split_padic
#print axioms actual_leadingNumerator_padic_degree
end Zeta5InnerDisk

