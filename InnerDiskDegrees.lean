import InnerDiskFactorization

noncomputable section
open scoped BigOperators
open Polynomial
namespace Zeta5InnerDisk
open Zeta5ResidueFactorization Zeta5InnerFactorization Zeta5InnerRowFactors
open Zeta5Parameters Zeta5InnerBasis

lemma xNear_monic (p : ℕ) (c : ℤ) : (xNear p c).Monic := by
  unfold xNear
  split_ifs
  · exact (monic_X_add_C _).pow _
  · exact monic_one

lemma xNear_degree (p : ℕ) (c : ℤ) : (xNear p c).natDegree=xExponent p c := by
  unfold xNear xExponent
  split_ifs <;> simp only [natDegree_pow, natDegree_X_add_C, natDegree_one, mul_one]

lemma denNear_monic (A p : ℕ) (c : ℤ) : (denNear A p c).Monic :=
  nearPolynomial_monic _ _ _ _
lemma denNear_degree (A p : ℕ) (c : ℤ) :
    (denNear A p c).natDegree=denExponent A p c := nearPolynomial_degree _ _ _ _

lemma rowNear_monic (m : ℕ) (ν : Fin (m+1) → ℕ) (p : ℕ) (c : ℤ) :
    (rowNear m ν p c).Monic := nearWeightedPolynomial_monic _ _ _ _ _
lemma rowNear_degree (m : ℕ) (ν : Fin (m+1) → ℕ) (p : ℕ) (c : ℤ) :
    (rowNear m ν p c).natDegree=rowExponent m ν p c := nearWeightedPolynomial_degree _ _ _ _ _

lemma numeratorNear_monic (N m p : ℕ) (c : ℤ) (ν κ : Fin (m+1) → ℕ) :
    (numeratorNear N m p c ν κ).Monic :=
  (((xNear_monic p c).mul ((denNear_monic N p c).pow 6)).mul (rowNear_monic m ν p c)).mul
    (rowNear_monic m κ p c)

lemma numeratorNear_degree (N m p : ℕ) (c : ℤ) (ν κ : Fin (m+1) → ℕ) :
    (numeratorNear N m p c ν κ).natDegree=numeratorExponent N m p c ν κ := by
  unfold numeratorNear numeratorExponent
  rw [(((xNear_monic p c).mul ((denNear_monic N p c).pow 6)).mul
    (rowNear_monic m ν p c)).natDegree_mul (rowNear_monic m κ p c),
    ((xNear_monic p c).mul ((denNear_monic N p c).pow 6)).natDegree_mul (rowNear_monic m ν p c),
    (xNear_monic p c).natDegree_mul ((denNear_monic N p c).pow 6)]
  simp only [natDegree_pow, xNear_degree, denNear_degree, rowNear_degree]
  omega

lemma ordinary_numerator_exponent (N m p : ℕ) (ν κ : Fin (m+1) → ℕ)
    (hm : 2*m<p) (a : Fin (m+1)) (ha : a≠0) :
    numeratorExponent N m p a.val ν κ =
      ν a+κ a+6*poleCount N p a.val := by
  have ha0 : 0<a.val := by
    have : a.val≠0 := fun he => ha (Fin.ext he)
    omega
  have hap : 2*a.val<p := by omega
  have had : ¬(p:ℤ)∣(a.val:ℤ) := by
    rw [Int.natCast_dvd_natCast]
    exact Nat.not_dvd_of_pos_of_lt ha0 (by omega)
  have hN : denExponent N p a.val=poleCount N p a.val := by
    rw [← denNear_degree]
    exact ordinary_near_degree N p a.val (by omega) hap
  have hν : rowExponent m ν p a.val=ν a := by
    rw [← rowNear_degree]
    exact ordinary_degree m ν p hm a ha
  have hκ : rowExponent m κ p a.val=κ a := by
    rw [← rowNear_degree]
    exact ordinary_degree m κ p hm a ha
  unfold numeratorExponent xExponent
  rw [if_neg had, hN, hν, hκ]
  omega

lemma zero_numerator_exponent (N m p : ℕ) (ν κ : Fin (m+1) → ℕ)
    (hp : 0<p) (hm : 2*m<p) :
    numeratorExponent N m p 0 ν κ =
      5+2*ν 0+2*κ 0+12*(N/p) := by
  have hN : denExponent N p 0=2*(N/p) := by
    rw [← denNear_degree]
    exact zero_near_degree N p hp
  have hν : rowExponent m ν p 0=2*ν 0 := by
    rw [← rowNear_degree]
    exact zero_degree m ν p hm
  have hκ : rowExponent m κ p 0=2*κ 0 := by
    rw [← rowNear_degree]
    exact zero_degree m κ p hm
  unfold numeratorExponent xExponent
  rw [if_pos (dvd_zero _), hN, hν, hκ]
  omega

lemma rowPullback_eq_actual (n M p : ℕ) (i : Σ a, Fin (dimension n M p a)) :
    rowPullback ((p-1)/2) (rowOrder n M p i) = (row n M p i).comp (-(X^2)) := by
  rw [row_product]
  rfl

/-- The low-degree numerator condition is now proved for every pair of the
paper's actual CRT rows, at every residue class used by the inner-prime proof. -/
theorem actual_leadingNumerator_degree (n M p : ℕ) (ha : Admissible n M)
    (hp : 3≤p) (hodd : p%2=1) (hinner : 3*p≤K n) (hcutoff : K n≤M*p)
    (i j : Σ a, Fin (dimension n M p a)) (c : Fin ((p-1)/2+1)) :
    (leadingNumerator
      (numeratorNear (N n) ((p-1)/2) p c.val (rowOrder n M p i) (rowOrder n M p j))
      (numeratorFar (N n) ((p-1)/2) p c.val (rowOrder n M p i) (rowOrder n M p j))).natDegree ≤ p+1 := by
  apply (leadingNumerator_degree_le _ _).trans
  rw [numeratorNear_degree]
  have hm : 2*((p-1)/2)<p := by omega
  by_cases hc : c=0
  · subst c
    simp only [Fin.val_zero, Int.natCast_zero]
    rw [zero_numerator_exponent _ _ _ _ _ (by omega) hm]
    exact zero_row_degree n M p ha (by omega) hcutoff i j
  · rw [ordinary_numerator_exponent _ _ _ _ _ hm c hc]
    exact ordinary_row_degree n M p ha hp hodd hinner hcutoff i j c (by simpa using hc)

lemma denExponent_reflect (A p a : ℕ) (ha : a≤p) :
    denExponent A p (p-a:ℕ)=denExponent A p a := by
  unfold denExponent
  rw [near_card, near_card]
  exact Zeta5InnerFactorCounts.linearNearCount_reflect A p a ha

lemma rowExponent_reflect (m p a : ℕ) (ν : Fin (m+1)→ℕ) (ha : a≤p) :
    rowExponent m ν p (p-a:ℕ)=rowExponent m ν p a := by
  unfold rowExponent
  rw [near_weight_sum, near_weight_sum]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [Zeta5InnerFactorCounts.dvd_sub_iff_mod,
    Zeta5InnerFactorCounts.dvd_add_iff_mod p (p-a) b.val (by omega),
    Zeta5InnerFactorCounts.dvd_add_iff_mod p a b.val ha, Nat.sub_sub_self ha]
  omega

lemma xExponent_reflect (p a : ℕ) (ha : a≤p) :
    xExponent p (p-a:ℕ)=xExponent p a := by
  have he : (p:ℤ)∣((p-a:ℕ):ℤ) ↔ (p:ℤ)∣(a:ℤ) := by
    rw [Nat.cast_sub ha]
    constructor
    · intro h
      have hd := dvd_sub (dvd_refl (p:ℤ)) h
      simpa only [sub_sub_cancel] using hd
    · intro h
      exact dvd_sub (dvd_refl _) h
  simp only [xExponent, he]

lemma numeratorExponent_reflect (N m p a : ℕ) (ν κ : Fin (m+1)→ℕ) (ha : a≤p) :
    numeratorExponent N m p (p-a:ℕ) ν κ=numeratorExponent N m p a ν κ := by
  simp only [numeratorExponent, xExponent_reflect p a ha,
    denExponent_reflect N p a ha, rowExponent_reflect m p a ν ha, rowExponent_reflect m p a κ ha]

lemma actual_numeratorExponent_bound (n M p : ℕ) (ha : Admissible n M)
    (hp : 3≤p) (hodd : p%2=1) (hinner : 3*p≤K n) (hcutoff : K n≤M*p)
    (i j : Σ a, Fin (dimension n M p a)) (c : Fin ((p-1)/2+1)) :
    numeratorExponent (N n) ((p-1)/2) p c.val (rowOrder n M p i) (rowOrder n M p j) ≤ p+1 := by
  have hm : 2*((p-1)/2)<p := by omega
  by_cases hc : c=0
  · subst c
    simp only [Fin.val_zero, Int.natCast_zero]
    rw [zero_numerator_exponent _ _ _ _ _ (by omega) hm]
    exact zero_row_degree n M p ha (by omega) hcutoff i j
  · rw [ordinary_numerator_exponent _ _ _ _ _ hm c hc]
    exact ordinary_row_degree n M p ha hp hodd hinner hcutoff i j c (by simpa using hc)

/-- Every residue in the distribution sum, including the reflected classes. -/
theorem actual_numeratorExponent_bound_all (n M p : ℕ) (ha : Admissible n M)
    (hp : 3≤p) (hodd : p%2=1) (hinner : 3*p≤K n) (hcutoff : K n≤M*p)
    (i j : Σ a, Fin (dimension n M p a)) (c : ℕ) (hc : c<p) :
    numeratorExponent (N n) ((p-1)/2) p c (rowOrder n M p i) (rowOrder n M p j) ≤ p+1 := by
  by_cases hc' : c≤(p-1)/2
  · exact actual_numeratorExponent_bound n M p ha hp hodd hinner hcutoff i j ⟨c,by omega⟩
  · let a : Fin ((p-1)/2+1) := ⟨p-c,by omega⟩
    have hap : a.val≤p := by dsimp [a]; omega
    have he : c=p-a.val := by dsimp [a]; omega
    rw [he, numeratorExponent_reflect _ _ _ _ _ _ hap]
    exact actual_numeratorExponent_bound n M p ha hp hodd hinner hcutoff i j a

theorem actual_leadingNumerator_degree_all (n M p : ℕ) (ha : Admissible n M)
    (hp : 3≤p) (hodd : p%2=1) (hinner : 3*p≤K n) (hcutoff : K n≤M*p)
    (i j : Σ a, Fin (dimension n M p a)) (c : ℕ) (hc : c<p) :
    (leadingNumerator
      (numeratorNear (N n) ((p-1)/2) p c (rowOrder n M p i) (rowOrder n M p j))
      (numeratorFar (N n) ((p-1)/2) p c (rowOrder n M p i) (rowOrder n M p j))).natDegree ≤ p+1 := by
  apply (leadingNumerator_degree_le _ _).trans
  rw [numeratorNear_degree]
  exact actual_numeratorExponent_bound_all n M p ha hp hodd hinner hcutoff i j c hc

#print axioms actual_leadingNumerator_degree_all
#print axioms actual_leadingNumerator_degree
end Zeta5InnerDisk

