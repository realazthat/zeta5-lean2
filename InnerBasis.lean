import ClassBasis
import InnerDegrees

noncomputable section
open scoped BigOperators
namespace Zeta5InnerBasis
open Polynomial Zeta5Parameters Zeta5ClassBasis Zeta5InnerAsymptotics

def dimension (n M p : ℕ) (a : Fin ((p-1)/2+1)) : ℕ :=
  if a.val=0 then zeroDimension M else classDimension n M p a.val

def rowOrder (n M p : ℕ) (i : Σ a, Fin (dimension n M p a))
    (c : Fin ((p-1)/2+1)) : ℕ := if c=i.1 then i.2.val else dimension n M p c

lemma rowOrder_le (n M p : ℕ) (i : Σ a, Fin (dimension n M p a))
    (c : Fin ((p-1)/2+1)) : rowOrder n M p i c≤dimension n M p c := by
  unfold rowOrder
  split_ifs with he
  · subst c; exact i.2.isLt.le
  · rfl

lemma dimension_sum (n M p : ℕ) (ha : Admissible n M) (hp : 3≤p)
    (hodd : p%2=1) (hinner : 3*p≤K n) :
    (∑ a, dimension n M p a)=h n := by
  rw [Fin.sum_univ_succ]
  simp only [dimension, Fin.val_zero, if_true, Fin.val_succ, Nat.add_eq_zero_iff,
    one_ne_zero, and_false, if_false]
  have he : (∑ a ∈ Finset.range ((p-1)/2), classDimension n M p (a+1)) =
      ∑ a ∈ Finset.Icc 1 ((p-1)/2), classDimension n M p a := by
    apply Finset.sum_bij (fun a _ => a+1)
    · intro a ha
      simp only [Finset.mem_range, Finset.mem_Icc] at *
      omega
    · intro a ha b hb he
      omega
    · intro b hb
      have hb' := Finset.mem_Icc.mp hb
      exact ⟨b-1, by simpa only [Finset.mem_range] using (by omega : b-1<(p-1)/2), by omega⟩
    · intro a ha
      rfl
  rw [Fin.sum_univ_eq_sum_range (fun a => classDimension n M p (a+1)), he]
  exact actual_classDimension_sum n M p ha hp hodd hinner

def row (n M p : ℕ) (i : Σ a, Fin (dimension n M p a)) : ℤ[X] :=
  (∏ a ∈ Finset.univ.erase i.1, (X+C ((a.val:ℤ)^2))^dimension n M p a) *
    (X+C ((i.1.val:ℤ)^2))^i.2.val

lemma row_product (n M p : ℕ) (i : Σ a, Fin (dimension n M p a)) :
    row n M p i = ∏ a, (X+C ((a.val:ℤ)^2))^rowOrder n M p i a := by
  unfold row
  rw [←Finset.prod_erase_mul _ _ (Finset.mem_univ i.1)]
  congr 1
  · apply Finset.prod_congr rfl
    intro a ha
    simp only [rowOrder, (Finset.mem_erase.mp ha).1, if_false]
  · simp only [rowOrder, if_true]

lemma row_monic (n M p : ℕ) (i : Σ a, Fin (dimension n M p a)) :
    (row n M p i).Monic := by
  rw [row_product]
  exact monic_prod_of_monic _ _ (fun _ _ => (monic_X_add_C _).pow _)

lemma row_natDegree (n M p : ℕ) (i : Σ a, Fin (dimension n M p a)) :
    (row n M p i).natDegree = (∑ a, dimension n M p a)-dimension n M p i.1+i.2.val := by
  unfold row
  rw [natDegree_mul (monic_prod_of_monic _ _ (fun _ _ => (monic_X_add_C _).pow _)).ne_zero
    ((monic_X_add_C _).pow _).ne_zero,
    natDegree_prod_of_monic _ _ (fun _ _ => (monic_X_add_C _).pow _)]
  simp only [natDegree_pow, natDegree_X_add_C, mul_one]
  have he := Finset.sum_erase_add Finset.univ (dimension n M p) (Finset.mem_univ i.1)
  omega

def indexEquiv (n M p : ℕ) : (Σ a, Fin (dimension n M p a)) ≃ Fin (∑ a, dimension n M p a) :=
  Fintype.equivOfCardEq (by simp)

def basisMatrix (n M p : ℕ) : Matrix (Σ a, Fin (dimension n M p a))
    (Σ a, Fin (dimension n M p a)) ℤ :=
  fun i j => (row n M p i).coeff (indexEquiv n M p j).val

lemma basisMatrix_det_valuation (n M p : ℕ) [Fact p.Prime] (hp : p%2=1) :
    padicValInt p (basisMatrix n M p).det=0 := by
  exact inner_basis_unimodular p ((p-1)/2) (by omega) (dimension n M p) (indexEquiv n M p)

lemma ordinary_row_degree (n M p : ℕ) (ha : Admissible n M)
    (hp : 3≤p) (hodd : p%2=1) (hinner : 3*p≤K n) (hcutoff : K n≤M*p)
    (i j : Σ a, Fin (dimension n M p a)) (c : Fin ((p-1)/2+1)) (hc : c.val≠0) :
    rowOrder n M p i c+rowOrder n M p j c+6*poleCount (N n) p c.val≤p+1 := by
  have hi := rowOrder_le n M p i c
  have hj := rowOrder_le n M p j c
  simp only [dimension, hc, if_false] at hi hj
  exact Zeta5InnerDegrees.ordinary_degree_bound n M p c.val _ _ ha hp hodd hinner hcutoff
    (by omega) (by omega) hi hj

lemma zero_row_degree (n M p : ℕ) (ha : Admissible n M)
    (hp : 0<p) (hcutoff : K n≤M*p) (i j : Σ a, Fin (dimension n M p a)) :
    5+2*rowOrder n M p i 0+2*rowOrder n M p j 0+12*(N n/p)≤p+1 := by
  have hi := rowOrder_le n M p i 0
  have hj := rowOrder_le n M p j 0
  simp only [dimension, Fin.val_zero, if_true] at hi hj
  exact Zeta5InnerDegrees.zero_degree_bound n M p _ _ ha hp hcutoff hi hj

#print axioms basisMatrix_det_valuation
#print axioms ordinary_row_degree
end Zeta5InnerBasis
