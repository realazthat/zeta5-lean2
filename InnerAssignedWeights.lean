import InnerBasis
import Mathlib.Data.List.Sort

noncomputable section
open scoped BigOperators
namespace Zeta5InnerAssignedWeights
open Zeta5Parameters Zeta5InnerBasis Zeta5InnerAsymptotics

lemma prioritized_pairwise (n p : ℕ) :
    (prioritizedClasses n p).Pairwise (fun a b => poleCount (K n) p b≤poleCount (K n) p a) := by
  unfold prioritizedClasses
  simpa using List.pairwise_mergeSort (le:=fun a b => decide (poleCount (K n) p b≤poleCount (K n) p a))
    (fun a b c hab hbc => by simpa using le_trans (by simpa using hbc) (by simpa using hab))
    (fun a b => by simpa using (le_total (poleCount (K n) p b) (poleCount (K n) p a))) _

lemma extra_order (n M p a b : ℕ) (hb : b∈Finset.Icc 1 ((p-1)/2))
    (ha1 : extra n M p a=1) (hb0 : extra n M p b=0) :
    poleCount (K n) p b≤poleCount (K n) p a := by
  have ha : a∈(prioritizedClasses n p).take (extraCount n M p) := by
    unfold extra at ha1
    split_ifs at ha1 with h <;> simp_all
  have hb' : b∉(prioritizedClasses n p).take (extraCount n M p) := by
    unfold extra at hb0
    split_ifs at hb0 with h <;> simp_all
  have hbmem := (prioritizedClasses_mem n p b).mpr hb
  have hbd : b∈(prioritizedClasses n p).drop (extraCount n M p) := by
    have he := List.take_append_drop (extraCount n M p) (prioritizedClasses n p)
    rw [←he, List.mem_append] at hbmem
    exact hbmem.resolve_left hb'
  have hs := prioritized_pairwise n p
  rw [←List.take_append_drop (extraCount n M p) (prioritizedClasses n p), List.pairwise_append] at hs
  exact hs.2.2 a ha b hbd

lemma fold_min_le_initial {ι : Type*} (l : List ι) (f : ι→ℤ) (w : ℤ) :
    l.foldl (fun z a => min z (f a)) w≤w := by
  induction l generalizing w with
  | nil => rfl
  | cons a l ih => exact (ih _).trans (min_le_left _ _)

lemma fold_min_le_member {ι : Type*} (l : List ι) (f : ι→ℤ) (w : ℤ)
    (a : ι) (ha : a∈l) : l.foldl (fun z b => min z (f b)) w≤f a := by
  induction l generalizing w with
  | nil => simp at ha
  | cons b l ih =>
    rcases List.mem_cons.mp ha with rfl|ha
    · exact (fold_min_le_initial l f (min w (f a))).trans (min_le_right _ _)
    · exact ih _ ha

def twiceWeight (n M p : ℕ) (i : Σ a, Fin (dimension n M p a)) : ℤ :=
  if i.1.val=0 then twiceZeroWeight n M p i.2.val else twiceOrdinaryWeight n p i.1.val i.2.val

def ordinarySource (n M p : ℕ) (i : Σ a, Fin (dimension n M p a))
    (c : Fin ((p-1)/2+1)) : ℤ :=
  2*(rowOrder n M p i c:ℤ)+6*(poleCount (N n) p c.val:ℤ)-(poleCount (K n) p c.val:ℤ)-4

def zeroSource (n M p : ℕ) (i : Σ a, Fin (dimension n M p a)) : ℤ :=
  4*(rowOrder n M p i 0:ℤ)+12*(N n/p:ℤ)-2*(K n/p:ℤ)+1

lemma classDimension_identity (n M p a : ℕ) (ha : Admissible n M)
    (hp : 3≤p) (hinner : 3*p≤K n) (ha0 : 1≤a) (hap : 2*a<p) :
    (classDimension n M p a:ℤ)+3*(poleCount (N n) p a:ℤ)=
      (baseAllocation n M p:ℤ)+(extra n M p a:ℤ) := by
  have hb := baseAllocation_ge_three_poleCount ha hp hinner
    (poleCount_mul_le (N n) p a (by omega) ha0 hap)
  unfold classDimension
  omega

lemma ordinary_source_bound (n M p : ℕ) (ha : Admissible n M)
    (hp : 3≤p) (hinner : 3*p≤K n)
    (i : Σ a, Fin (dimension n M p a)) (c : Fin ((p-1)/2+1)) (hc : c.val≠0) :
    twiceWeight n M p i≤ordinarySource n M p i c := by
  by_cases hi : i.1.val=0
  · have hne : c≠i.1 := by intro he; rw [he,hi] at hc; exact hc rfl
    simp only [twiceWeight, hi, if_true, ordinarySource, rowOrder, hne, if_false,
      dimension, hc]
    unfold twiceZeroWeight
    have hh := fold_min_le_member (ordinaryClasses p)
      (fun a => 2*((classDimension n M p a:ℤ)+3*(poleCount (N n) p a:ℤ))-(poleCount (K n) p a:ℤ)-4)
      (4*(i.2.val:ℤ)+12*(N n/p:ℤ)-2*(K n/p:ℤ)+1) c.val
      ((ordinaryClasses_mem p c.val).mpr (by simp only [Finset.mem_Icc]; constructor <;> omega))
    convert hh using 1 <;> ring
  · by_cases hci : c=i.1
    · subst c
      simp [twiceWeight, hi, ordinarySource, rowOrder, twiceOrdinaryWeight]
    · have hcbase := classDimension_identity n M p c.val ha hp hinner (by omega) (by omega)
      have hibase := classDimension_identity n M p i.1.val ha hp hinner (by omega) (by omega)
      have hil : i.2.val<classDimension n M p i.1.val := by
        simpa [dimension,hi] using i.2.isLt
      have hcoun : poleCount (K n) p c.val≤poleCount (K n) p i.1.val+1 := by
        rcases actual_poleCount_two_values (K n) p c.val (by omega) (by omega) (by omega) with h|h <;>
          rcases actual_poleCount_two_values (K n) p i.1.val (by omega) (by omega) (by omega) with g|g <;> omega
      have hei : extra n M p i.1.val=0 ∨ extra n M p i.1.val=1 := by unfold extra; split_ifs <;> simp
      have hec : extra n M p c.val=0 ∨ extra n M p c.val=1 := by unfold extra; split_ifs <;> simp
      have horder : extra n M p i.1.val=1 → extra n M p c.val=0 →
          poleCount (K n) p c.val≤poleCount (K n) p i.1.val :=
        extra_order n M p i.1.val c.val (by simp only [Finset.mem_Icc]; constructor <;> omega)
      simp only [twiceWeight, hi, if_false, ordinarySource, rowOrder, hci, dimension, hc,
        twiceOrdinaryWeight]
      rcases hei with hei|hei <;> rcases hec with hec|hec <;> omega

lemma zero_source_bound (n M p : ℕ) (ha : Admissible n M) (hp : 3≤p)
    (hodd : p%2=1) (hinner : 3*p≤K n) (hcutoff : K n≤M*p)
    (i : Σ a, Fin (dimension n M p a)) : twiceWeight n M p i≤zeroSource n M p i := by
  by_cases hi : i.1.val=0
  · have he : i.1=0 := Fin.ext hi
    simp only [twiceWeight, hi, if_true, zeroSource, rowOrder, he, if_true]
    exact fold_min_le_initial _ _ _
  · have he : (0:Fin ((p-1)/2+1))≠i.1 := by intro he; rw [←he] at hi; exact hi rfl
    have hid := classDimension_identity n M p i.1.val ha hp hinner (by omega) (by omega)
    have hil : i.2.val<classDimension n M p i.1.val := by simpa [dimension,hi] using i.2.isLt
    have hT := actual_baseAllocation_le n M p hp hodd hcutoff
    have hex : extra n M p i.1.val≤1 := by unfold extra; split_ifs <;> omega
    have hK : K n/p≤M := by have := Nat.div_mul_le_self (K n) p; nlinarith
    have hKz : (K n:ℤ)/(p:ℤ)≤M := by exact_mod_cast hK
    have hNz : 0≤(N n:ℤ)/(p:ℤ) := Int.ediv_nonneg (by positivity) (by positivity)
    simp only [twiceWeight, hi, if_false, zeroSource, rowOrder, he, dimension,
      Fin.val_zero, if_true, twiceOrdinaryWeight, zeroDimension]
    omega

lemma sum_twiceWeight (n M p : ℕ) :
    (∑ i, twiceWeight n M p i)=innerExponent n M p := by
  rw [Fintype.sum_sigma, Fin.sum_univ_succ]
  simp only [twiceWeight, dimension, Fin.val_zero, if_true, Fin.val_succ,
    Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false]
  change (∑ i : Fin (zeroDimension M), twiceZeroWeight n M p i.val) +
    (∑ a : Fin ((p-1)/2), ∑ i : Fin (classDimension n M p (a.val+1)),
      twiceOrdinaryWeight n p (a.val+1) i.val) = _
  rw [Fin.sum_univ_eq_sum_range (twiceZeroWeight n M p)]
  have hf : ∀ a : ℕ, (∑ i : Fin (classDimension n M p a), twiceOrdinaryWeight n p a i.val) =
      ∑ i ∈ Finset.range (classDimension n M p a), twiceOrdinaryWeight n p a i :=
    fun a => Fin.sum_univ_eq_sum_range _ _
  simp_rw [hf]
  rw [Fin.sum_univ_eq_sum_range
    (fun a => ∑ i ∈ Finset.range (classDimension n M p (a+1)), twiceOrdinaryWeight n p (a+1) i)]
  unfold innerExponent
  congr 1
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

#print axioms sum_twiceWeight
#print axioms ordinary_source_bound
#print axioms zero_source_bound
end Zeta5InnerAssignedWeights
