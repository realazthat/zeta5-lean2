import InnerAsymptotics
import ResidueFactorization

noncomputable section
open scoped BigOperators
namespace Zeta5InnerFactorCounts
open Zeta5Parameters

lemma dvd_sub_iff_mod (p a j : ℕ) :
    ((p:ℤ)∣(a:ℤ)-j) ↔ j%p=a%p := Nat.modEq_iff_dvd.symm

lemma dvd_add_iff_mod (p a j : ℕ) (ha : a≤p) :
    ((p:ℤ)∣(a:ℤ)+j) ↔ j%p=(p-a)%p := by
  change _ ↔ Nat.ModEq p j (p-a)
  rw [Nat.modEq_iff_dvd, Int.natCast_sub ha]
  constructor
  · intro hd
    have he : (p:ℤ)-a-j=(p:ℤ)-((a:ℤ)+j) := by ring
    rw [he]
    exact dvd_sub (dvd_refl _) hd
  · intro hd
    have he : (a:ℤ)+j=(p:ℤ)-((p:ℤ)-a-j) := by ring
    rw [he]
    exact dvd_sub (dvd_refl _) hd

def linearNearCount (A p : ℕ) (c : ℤ) : ℕ :=
  ∑ j ∈ Finset.Icc 1 A,
    ((if (p:ℤ)∣c-j then 1 else 0)+(if (p:ℤ)∣c+j then 1 else 0))

lemma linearNearCount_ordinary (A p a : ℕ) (ha : 1≤a) (hap : 2*a<p) :
    linearNearCount A p a = poleCount A p a := by
  unfold linearNearCount poleCount
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [dvd_sub_iff_mod, dvd_add_iff_mod p a j (by omega)]
  have hex : ¬(j%p=a%p ∧ j%p=(p-a)%p) := by
    have ha' : a<p := by omega
    have hb' : p-a<p := by omega
    rw [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb']
    omega
  split_ifs <;> omega

lemma linearNearCount_reflect (A p a : ℕ) (hap : a≤p) :
    linearNearCount A p (p-a:ℕ) = linearNearCount A p a := by
  unfold linearNearCount
  apply Finset.sum_congr rfl
  intro j hj
  simp only [dvd_sub_iff_mod, dvd_add_iff_mod p (p-a) j (by omega),
    dvd_sub_iff_mod, dvd_add_iff_mod p a j hap, Nat.sub_sub_self hap]
  omega

lemma linearNearCount_zero (A p : ℕ) (hp : 0<p) :
    linearNearCount A p 0 = 2*(A/p) := by
  unfold linearNearCount
  simp only [zero_sub, zero_add, dvd_neg, Int.natCast_dvd_natCast]
  rw [Finset.sum_add_distrib]
  have hc : (∑ j ∈ Finset.Icc 1 A, if p∣j then 1 else 0)=A/p := by
    rw [←Finset.card_filter]
    have he : Finset.Icc 1 A = Finset.Ioc 0 A := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      omega
    rw [he]
    exact Nat.Ioc_filter_dvd_card_eq_div A p
  rw [hc]
  omega

#print axioms linearNearCount_ordinary
end Zeta5InnerFactorCounts
