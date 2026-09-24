import PaperParameters
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace Zeta5Parameters

lemma ordinaryClasses_mem (p a : ℕ) :
    a ∈ ordinaryClasses p ↔ a ∈ Finset.Icc 1 ((p-1)/2) := by
  simp only [ordinaryClasses, List.mem_map, List.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · rintro ⟨h1, ha⟩
    exact ⟨a-1, by omega, by omega⟩

lemma ordinaryClasses_nodup (p : ℕ) : (ordinaryClasses p).Nodup := by
  apply List.Nodup.map (fun a b hab => by omega)
  exact List.nodup_range

lemma prioritizedClasses_perm (n p : ℕ) :
    (prioritizedClasses n p).Perm (ordinaryClasses p) := List.mergeSort_perm _ _

lemma prioritizedClasses_mem (n p a : ℕ) :
    a ∈ prioritizedClasses n p ↔ a ∈ Finset.Icc 1 ((p-1)/2) :=
  (prioritizedClasses_perm n p).mem_iff.trans (ordinaryClasses_mem p a)

lemma prioritizedClasses_length (n p : ℕ) :
    (prioritizedClasses n p).length = (p-1)/2 := by
  rw [(prioritizedClasses_perm n p).length_eq]
  simp [ordinaryClasses]

theorem extra_sum (n M p : ℕ) (hp : 3 ≤ p) :
    ∑ a ∈ Finset.Icc 1 ((p-1)/2), extra n M p a = extraCount n M p := by
  let l := (prioritizedClasses n p).take (extraCount n M p)
  have hn : l.Nodup :=
    ((prioritizedClasses_perm n p).nodup_iff.mpr (ordinaryClasses_nodup p)).take
  have hsub : l.toFinset ⊆ Finset.Icc 1 ((p-1)/2) := by
    intro a ha
    exact (prioritizedClasses_mem n p a).mp
      (List.mem_of_mem_take (List.mem_toFinset.mp ha))
  have hfilter : (Finset.Icc 1 ((p-1)/2)).filter (fun a => a ∈ l) = l.toFinset := by
    ext a
    simp only [Finset.mem_filter, List.mem_toFinset]
    exact ⟨fun h => h.2, fun h => ⟨hsub (List.mem_toFinset.mpr h), h⟩⟩
  change ∑ a ∈ Finset.Icc 1 ((p-1)/2), (if a ∈ l then 1 else 0) = _
  rw [Finset.sum_boole, hfilter, List.toFinset_card_of_nodup hn]
  dsimp [l]
  rw [List.length_take, prioritizedClasses_length, Nat.min_eq_left]
  exact Nat.le_of_lt (Nat.mod_lt _ (by omega))

theorem base_extra_budget (n M p : ℕ) :
    ((p-1)/2) * baseAllocation n M p + extraCount n M p = allocationBudget n M p := by
  exact Nat.div_add_mod _ _

theorem admissible_zeroDimension_small {n M : ℕ} (ha : Admissible n M) :
    zeroDimension M ≤ 7*n := by
  obtain ⟨hM, hn⟩ := ha
  dsimp [zeroDimension, K] at *
  nlinarith [sq_nonneg (M : ℤ)]

/-- A convenient lower bound proving the paper's truncated subtraction is
ordinary subtraction: even the first part of the allocation budget suffices. -/
theorem baseAllocation_ge_three_poleCount {n M p a : ℕ}
    (ha : Admissible n M) (hp : 3 ≤ p) (hinner : 3*p ≤ K n)
    (hcount : p * poleCount (N n) p a ≤ 2*N n + p) :
    3*poleCount (N n) p a ≤ baseAllocation n M p := by
  have hz := admissible_zeroDimension_small ha
  have hB : 30*n ≤ allocationBudget n M p := by
    dsimp [allocationBudget, h]
    omega
  have hbudget := base_extra_budget n M p
  have hE : extraCount n M p < (p-1)/2 := Nat.mod_lt _ (by omega)
  have hm : 2*((p-1)/2) ≤ p := by omega
  by_contra hbad
  have hT : baseAllocation n M p + 1 ≤ 3*poleCount (N n) p a := by omega
  have hmul := Nat.mul_le_mul_left ((p-1)/2) hT
  have hmul' := Nat.mul_le_mul_right (3*poleCount (N n) p a) hm
  dsimp [K, N] at hcount hinner
  dsimp [N] at hT hmul hmul'
  nlinarith

theorem classDimension_sum (n M p : ℕ) (hp : 3 ≤ p)
    (hzero : zeroDimension M ≤ h n)
    (hbase : ∀ a ∈ Finset.Icc 1 ((p-1)/2),
      3*poleCount (N n) p a ≤ baseAllocation n M p)
    (hcount : ∑ a ∈ Finset.Icc 1 ((p-1)/2), poleCount (N n) p a = N n - N n / p) :
    zeroDimension M + ∑ a ∈ Finset.Icc 1 ((p-1)/2), classDimension n M p a = h n := by
  have hterm : ∀ a ∈ Finset.Icc 1 ((p-1)/2),
      classDimension n M p a + 3*poleCount (N n) p a =
      baseAllocation n M p + extra n M p a := by
    intro a ha
    dsimp [classDimension]
    have := hbase a ha
    omega
  have hsum := Finset.sum_congr rfl hterm
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hcount,
    extra_sum n M p hp, Finset.sum_const, nsmul_eq_mul, Nat.card_Icc] at hsum
  simp only [Nat.add_sub_cancel] at hsum
  norm_cast at hsum
  have hbudget := base_extra_budget n M p
  dsimp [allocationBudget] at hbudget
  omega

#print axioms extra_sum
#print axioms baseAllocation_ge_three_poleCount
#print axioms classDimension_sum

end Zeta5Parameters
