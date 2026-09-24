import InnerDiskPadic
import ActualPullbackCertificate
import IntegerPoleDistribution

noncomputable section
open scoped BigOperators
open Polynomial
namespace Zeta5InnerDisk
open Zeta5ResidueFactorization Zeta5InnerFactorization Zeta5InnerRoots Zeta5Local
open Zeta5Parameters
variable {p : ℕ} [Fact p.Prime]

def fullRoot {K : ℕ} (j : Fin K×Bool) : ℤ := if j.2 then -(j.1.val+1:ℤ) else j.1.val+1
def fullIndex {K : ℕ} (j : Fin K×Bool) : ℕ×Bool := (j.1.val+1,!j.2)
def fullNear (K p : ℕ) (c : ℤ) : Finset (Fin K×Bool) :=
  Finset.univ.filter fun j => (p:ℤ)∣fullRoot j-c
def fullNearRoot {K : ℕ} (p : ℕ) (c : ℤ) (j : Fin K×Bool) : ℤ := nearRoot p c (fullRoot j)
def fullLocalRoot {K : ℕ} (p : ℕ) [Fact p.Prime] (c : ℤ) (j : Fin K×Bool) : ℚ_[p] :=
  ((fullRoot j:ℚ_[p])-(c:ℚ_[p]))/(p:ℚ_[p])

lemma fullIndex_root {K : ℕ} (j : Fin K×Bool) : signedRoot (fullIndex j)=fullRoot j := by
  rcases j with ⟨j,b⟩
  cases b <;> simp [fullRoot, fullIndex, signedRoot]

lemma fullIndex_injective (K : ℕ) : Function.Injective (fullIndex (K := K)) := by
  rintro ⟨i,b⟩ ⟨j,d⟩ h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  have hij : i=j := Fin.ext (by simpa only [fullIndex, Nat.add_right_cancel_iff] using h1)
  subst j
  cases b <;> cases d <;> simp_all [fullIndex]

lemma fullIndex_mem {K : ℕ} (j : Fin K×Bool) : fullIndex j∈signedIndices K := by
  simp only [fullIndex, signedIndices, Finset.mem_product, Finset.mem_Icc, Finset.mem_univ, and_true]
  constructor <;> omega

lemma fullIndex_surjective {K : ℕ} (j : ℕ×Bool) (hj : j∈signedIndices K) :
    ∃ i : Fin K×Bool, fullIndex i=j := by
  have hj' := Finset.mem_Icc.mp (Finset.mem_product.mp hj).1
  refine ⟨(⟨j.1-1,by omega⟩,!j.2), ?_⟩
  apply Prod.ext
  · dsimp [fullIndex]
    omega
  · simp [fullIndex]

lemma fullNear_mem_iff {K : ℕ} (c : ℤ) (j : Fin K×Bool) :
    j∈fullNear K p c ↔ fullIndex j∈nearIndices (signedIndices K) signedRoot p c := by
  simp only [fullNear, Finset.mem_filter, Finset.mem_univ, true_and, nearIndices,
    fullIndex_mem, fullIndex_root, true_and]
  constructor <;> intro hd <;> simpa only [neg_sub] using dvd_neg.mpr hd

lemma fullRoot_eq_actualSignedRoot {K : ℕ} (j : Fin K×Bool) :
    (fullRoot j:ℚ)=actualSignedRoot 0 j := by
  rcases j with ⟨j,b⟩
  cases b <;> simp [fullRoot, actualSignedRoot, Zeta5Construction.poleIndex] <;> ring

lemma fullLocalRoot_eq_actual {K : ℕ} (c : ℤ) (j : Fin K×Bool) :
    fullLocalRoot p c j =
      ((actualSignedRoot 0 j:ℚ_[p])-(c:ℚ_[p]))/(p:ℚ_[p]) := by
  unfold fullLocalRoot
  rw [← fullRoot_eq_actualSignedRoot]
  norm_cast

lemma fullNearRoot_eq_local {K : ℕ} (c : ℤ) {j : Fin K×Bool} (hj : j∈fullNear K p c) :
    (fullNearRoot p c j:ℚ_[p])=fullLocalRoot p c j := by
  have hj' : (p:ℤ)∣fullRoot j-c := (Finset.mem_filter.mp hj).2
  have he := Int.mul_ediv_cancel' hj'
  have hp0 : (p:ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  unfold fullNearRoot nearRoot fullLocalRoot
  apply (eq_div_iff hp0).mpr
  exact_mod_cast (by simpa only [mul_comm] using he)

lemma denNear_padic_eq_full (K : ℕ) (c : ℤ) :
    padicMap (p := p) (denNear K p c) =
      poleDenominator (fullNear K p c) (fun j => (fullNearRoot p c j:ℚ_[p])) := by
  rw [denNear_padic_eq_poleDenominator]
  unfold poleDenominator
  symm
  apply Finset.prod_bij (fun j hj => fullIndex j)
  · intro j hj
    exact (fullNear_mem_iff c j).mp hj
  · intro i hi j hj he
    exact fullIndex_injective K he
  · intro j hj
    obtain ⟨i, rfl⟩ := fullIndex_surjective j (Finset.mem_filter.mp hj).1
    exact ⟨i,(fullNear_mem_iff c i).mpr hj,rfl⟩
  · intro j hj
    dsimp only
    rw [fullIndex_root]
    rfl

lemma fullNearRoot_integral {K : ℕ} (c : ℤ) (j : Fin K×Bool) :
    ‖(fullNearRoot p c j:ℚ_[p])‖ ≤ 1 := Padic.norm_int_le_one _

lemma fullLocalRoot_near_integral {K : ℕ} (c : ℤ) {j : Fin K×Bool}
    (hj : j∈fullNear K p c) : ‖fullLocalRoot p c j‖ ≤ 1 := by
  rw [← fullNearRoot_eq_local c hj]
  exact fullNearRoot_integral c j

lemma fullNearRoots_injective (K : ℕ) (c : ℤ) :
    Set.InjOn (fun j : Fin K×Bool => (fullNearRoot p c j:ℚ_[p])) (fullNear K p c) := by
  intro i hi j hj he
  apply fullIndex_injective K
  apply nearRoots_injective K c ((fullNear_mem_iff c i).mp hi) ((fullNear_mem_iff c j).mp hj)
  simpa only [fullIndex_root, fullNearRoot] using he

lemma fullLocalRoot_far_inverse_norm {K : ℕ} (c : ℤ) {j : Fin K×Bool}
    (hj : j∉fullNear K p c) : ‖(fullLocalRoot p c j)⁻¹‖=(p:ℝ)⁻¹ := by
  have hn : ¬(p:ℤ)∣fullRoot j-c := by simpa only [fullNear, Finset.mem_filter,
    Finset.mem_univ, true_and] using hj
  simpa only [fullLocalRoot, Int.cast_sub] using farInteger_inverse_norm (p := p) (fullRoot j-c) hn

lemma fullLocalRoot_far_inverse_lt_one {K : ℕ} (c : ℤ) {j : Fin K×Bool}
    (hj : j∉fullNear K p c) : ‖(fullLocalRoot p c j)⁻¹‖<1 := by
  rw [fullLocalRoot_far_inverse_norm c hj]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)

lemma fullLocalRoot_far_ne_zero {K : ℕ} (c : ℤ) {j : Fin K×Bool}
    (hj : j∉fullNear K p c) : fullLocalRoot p c j≠0 := by
  have hn := fullLocalRoot_far_inverse_norm c hj
  intro hz
  rw [hz, inv_zero, norm_zero] at hn
  have hp : (0:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  exact (ne_of_gt (inv_pos.mpr hp)) hn.symm

lemma actual_fullNearRoot_index (n M : ℕ) (ha : Admissible n M) (hcutoff : K n≤M*p)
    {c : ℤ} (hc0 : 0≤c) (hcp : c<p) {j : Fin (K n)×Bool}
    (hj : j∈fullNear (K n) p c) : Zeta5Local.poleIndex (fullNearRoot p c j)<p := by
  have he := actual_nearRoot_index n M ha hcutoff hc0 hcp ((fullNear_mem_iff c j).mp hj)
  simpa only [fullIndex_root, fullNearRoot] using he

lemma actual_fullNearRoots_separated (n M : ℕ) (ha : Admissible n M) (hcutoff : K n≤M*p)
    {c : ℤ} (hc0 : 0≤c) (hcp : c<p) {i j : Fin (K n)×Bool}
    (hi : i∈fullNear (K n) p c) (hj : j∈(fullNear (K n) p c).erase i) :
    ‖((fullNearRoot p c i:ℚ_[p])-(fullNearRoot p c j:ℚ_[p]))‖=1 := by
  have he := actual_nearRoots_separated n M ha hcutoff hc0 hcp
    ((fullNear_mem_iff c i).mp hi)
    (show fullIndex j∈(nearIndices (signedIndices (K n)) signedRoot p c).erase (fullIndex i) by
      apply Finset.mem_erase.mpr
      exact ⟨fun h => (Finset.mem_erase.mp hj).1 (fullIndex_injective (K n) h),
        (fullNear_mem_iff c j).mp (Finset.mem_erase.mp hj).2⟩)
  simpa only [fullIndex_root, fullNearRoot] using he

#print axioms denNear_padic_eq_full
#print axioms actual_fullNearRoots_separated
end Zeta5InnerDisk

