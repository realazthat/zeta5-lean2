import InnerAllocationLimit
import InnerRoots

noncomputable section
namespace Zeta5InnerDegrees
open Zeta5Parameters Zeta5InnerAsymptotics

lemma prime_large (n M p : ℕ) (ha : Admissible n M) (hcutoff : K n≤M*p) :
    200*M≤p := by
  obtain ⟨hM,hK⟩ := ha
  nlinarith

lemma poleCount_small (A p M : ℕ) (hp : 0<p) (hA : A≤M*p)
    (a : ℕ) (ha : 1≤a) (hap : 2*a<p) : poleCount A p a≤2*M+1 := by
  have hc := poleCount_mul_le A p a hp ha hap
  nlinarith

lemma classDimension_add_three (n M p a : ℕ) (ha : Admissible n M)
    (hp : 3≤p) (hinner : 3*p≤K n) (ha0 : 1≤a) (hap : 2*a<p) :
    classDimension n M p a+3*poleCount (N n) p a≤baseAllocation n M p+1 := by
  have hb := baseAllocation_ge_three_poleCount ha hp hinner
    (poleCount_mul_le (N n) p a (by omega) ha0 hap)
  have he : extra n M p a≤1 := by unfold extra; split_ifs <;> omega
  unfold classDimension
  omega

/-- The ordinary numerator degree restriction is discharged for every pair
of actual CRT rows, using only their orders at the source class. -/
theorem ordinary_degree_bound (n M p a u v : ℕ) (ha : Admissible n M)
    (hp : 3≤p) (hodd : p%2=1) (hinner : 3*p≤K n) (hcutoff : K n≤M*p)
    (ha0 : 1≤a) (hap : 2*a<p)
    (hu : u≤classDimension n M p a) (hv : v≤classDimension n M p a) :
    u+v+6*poleCount (N n) p a≤p+1 := by
  have hd := classDimension_add_three n M p a ha hp hinner ha0 hap
  have ht := actual_baseAllocation_le n M p hp hodd hcutoff
  have hl := prime_large n M p ha hcutoff
  have hm := ha.1
  omega

/-- A coarse bound suffices for the zero residue, avoiding sharp constants
that are irrelevant to the irrationality criterion. -/
theorem zero_degree_bound (n M p u v : ℕ) (ha : Admissible n M)
    (hp : 0<p) (hcutoff : K n≤M*p)
    (hu : u≤zeroDimension M) (hv : v≤zeroDimension M) :
    5+2*u+2*v+12*(N n/p)≤p+1 := by
  have hN : N n≤M*p := by unfold N K at *; omega
  have hdiv : N n/p≤M := (Nat.div_le_iff_le_mul hp).mpr (by omega)
  have hl := prime_large n M p ha hcutoff
  have hm := ha.1
  unfold zeroDimension at hu hv
  omega

theorem actual_near_root_bounds (n M p : ℕ) [Fact p.Prime]
    (ha : Admissible n M) (hcutoff : K n≤M*p)
    {c r s : ℤ} (hc0 : 0≤c) (hcp : c<p)
    (hr : -(K n:ℤ)≤r ∧ r≤K n) (hs : -(K n:ℤ)≤s ∧ s≤K n)
    (hrp : (p:ℤ)∣c-r) (hsp : (p:ℤ)∣c-s) (hrs : r≠s) :
    Zeta5Local.poleIndex (Zeta5InnerRoots.nearRoot p c r)<p ∧
    ‖((Zeta5InnerRoots.nearRoot p c r:ℚ_[p])-
       (Zeta5InnerRoots.nearRoot p c s:ℚ_[p]))‖=1 := by
  have hl := prime_large n M p ha hcutoff
  have hm := ha.1
  exact ⟨Zeta5InnerRoots.nearRoot_poleIndex_lt (Fact.out : p.Prime).pos
    hcutoff (by omega) hc0 hcp hr hrp,
    Zeta5InnerRoots.nearRoot_unit_separated hcutoff (by omega) hc0 hcp hr hs hrp hsp hrs⟩

#print axioms ordinary_degree_bound
#print axioms zero_degree_bound
end Zeta5InnerDegrees
