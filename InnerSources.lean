import InnerDistributionBound

noncomputable section
open scoped BigOperators
namespace Zeta5InnerSources
open Zeta5Parameters Zeta5InnerBasis Zeta5InnerAssignedWeights Zeta5InnerDeterminant
open Zeta5InnerDistributionBound Zeta5Outer

def sourceClass (p : ℕ) (hodd : p%2=1) (c : Fin p) : Fin ((p-1)/2+1) :=
  ⟨min c.val (p-c.val), by have hc := c.isLt; omega⟩

lemma sourceClass_zero_iff (p : ℕ) (hodd : p%2=1) (c : Fin p) :
    (sourceClass p hodd c).val=0 ↔ c.val=0 := by
  simp only [sourceClass]
  have hc := c.isLt
  omega

lemma sourceClass_eq_or_reflect (p : ℕ) (hodd : p%2=1) (c : Fin p) :
    c.val=(sourceClass p hodd c).val ∨ c.val=p-(sourceClass p hodd c).val := by
  simp only [sourceClass]
  have hc := c.isLt
  omega

def sourceExponent (n M p : ℕ) (hodd : p%2=1) (i j : RowIndex n M p) (c : Fin p) : ℤ :=
  if c.val=0 then
    2*(rowOrder n M p i 0:ℤ)+2*(rowOrder n M p j 0:ℤ)+12*(N n/p:ℤ)-2*(K n/p:ℤ)+1
  else
    (rowOrder n M p i (sourceClass p hodd c):ℤ)+
    (rowOrder n M p j (sourceClass p hodd c):ℤ)+
    6*(poleCount (N n) p (sourceClass p hodd c).val:ℤ)-
    (poleCount (K n) p (sourceClass p hodd c).val:ℤ)-4

lemma sourceExponent_weight_bound (n M p : ℕ) (ha : Admissible n M) (hp : 3≤p)
    (hodd : p%2=1) (hinner : 3*p≤K n) (hcutoff : K n≤M*p)
    (i j : RowIndex n M p) (c : Fin p) :
    rowWeight n M p i+rowWeight n M p j≤(sourceExponent n M p hodd i j c:ℚ) := by
  have hh : twiceWeight n M p i+twiceWeight n M p j≤2*sourceExponent n M p hodd i j c := by
    by_cases hc : c.val=0
    · have hi := zero_source_bound n M p ha hp hodd hinner hcutoff i
      have hj := zero_source_bound n M p ha hp hodd hinner hcutoff j
      simp only [zeroSource] at hi hj
      simp only [sourceExponent, hc, if_true]
      omega
    · have hca : (sourceClass p hodd c).val≠0 := by exact fun h => hc ((sourceClass_zero_iff p hodd c).mp h)
      have hi := ordinary_source_bound n M p ha hp hinner i (sourceClass p hodd c) hca
      have hj := ordinary_source_bound n M p ha hp hinner j (sourceClass p hodd c) hca
      simp only [ordinarySource] at hi hj
      simp only [sourceExponent, hc, if_false]
      omega
  have hhq : (twiceWeight n M p i:ℚ)+(twiceWeight n M p j:ℚ)≤
      2*(sourceExponent n M p hodd i j c:ℚ) := by exact_mod_cast hh
  unfold rowWeight
  linarith

/-- Integer source bounds dominate the ceiling of the assigned half-weights. -/
lemma ceil_weight_le_source (n M p : ℕ) (ha : Admissible n M) (hp : 3≤p)
    (hodd : p%2=1) (hinner : 3*p≤K n) (hcutoff : K n≤M*p)
    (i j : RowIndex n M p) (c : Fin p) :
    ⌈rowWeight n M p i+rowWeight n M p j⌉≤sourceExponent n M p hodd i j c :=
  Int.ceil_le.mpr (sourceExponent_weight_bound n M p ha hp hodd hinner hcutoff i j c)

/-- All p-adic coefficient and distribution bookkeeping is discharged here;
only the source-local rational-function estimates remain to be instantiated. -/
theorem classMatrix_weighted_of_disk_bounds (n M p : ℕ) [Fact p.Prime]
    (ha : Admissible n M) (hp7 : 7≤p) (hodd : p%2=1)
    (hinner : 3*p≤K n) (hcutoff : K n≤M*p)
    (hdisk : ∀ i j : RowIndex n M p, ∀x : ℚ, x=0 ∨ x=1 → ∀c : Fin p,
      ‖diskValue (N n) (Zeta5Parameters.h n)
        (Zeta5Construction.denominator (N n)^5*
          ((row n M p i).map (Int.castRingHom ℚ)*(row n M p j).map (Int.castRingHom ℚ)))
        (x:ℚ_[p]) c.val‖≤(p:ℝ)^(-(sourceExponent n M p hodd i j c+4))) :
    ∀ i j, CoeffLower (rationalPadicValuation p) (classMatrix n M p i j)
      (rowWeight n M p i+rowWeight n M p j) := by
  intro i j
  have he := Int.le_ceil (rowWeight n M p i+rowWeight n M p j)
  apply coeffLower_mono (rationalPadicValuation p) ?_ he
  apply functional_coeffLower_of_disks hp7
  intro x hx a ha'
  let c : Fin p := ⟨a,Finset.mem_range.mp ha'⟩
  have hh := hdisk i j x hx c
  have hs := ceil_weight_le_source n M p ha (by omega) hodd hinner hcutoff i j c
  exact hh.trans ((zpow_le_zpow_iff_right₀ (by exact_mod_cast (Fact.out:p.Prime).one_lt : (1:ℝ)<p)).mpr (by omega))

#print axioms classMatrix_weighted_of_disk_bounds
end Zeta5InnerSources
