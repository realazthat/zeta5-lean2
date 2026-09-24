import ResidueFactorization
import LocalFunctional
import Mathlib.NumberTheory.Padics.PadicNumbers

noncomputable section
namespace Zeta5InnerRoots
open Polynomial Zeta5ResidueFactorization

/-- Integer location of a pole inside a residue disk. -/
def nearRoot (p : ℕ) (c r : ℤ) : ℤ := (r-c)/(p:ℤ)

lemma nearRoot_mul {p : ℕ} {c r : ℤ} (h : (p:ℤ) ∣ c-r) :
    (p:ℤ)*nearRoot p c r = r-c := by
  have hd : (p:ℤ) ∣ r-c := by simpa only [neg_sub] using dvd_neg.mpr h
  exact Int.mul_ediv_cancel' hd

/-- All local roots lie in the interval [-M-1,M]. -/
lemma nearRoot_bounds {p M K : ℕ} (hp : 0<p) (hK : K≤M*p)
    {c r : ℤ} (hc0 : 0≤c) (hcp : c<p) (hr : -(K:ℤ)≤r ∧ r≤K)
    (h : (p:ℤ) ∣ c-r) :
    -(M:ℤ)-1 ≤ nearRoot p c r ∧ nearRoot p c r ≤ M := by
  have he := nearRoot_mul h
  have hpz : (0:ℤ)<p := by exact_mod_cast hp
  have hKz : (K:ℤ)≤(M:ℤ)*p := by exact_mod_cast hK
  constructor <;> nlinarith

lemma nearRoot_injective {p : ℕ} {c r s : ℤ}
    (hr : (p:ℤ)∣c-r) (hs : (p:ℤ)∣c-s)
    (he : nearRoot p c r = nearRoot p c s) : r=s := by
  have hr' := nearRoot_mul hr
  have hs' := nearRoot_mul hs
  rw [he] at hr'
  omega

lemma nearRoot_poleIndex_lt {p M K : ℕ} (hp : 0<p) (hK : K≤M*p) (hM : M+1<p)
    {c r : ℤ} (hc0 : 0≤c) (hcp : c<p) (hr : -(K:ℤ)≤r ∧ r≤K)
    (h : (p:ℤ)∣c-r) : Zeta5Local.poleIndex (nearRoot p c r)<p := by
  have hb := nearRoot_bounds hp hK hc0 hcp hr h
  unfold Zeta5Local.poleIndex
  split_ifs <;> omega

lemma nearRoot_unit_separated {p M K : ℕ} [Fact p.Prime]
    (hK : K≤M*p) (hM : 2*M+1<p)
    {c r s : ℤ} (hc0 : 0≤c) (hcp : c<p)
    (hr : -(K:ℤ)≤r ∧ r≤K) (hs : -(K:ℤ)≤s ∧ s≤K)
    (hrp : (p:ℤ)∣c-r) (hsp : (p:ℤ)∣c-s) (hrs : r≠s) :
    ‖((nearRoot p c r:ℚ_[p])-(nearRoot p c s:ℚ_[p]))‖=1 := by
  have hp := (Fact.out : p.Prime)
  have hb := nearRoot_bounds hp.pos hK hc0 hcp hr hrp
  have hb' := nearRoot_bounds hp.pos hK hc0 hcp hs hsp
  have hne : nearRoot p c r-nearRoot p c s≠0 := by
    intro he
    exact hrs (nearRoot_injective hrp hsp (sub_eq_zero.mp he))
  have hnot : ¬(p:ℤ)∣nearRoot p c r-nearRoot p c s := by
    intro hd
    have hd' : p ∣ (nearRoot p c r-nearRoot p c s).natAbs := (Int.natCast_dvd).mp hd
    have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hne) hd'
    have habs : (nearRoot p c r-nearRoot p c s).natAbs < p := by
      rw [← Nat.cast_lt (α:=ℤ), Int.natCast_natAbs]
      exact abs_lt.mpr (by constructor <;> omega)
    omega
  rw [← Int.cast_sub]
  apply le_antisymm (Padic.norm_int_le_one _)
  apply le_of_not_gt
  exact fun hh => hnot ((Padic.norm_intCast_lt_one_iff).mp hh)

#print axioms nearRoot_unit_separated
end Zeta5InnerRoots
