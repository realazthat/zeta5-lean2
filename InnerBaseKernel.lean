import InnerAsymptotics
import Mathlib.Tactic

noncomputable section
open Finset
namespace Zeta5InnerAsymptotics

private theorem sum_indicator_of_subset {S H : Finset ℕ} (hsub : H ⊆ S) :
    (∑ a ∈ S, if a ∈ H then (1:ℚ) else 0) = H.card := by
  rw [Finset.sum_boole]
  have hf : S.filter (fun a => a ∈ H) = H := by
    ext a
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
  rw [hf]

private theorem sum_two_indicators_of_subset {S H J : Finset ℕ}
    (hH : H ⊆ S) (hJ : J ⊆ S) :
    (∑ a ∈ S, (if a ∈ H then (1:ℚ) else 0) *
      (if a ∈ J then 1 else 0)) = (H ∩ J).card := by
  have he : ∀ a, (if a ∈ H then (1:ℚ) else 0) *
      (if a ∈ J then 1 else 0) = if a ∈ H ∩ J then 1 else 0 := by
    intro a
    by_cases ha : a ∈ H <;> by_cases hb : a ∈ J <;> simp [ha,hb]
  simp_rw [he]
  exact sum_indicator_of_subset (fun a ha => hH (Finset.mem_inter.mp ha).1)

/-- The complete ordinary base-allocation cost is controlled by three
literal finite interval counts, with no limiting assumption. -/
theorem actual_base_cost_expansion (A B p : ℕ) (T : ℚ) (hp : 0 < p) :
    (∑ a ∈ Finset.Icc 1 ((p-1)/2),
      (T-3*(Zeta5Parameters.poleCount A p a : ℚ)) *
      (T+3*(Zeta5Parameters.poleCount A p a : ℚ)-
        (Zeta5Parameters.poleCount B p a : ℚ)-5)) =
      (((p-1)/2 : ℕ) : ℚ) * baseConstant T (lowLevel A p) (lowLevel B p) +
      ((highClasses B p).card : ℚ) * highKCoefficient T (lowLevel A p) +
      ((highClasses A p).card : ℚ) * highNCoefficient (lowLevel A p) (lowLevel B p) +
      3*(((highClasses A p) ∩ (highClasses B p)).card : ℚ) := by
  let S := Finset.Icc 1 ((p-1)/2)
  let u : ℕ → ℚ := fun a => if a ∈ highClasses A p then 1 else 0
  let v : ℕ → ℚ := fun a => if a ∈ highClasses B p then 1 else 0
  have hN : ∀ a ∈ S, (Zeta5Parameters.poleCount A p a : ℚ) = lowLevel A p + u a := by
    intro a ha
    have hmem := Finset.mem_Icc.mp ha
    rw [poleCount_highClasses A p a hp (by omega) (by omega)]
    simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rfl
  have hK : ∀ a ∈ S, (Zeta5Parameters.poleCount B p a : ℚ) = lowLevel B p + v a := by
    intro a ha
    have hmem := Finset.mem_Icc.mp ha
    rw [poleCount_highClasses B p a hp (by omega) (by omega)]
    simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rfl
  have hu : ∀ a ∈ S, (u a)^2=u a := by
    intro a ha
    dsimp [u]
    split_ifs <;> norm_num
  have hsum := sum_base_cost_indicator_expansion S T (lowLevel A p) (lowLevel B p) u v hu
  have hsu : ∑ a ∈ S, u a = ((highClasses A p).card : ℚ) :=
    sum_indicator_of_subset (highClasses_subset A p hp)
  have hsv : ∑ a ∈ S, v a = ((highClasses B p).card : ℚ) :=
    sum_indicator_of_subset (highClasses_subset B p hp)
  have hsuv : ∑ a ∈ S, u a*v a = (((highClasses A p) ∩ (highClasses B p)).card : ℚ) :=
    sum_two_indicators_of_subset (highClasses_subset A p hp) (highClasses_subset B p hp)
  have hcard : S.card=(p-1)/2 := by simp [S]
  rw [hsu, hsv, hsuv, hcard] at hsum
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [hN a ha, hK a ha]

def baseMass (A B p : ℕ) (T : ℚ) : ℚ :=
  p*baseConstant T (lowLevel A p) (lowLevel B p)/2 +
  highMass B p*highKCoefficient T (lowLevel A p) +
  highMass A p*highNCoefficient (lowLevel A p) (lowLevel B p) +
  3*overlapMass A B p

/-- An explicit error bound for the actual ordinary residue-class sum.
For bounded K/p all coefficients on the right are uniformly bounded. -/
theorem actual_base_cost_error (A B p : ℕ) (T : ℚ) (hp : 0 < p) (hodd : p%2=1) :
    |(∑ a ∈ Finset.Icc 1 ((p-1)/2),
      (T-3*(Zeta5Parameters.poleCount A p a : ℚ)) *
      (T+3*(Zeta5Parameters.poleCount A p a : ℚ)-
        (Zeta5Parameters.poleCount B p a : ℚ)-5)) - baseMass A B p T| ≤
      |baseConstant T (lowLevel A p) (lowLevel B p)|/2 +
      |highKCoefficient T (lowLevel A p)| +
      |highNCoefficient (lowLevel A p) (lowLevel B p)|+3 := by
  rw [actual_base_cost_expansion A B p T hp]
  have hpq : (p:ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  have hhalf : |((((p-1)/2 : ℕ) : ℚ)-(p:ℚ)/2)| ≤ 1/2 := by
    have he : 2*((p-1)/2)+1=p := by omega
    have heq : 2*(((p-1)/2 : ℕ) : ℚ)+1=p := by exact_mod_cast he
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hN : |((highClasses A p).card : ℚ)-p*(highMass A p/p)| ≤ 1 := by
    rw [mul_div_cancel₀ _ hpq]
    exact (highClasses_card_error A p hp hodd).trans (by norm_num)
  have hK : |((highClasses B p).card : ℚ)-p*(highMass B p/p)| ≤ 1 := by
    rw [mul_div_cancel₀ _ hpq]
    exact (highClasses_card_error B p hp hodd).trans (by norm_num)
  have hB : |(((highClasses A p) ∩ (highClasses B p)).card : ℚ)-p*(overlapMass A B p/p)| ≤ 1 := by
    rw [mul_div_cancel₀ _ hpq]
    exact highClasses_inter_card_error A B p hp hodd
  have hest := base_cost_grid_error T (lowLevel A p) (lowLevel B p)
    (((p-1)/2 : ℕ) : ℚ) (highClasses A p).card (highClasses B p).card
    ((highClasses A p) ∩ (highClasses B p)).card p
    (highMass A p/p) (highMass B p/p) (overlapMass A B p/p) hhalf hN hK hB
  convert hest using 2
  unfold baseMass
  field_simp

#print axioms actual_base_cost_error
end Zeta5InnerAsymptotics
