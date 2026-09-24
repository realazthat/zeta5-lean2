import ScalarValuation
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace Zeta5InnerAsymptotics

private theorem floor_layer_count (h p i : ℕ) (hp : 0<p) (hi : i<h) :
    ((2*i/p:ℕ):ℚ) = ∑ j ∈ Finset.range (2*h/p),
      if (j+1)*p≤2*i then (1:ℚ) else 0 := by
  rw [Finset.sum_boole]
  have hle : 2*i/p≤2*h/p := Nat.div_le_div_right (by omega)
  have hf : (Finset.range (2*h/p)).filter (fun j => (j+1)*p≤2*i) =
      Finset.range (2*i/p) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    rw [← Nat.le_div_iff_mul_le hp]
    omega
  rw [hf,Finset.card_range]

private theorem floor_level_card (h p j : ℕ) :
    ((Finset.range h).filter (fun i => (j+1)*p≤2*i)).card = h-((j+1)*p+1)/2 := by
  have hf : (Finset.range h).filter (fun i => (j+1)*p≤2*i) =
      Finset.Ico (((j+1)*p+1)/2) h := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hf,Nat.card_Ico]

/-- Reverse the two finite sums by counting the horizontal levels of the
floor function. -/
theorem sum_floor_by_levels (h p : ℕ) (hp : 0<p) :
    (∑ i ∈ Finset.range h, ((2*i/p:ℕ):ℚ)) =
      ∑ j ∈ Finset.range (2*h/p), ((h-((j+1)*p+1)/2:ℕ):ℚ) := by
  calc
    _ = ∑ i ∈ Finset.range h, ∑ j ∈ Finset.range (2*h/p),
        if (j+1)*p≤2*i then (1:ℚ) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact floor_layer_count h p i hp (Finset.mem_range.mp hi)
    _ = ∑ j ∈ Finset.range (2*h/p), ∑ i ∈ Finset.range h,
        if (j+1)*p≤2*i then (1:ℚ) else 0 := Finset.sum_comm
    _ = _ := by simp only [Finset.sum_boole,floor_level_card]

private theorem floor_level_error (h p j : ℕ) (hp : 0<p) (hj : j<2*h/p) :
    |((h-((j+1)*p+1)/2:ℕ):ℚ)-((h:ℚ)-(p:ℚ)*(j+1)/2)|≤1 := by
  have hjp : (j+1)*p≤2*h := by
    apply (Nat.le_div_iff_mul_le hp).mp
    omega
  have hceil : ((j+1)*p+1)/2≤h := by omega
  have hc0 : (j+1)*p≤2*(((j+1)*p+1)/2) := by omega
  have hc1 : 2*(((j+1)*p+1)/2)≤(j+1)*p+1 := by omega
  have hc0q : ((j:ℚ)+1)*p≤2*((((j+1)*p+1)/2:ℕ):ℚ) := by exact_mod_cast hc0
  have hc1q : 2*((((j+1)*p+1)/2:ℕ):ℚ)≤((j:ℚ)+1)*p+1 := by exact_mod_cast hc1
  rw [Nat.cast_sub hceil, abs_le]
  constructor <;> nlinarith

private theorem sum_range_succ_rat (m : ℕ) :
    (∑ j ∈ Finset.range m, ((j:ℚ)+1)) = (m:ℚ)*((m:ℚ)+1)/2 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ,ih]; push_cast; ring

def floorIntegral (u : ℚ) : ℚ :=
  (⌊2*u⌋:ℚ)*u-(⌊2*u⌋:ℚ)*((⌊2*u⌋:ℚ)+1)/4

theorem floor_nat_ratio (A p : ℕ) :
    ⌊(A:ℚ)/p⌋ = ((A/p:ℕ):ℤ) := by
  rw [Int.floor_div_natCast]
  norm_cast

/-- Uniform finite-sum error in the scalar normalization, equation (5.7). -/
theorem floor_sum_error (h p : ℕ) (hp : 0<p) :
    |(∑ i ∈ Finset.range h, ((2*i/p:ℕ):ℚ))-(p:ℚ)*floorIntegral ((h:ℚ)/p)| ≤
      ((2*h/p:ℕ):ℚ) := by
  have hpq : (p:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hp)
  rw [sum_floor_by_levels h p hp]
  have hsum := Finset.abs_sum_le_sum_abs (s := Finset.range (2*h/p))
    (f := fun j => ((h-((j+1)*p+1)/2:ℕ):ℚ)-((h:ℚ)-(p:ℚ)*(j+1)/2))
  have hbound : (∑ j ∈ Finset.range (2*h/p),
      |((h-((j+1)*p+1)/2:ℕ):ℚ)-((h:ℚ)-(p:ℚ)*(j+1)/2)|) ≤ ((2*h/p:ℕ):ℚ) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (2*h/p), (1:ℚ) := Finset.sum_le_sum
        (fun j hj => floor_level_error h p j hp (Finset.mem_range.mp hj))
      _ = _ := by simp
  have hideal : (∑ j ∈ Finset.range (2*h/p), ((h:ℚ)-(p:ℚ)*(j+1)/2)) =
      (p:ℚ)*floorIntegral ((h:ℚ)/p) := by
    rw [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    rw [←Finset.sum_div,←Finset.mul_sum,sum_range_succ_rat]
    unfold floorIntegral
    have he : 2*((h:ℚ)/p)=((2*h:ℕ):ℚ)/p := by push_cast; ring
    rw [he,floor_nat_ratio]
    simp only [Int.cast_natCast]
    field_simp
    <;> ring
  rw [Finset.sum_sub_distrib,hideal] at hsum
  exact hsum.trans hbound

/-- The product in the scalar runs over i=1,...,h−1; its zero term may
be added without changing the sum. -/
theorem scalar_floor_sum_eq_range (h p : ℕ) :
    (∑ i ∈ Finset.range (h-1), (((2*(i+1))/p:ℕ):ℚ)) =
      ∑ i ∈ Finset.range h, ((2*i/p:ℕ):ℚ) := by
  cases h with
  | zero => simp
  | succ h =>
    simp only [Nat.add_sub_cancel]
    rw [Finset.sum_range_succ']
    simp

#print axioms floor_sum_error
end Zeta5InnerAsymptotics
