import InnerPrimeCellBase

noncomputable section
namespace Zeta5InnerAsymptotics

theorem innerKernel_cell_000 (x : ℚ) (hl : 3≤x) (hr : x<(70/23)) :
    innerKernel x = (18/5)*x+-6 := by
  have hf0 : ⌊(23/10)*x⌋=(6:ℤ) := floor_linear_interval x 3 (70/23) (23/10) 6
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(0:ℤ) := floor_linear_interval x 3 (70/23) (3/20) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(6:ℤ) := floor_linear_interval x 3 (70/23) 2 6
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x 3 (70/23) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(3:ℤ) := floor_linear_interval x 3 (70/23) 1 3
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(5:ℤ) := floor_linear_interval x 3 (70/23) (37/20) 5
    hl hr (by norm_num) (by norm_num) (by norm_num)
  simp only [one_mul] at hf4
  unfold innerKernel gamma gammaAtAllocation baseIntegral baseConstant highKCoefficient
    highNCoefficient extraCost scalarLimit floorIntegral overlapLimit Int.fract
  rw [show 2*((37:ℚ)/40*x)=(37/20)*x by ring]
  simp only [Int.fract,hf0,hf1,hf2,hf3,hf4,hf5,one_mul]
  norm_num
  split_ifs <;> try { exfalso; linarith }
  all_goals
    repeat first
      | rw [min_eq_left (by linarith)]
      | rw [min_eq_right (by linarith)]
      | rw [max_eq_left (by linarith)]
      | rw [max_eq_right (by linarith)]
    ring


#print axioms innerKernel_cell_000
end Zeta5InnerAsymptotics
