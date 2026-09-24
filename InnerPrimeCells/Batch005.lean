import InnerPrimeCellBase

set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

noncomputable section
namespace Zeta5InnerAsymptotics

theorem innerKernel_cell_045 (x : ℚ) (hl : (300/37)≤x) (hr : x<(190/23)) :
    innerKernel x = (157/20)*x+-86 := by
  have hf0 : ⌊(23/10)*x⌋=(18:ℤ) := floor_linear_interval x (300/37) (190/23) (23/10) 18
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(1:ℤ) := floor_linear_interval x (300/37) (190/23) (3/20) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(16:ℤ) := floor_linear_interval x (300/37) (190/23) 2 16
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (300/37) (190/23) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(8:ℤ) := floor_linear_interval x (300/37) (190/23) 1 8
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(15:ℤ) := floor_linear_interval x (300/37) (190/23) (37/20) 15
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

theorem innerKernel_cell_046 (x : ℚ) (hl : (190/23)≤x) (hr : x<(360/43)) :
    innerKernel x = (67/10)*x+(-153/2) := by
  have hf0 : ⌊(23/10)*x⌋=(19:ℤ) := floor_linear_interval x (190/23) (360/43) (23/10) 19
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(1:ℤ) := floor_linear_interval x (190/23) (360/43) (3/20) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(16:ℤ) := floor_linear_interval x (190/23) (360/43) 2 16
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (190/23) (360/43) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(8:ℤ) := floor_linear_interval x (190/23) (360/43) 1 8
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(15:ℤ) := floor_linear_interval x (190/23) (360/43) (37/20) 15
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

theorem innerKernel_cell_047 (x : ℚ) (hl : (360/43)≤x) (hr : x<(17/2)) :
    innerKernel x = (139/40)*x+(-99/2) := by
  have hf0 : ⌊(23/10)*x⌋=(19:ℤ) := floor_linear_interval x (360/43) (17/2) (23/10) 19
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(1:ℤ) := floor_linear_interval x (360/43) (17/2) (3/20) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(16:ℤ) := floor_linear_interval x (360/43) (17/2) 2 16
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (360/43) (17/2) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(8:ℤ) := floor_linear_interval x (360/43) (17/2) 1 8
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(15:ℤ) := floor_linear_interval x (360/43) (17/2) (37/20) 15
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

theorem innerKernel_cell_048 (x : ℚ) (hl : (17/2)≤x) (hr : x<(320/37)) :
    innerKernel x = (179/40)*x+-58 := by
  have hf0 : ⌊(23/10)*x⌋=(19:ℤ) := floor_linear_interval x (17/2) (320/37) (23/10) 19
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(1:ℤ) := floor_linear_interval x (17/2) (320/37) (3/20) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(17:ℤ) := floor_linear_interval x (17/2) (320/37) 2 17
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (17/2) (320/37) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(8:ℤ) := floor_linear_interval x (17/2) (320/37) 1 8
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(15:ℤ) := floor_linear_interval x (17/2) (320/37) (37/20) 15
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

theorem innerKernel_cell_049 (x : ℚ) (hl : (320/37)≤x) (hr : x<(200/23)) :
    innerKernel x = (91/10)*x+-98 := by
  have hf0 : ⌊(23/10)*x⌋=(19:ℤ) := floor_linear_interval x (320/37) (200/23) (23/10) 19
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(1:ℤ) := floor_linear_interval x (320/37) (200/23) (3/20) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(17:ℤ) := floor_linear_interval x (320/37) (200/23) 2 17
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (320/37) (200/23) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(8:ℤ) := floor_linear_interval x (320/37) (200/23) 1 8
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(16:ℤ) := floor_linear_interval x (320/37) (200/23) (37/20) 16
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

theorem innerKernel_cell_050 (x : ℚ) (hl : (200/23)≤x) (hr : x<(380/43)) :
    innerKernel x = (159/20)*x+-88 := by
  have hf0 : ⌊(23/10)*x⌋=(20:ℤ) := floor_linear_interval x (200/23) (380/43) (23/10) 20
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(1:ℤ) := floor_linear_interval x (200/23) (380/43) (3/20) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(17:ℤ) := floor_linear_interval x (200/23) (380/43) 2 17
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (200/23) (380/43) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(8:ℤ) := floor_linear_interval x (200/23) (380/43) 1 8
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(16:ℤ) := floor_linear_interval x (200/23) (380/43) (37/20) 16
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

theorem innerKernel_cell_051 (x : ℚ) (hl : (380/43)≤x) (hr : x<9) :
    innerKernel x = (159/20)*x+-88 := by
  have hf0 : ⌊(23/10)*x⌋=(20:ℤ) := floor_linear_interval x (380/43) 9 (23/10) 20
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(1:ℤ) := floor_linear_interval x (380/43) 9 (3/20) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(17:ℤ) := floor_linear_interval x (380/43) 9 2 17
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (380/43) 9 (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(8:ℤ) := floor_linear_interval x (380/43) 9 1 8
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(16:ℤ) := floor_linear_interval x (380/43) 9 (37/20) 16
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

theorem innerKernel_cell_052 (x : ℚ) (hl : 9≤x) (hr : x<(210/23)) :
    innerKernel x = (71/10)*x+-97 := by
  have hf0 : ⌊(23/10)*x⌋=(20:ℤ) := floor_linear_interval x 9 (210/23) (23/10) 20
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(1:ℤ) := floor_linear_interval x 9 (210/23) (3/20) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(18:ℤ) := floor_linear_interval x 9 (210/23) 2 18
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x 9 (210/23) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(9:ℤ) := floor_linear_interval x 9 (210/23) 1 9
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(16:ℤ) := floor_linear_interval x 9 (210/23) (37/20) 16
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

theorem innerKernel_cell_053 (x : ℚ) (hl : (210/23)≤x) (hr : x<(340/37)) :
    innerKernel x = (119/20)*x+(-173/2) := by
  have hf0 : ⌊(23/10)*x⌋=(21:ℤ) := floor_linear_interval x (210/23) (340/37) (23/10) 21
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(1:ℤ) := floor_linear_interval x (210/23) (340/37) (3/20) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(18:ℤ) := floor_linear_interval x (210/23) (340/37) 2 18
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (210/23) (340/37) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(9:ℤ) := floor_linear_interval x (210/23) (340/37) 1 9
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(16:ℤ) := floor_linear_interval x (210/23) (340/37) (37/20) 16
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

end Zeta5InnerAsymptotics
