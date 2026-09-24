import InnerPrimeCellBase

set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

noncomputable section
namespace Zeta5InnerAsymptotics

theorem innerKernel_cell_126 (x : ℚ) (hl : (410/23)≤x) (hr : x<(660/37)) :
    innerKernel x = (167/10)*x+-270 := by
  have hf0 : ⌊(23/10)*x⌋=(41:ℤ) := floor_linear_interval x (410/23) (660/37) (23/10) 41
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(2:ℤ) := floor_linear_interval x (410/23) (660/37) (3/20) 2
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(35:ℤ) := floor_linear_interval x (410/23) (660/37) 2 35
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(1:ℤ) := floor_linear_interval x (410/23) (660/37) (3/40) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(17:ℤ) := floor_linear_interval x (410/23) (660/37) 1 17
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(32:ℤ) := floor_linear_interval x (410/23) (660/37) (37/20) 32
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

theorem innerKernel_cell_127 (x : ℚ) (hl : (660/37)≤x) (hr : x<18) :
    innerKernel x = (371/20)*x+-303 := by
  have hf0 : ⌊(23/10)*x⌋=(41:ℤ) := floor_linear_interval x (660/37) 18 (23/10) 41
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(2:ℤ) := floor_linear_interval x (660/37) 18 (3/20) 2
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(35:ℤ) := floor_linear_interval x (660/37) 18 2 35
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(1:ℤ) := floor_linear_interval x (660/37) 18 (3/40) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(17:ℤ) := floor_linear_interval x (660/37) 18 1 17
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(33:ℤ) := floor_linear_interval x (660/37) 18 (37/20) 33
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

theorem innerKernel_cell_128 (x : ℚ) (hl : 18≤x) (hr : x<(780/43)) :
    innerKernel x = (177/10)*x+-321 := by
  have hf0 : ⌊(23/10)*x⌋=(41:ℤ) := floor_linear_interval x 18 (780/43) (23/10) 41
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(2:ℤ) := floor_linear_interval x 18 (780/43) (3/20) 2
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(36:ℤ) := floor_linear_interval x 18 (780/43) 2 36
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(1:ℤ) := floor_linear_interval x 18 (780/43) (3/40) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(18:ℤ) := floor_linear_interval x 18 (780/43) 1 18
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(33:ℤ) := floor_linear_interval x 18 (780/43) (37/20) 33
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

theorem innerKernel_cell_129 (x : ℚ) (hl : (780/43)≤x) (hr : x<(420/23)) :
    innerKernel x = (177/10)*x+-321 := by
  have hf0 : ⌊(23/10)*x⌋=(41:ℤ) := floor_linear_interval x (780/43) (420/23) (23/10) 41
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(2:ℤ) := floor_linear_interval x (780/43) (420/23) (3/20) 2
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(36:ℤ) := floor_linear_interval x (780/43) (420/23) 2 36
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(1:ℤ) := floor_linear_interval x (780/43) (420/23) (3/40) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(18:ℤ) := floor_linear_interval x (780/43) (420/23) 1 18
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(33:ℤ) := floor_linear_interval x (780/43) (420/23) (37/20) 33
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

theorem innerKernel_cell_130 (x : ℚ) (hl : (420/23)≤x) (hr : x<(680/37)) :
    innerKernel x = (331/20)*x+-300 := by
  have hf0 : ⌊(23/10)*x⌋=(42:ℤ) := floor_linear_interval x (420/23) (680/37) (23/10) 42
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(2:ℤ) := floor_linear_interval x (420/23) (680/37) (3/20) 2
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(36:ℤ) := floor_linear_interval x (420/23) (680/37) 2 36
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(1:ℤ) := floor_linear_interval x (420/23) (680/37) (3/40) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(18:ℤ) := floor_linear_interval x (420/23) (680/37) 1 18
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(33:ℤ) := floor_linear_interval x (420/23) (680/37) (37/20) 33
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

theorem innerKernel_cell_131 (x : ℚ) (hl : (680/37)≤x) (hr : x<(37/2)) :
    innerKernel x = (847/40)*x+-385 := by
  have hf0 : ⌊(23/10)*x⌋=(42:ℤ) := floor_linear_interval x (680/37) (37/2) (23/10) 42
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(2:ℤ) := floor_linear_interval x (680/37) (37/2) (3/20) 2
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(36:ℤ) := floor_linear_interval x (680/37) (37/2) 2 36
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(1:ℤ) := floor_linear_interval x (680/37) (37/2) (3/40) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(18:ℤ) := floor_linear_interval x (680/37) (37/2) 1 18
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(34:ℤ) := floor_linear_interval x (680/37) (37/2) (37/20) 34
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

theorem innerKernel_cell_132 (x : ℚ) (hl : (37/2)≤x) (hr : x<(800/43)) :
    innerKernel x = (887/40)*x+(-807/2) := by
  have hf0 : ⌊(23/10)*x⌋=(42:ℤ) := floor_linear_interval x (37/2) (800/43) (23/10) 42
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(2:ℤ) := floor_linear_interval x (37/2) (800/43) (3/20) 2
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(37:ℤ) := floor_linear_interval x (37/2) (800/43) 2 37
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(1:ℤ) := floor_linear_interval x (37/2) (800/43) (3/40) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(18:ℤ) := floor_linear_interval x (37/2) (800/43) 1 18
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(34:ℤ) := floor_linear_interval x (37/2) (800/43) (37/20) 34
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

theorem innerKernel_cell_133 (x : ℚ) (hl : (800/43)≤x) (hr : x<(430/23)) :
    innerKernel x = (379/20)*x+(-687/2) := by
  have hf0 : ⌊(23/10)*x⌋=(42:ℤ) := floor_linear_interval x (800/43) (430/23) (23/10) 42
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(2:ℤ) := floor_linear_interval x (800/43) (430/23) (3/20) 2
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(37:ℤ) := floor_linear_interval x (800/43) (430/23) 2 37
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(1:ℤ) := floor_linear_interval x (800/43) (430/23) (3/40) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(18:ℤ) := floor_linear_interval x (800/43) (430/23) 1 18
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(34:ℤ) := floor_linear_interval x (800/43) (430/23) (37/20) 34
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

theorem innerKernel_cell_134 (x : ℚ) (hl : (430/23)≤x) (hr : x<(700/37)) :
    innerKernel x = (89/5)*x+-322 := by
  have hf0 : ⌊(23/10)*x⌋=(43:ℤ) := floor_linear_interval x (430/23) (700/37) (23/10) 43
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(2:ℤ) := floor_linear_interval x (430/23) (700/37) (3/20) 2
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(37:ℤ) := floor_linear_interval x (430/23) (700/37) 2 37
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(1:ℤ) := floor_linear_interval x (430/23) (700/37) (3/40) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(18:ℤ) := floor_linear_interval x (430/23) (700/37) 1 18
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(34:ℤ) := floor_linear_interval x (430/23) (700/37) (37/20) 34
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
