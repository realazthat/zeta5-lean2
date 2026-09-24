import InnerPrimeCellBase

set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

noncomputable section
namespace Zeta5InnerAsymptotics

theorem innerKernel_cell_081 (x : ℚ) (hl : (540/43)≤x) (hr : x<(290/23)) :
    innerKernel x = (303/40)*x+(-333/2) := by
  have hf0 : ⌊(23/10)*x⌋=(28:ℤ) := floor_linear_interval x (540/43) (290/23) (23/10) 28
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(1:ℤ) := floor_linear_interval x (540/43) (290/23) (3/20) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(25:ℤ) := floor_linear_interval x (540/43) (290/23) 2 25
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (540/43) (290/23) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(12:ℤ) := floor_linear_interval x (540/43) (290/23) 1 12
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(23:ℤ) := floor_linear_interval x (540/43) (290/23) (37/20) 23
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

theorem innerKernel_cell_082 (x : ℚ) (hl : (290/23)≤x) (hr : x<(480/37)) :
    innerKernel x = (257/40)*x+-152 := by
  have hf0 : ⌊(23/10)*x⌋=(29:ℤ) := floor_linear_interval x (290/23) (480/37) (23/10) 29
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(1:ℤ) := floor_linear_interval x (290/23) (480/37) (3/20) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(25:ℤ) := floor_linear_interval x (290/23) (480/37) 2 25
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (290/23) (480/37) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(12:ℤ) := floor_linear_interval x (290/23) (480/37) 1 12
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(23:ℤ) := floor_linear_interval x (290/23) (480/37) (37/20) 23
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

theorem innerKernel_cell_083 (x : ℚ) (hl : (480/37)≤x) (hr : x<13) :
    innerKernel x = (221/20)*x+-212 := by
  have hf0 : ⌊(23/10)*x⌋=(29:ℤ) := floor_linear_interval x (480/37) 13 (23/10) 29
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(1:ℤ) := floor_linear_interval x (480/37) 13 (3/20) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(25:ℤ) := floor_linear_interval x (480/37) 13 2 25
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (480/37) 13 (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(12:ℤ) := floor_linear_interval x (480/37) 13 1 12
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(24:ℤ) := floor_linear_interval x (480/37) 13 (37/20) 24
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

theorem innerKernel_cell_084 (x : ℚ) (hl : 13≤x) (hr : x<(560/43)) :
    innerKernel x = (51/5)*x+-225 := by
  have hf0 : ⌊(23/10)*x⌋=(29:ℤ) := floor_linear_interval x 13 (560/43) (23/10) 29
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(1:ℤ) := floor_linear_interval x 13 (560/43) (3/20) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(26:ℤ) := floor_linear_interval x 13 (560/43) 2 26
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x 13 (560/43) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(13:ℤ) := floor_linear_interval x 13 (560/43) 1 13
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(24:ℤ) := floor_linear_interval x 13 (560/43) (37/20) 24
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

theorem innerKernel_cell_085 (x : ℚ) (hl : (560/43)≤x) (hr : x<(300/23)) :
    innerKernel x = (279/40)*x+-183 := by
  have hf0 : ⌊(23/10)*x⌋=(29:ℤ) := floor_linear_interval x (560/43) (300/23) (23/10) 29
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(1:ℤ) := floor_linear_interval x (560/43) (300/23) (3/20) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(26:ℤ) := floor_linear_interval x (560/43) (300/23) 2 26
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (560/43) (300/23) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(13:ℤ) := floor_linear_interval x (560/43) (300/23) 1 13
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(24:ℤ) := floor_linear_interval x (560/43) (300/23) (37/20) 24
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

theorem innerKernel_cell_086 (x : ℚ) (hl : (300/23)≤x) (hr : x<(40/3)) :
    innerKernel x = (233/40)*x+-168 := by
  have hf0 : ⌊(23/10)*x⌋=(30:ℤ) := floor_linear_interval x (300/23) (40/3) (23/10) 30
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(1:ℤ) := floor_linear_interval x (300/23) (40/3) (3/20) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(26:ℤ) := floor_linear_interval x (300/23) (40/3) 2 26
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (300/23) (40/3) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(13:ℤ) := floor_linear_interval x (300/23) (40/3) 1 13
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(24:ℤ) := floor_linear_interval x (300/23) (40/3) (37/20) 24
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

theorem innerKernel_cell_087 (x : ℚ) (hl : (40/3)≤x) (hr : x<(310/23)) :
    innerKernel x = (145/8)*x+-184 := by
  have hf0 : ⌊(23/10)*x⌋=(30:ℤ) := floor_linear_interval x (40/3) (310/23) (23/10) 30
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(2:ℤ) := floor_linear_interval x (40/3) (310/23) (3/20) 2
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(26:ℤ) := floor_linear_interval x (40/3) (310/23) 2 26
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(1:ℤ) := floor_linear_interval x (40/3) (310/23) (3/40) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(13:ℤ) := floor_linear_interval x (40/3) (310/23) 1 13
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(24:ℤ) := floor_linear_interval x (40/3) (310/23) (37/20) 24
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

theorem innerKernel_cell_088 (x : ℚ) (hl : (310/23)≤x) (hr : x<(580/43)) :
    innerKernel x = (679/40)*x+(-337/2) := by
  have hf0 : ⌊(23/10)*x⌋=(31:ℤ) := floor_linear_interval x (310/23) (580/43) (23/10) 31
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(2:ℤ) := floor_linear_interval x (310/23) (580/43) (3/20) 2
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(26:ℤ) := floor_linear_interval x (310/23) (580/43) 2 26
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(1:ℤ) := floor_linear_interval x (310/23) (580/43) (3/40) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(13:ℤ) := floor_linear_interval x (310/23) (580/43) 1 13
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(24:ℤ) := floor_linear_interval x (310/23) (580/43) (37/20) 24
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

theorem innerKernel_cell_089 (x : ℚ) (hl : (580/43)≤x) (hr : x<(27/2)) :
    innerKernel x = (679/40)*x+(-337/2) := by
  have hf0 : ⌊(23/10)*x⌋=(31:ℤ) := floor_linear_interval x (580/43) (27/2) (23/10) 31
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(2:ℤ) := floor_linear_interval x (580/43) (27/2) (3/20) 2
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(26:ℤ) := floor_linear_interval x (580/43) (27/2) 2 26
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(1:ℤ) := floor_linear_interval x (580/43) (27/2) (3/40) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(13:ℤ) := floor_linear_interval x (580/43) (27/2) 1 13
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(24:ℤ) := floor_linear_interval x (580/43) (27/2) (37/20) 24
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
