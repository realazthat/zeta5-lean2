import InnerPrimeCellBase

set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

noncomputable section
namespace Zeta5InnerAsymptotics

theorem innerKernel_cell_054 (x : ℚ) (hl : (340/37)≤x) (hr : x<(400/43)) :
    innerKernel x = (39/5)*x+(-207/2) := by
  have hf0 : ⌊(23/10)*x⌋=(21:ℤ) := floor_linear_interval x (340/37) (400/43) (23/10) 21
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(1:ℤ) := floor_linear_interval x (340/37) (400/43) (3/20) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(18:ℤ) := floor_linear_interval x (340/37) (400/43) 2 18
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (340/37) (400/43) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(9:ℤ) := floor_linear_interval x (340/37) (400/43) 1 9
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(17:ℤ) := floor_linear_interval x (340/37) (400/43) (37/20) 17
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

theorem innerKernel_cell_055 (x : ℚ) (hl : (400/43)≤x) (hr : x<(19/2)) :
    innerKernel x = (183/40)*x+(-147/2) := by
  have hf0 : ⌊(23/10)*x⌋=(21:ℤ) := floor_linear_interval x (400/43) (19/2) (23/10) 21
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(1:ℤ) := floor_linear_interval x (400/43) (19/2) (3/20) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(18:ℤ) := floor_linear_interval x (400/43) (19/2) 2 18
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (400/43) (19/2) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(9:ℤ) := floor_linear_interval x (400/43) (19/2) 1 9
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(17:ℤ) := floor_linear_interval x (400/43) (19/2) (37/20) 17
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

theorem innerKernel_cell_056 (x : ℚ) (hl : (19/2)≤x) (hr : x<(220/23)) :
    innerKernel x = (223/40)*x+-83 := by
  have hf0 : ⌊(23/10)*x⌋=(21:ℤ) := floor_linear_interval x (19/2) (220/23) (23/10) 21
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(1:ℤ) := floor_linear_interval x (19/2) (220/23) (3/20) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(19:ℤ) := floor_linear_interval x (19/2) (220/23) 2 19
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (19/2) (220/23) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(9:ℤ) := floor_linear_interval x (19/2) (220/23) 1 9
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(17:ℤ) := floor_linear_interval x (19/2) (220/23) (37/20) 17
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

theorem innerKernel_cell_057 (x : ℚ) (hl : (220/23)≤x) (hr : x<(360/37)) :
    innerKernel x = (177/40)*x+-72 := by
  have hf0 : ⌊(23/10)*x⌋=(22:ℤ) := floor_linear_interval x (220/23) (360/37) (23/10) 22
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(1:ℤ) := floor_linear_interval x (220/23) (360/37) (3/20) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(19:ℤ) := floor_linear_interval x (220/23) (360/37) 2 19
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (220/23) (360/37) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(9:ℤ) := floor_linear_interval x (220/23) (360/37) 1 9
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(17:ℤ) := floor_linear_interval x (220/23) (360/37) (37/20) 17
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

theorem innerKernel_cell_058 (x : ℚ) (hl : (360/37)≤x) (hr : x<(420/43)) :
    innerKernel x = (181/20)*x+-117 := by
  have hf0 : ⌊(23/10)*x⌋=(22:ℤ) := floor_linear_interval x (360/37) (420/43) (23/10) 22
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(1:ℤ) := floor_linear_interval x (360/37) (420/43) (3/20) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(19:ℤ) := floor_linear_interval x (360/37) (420/43) 2 19
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (360/37) (420/43) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(9:ℤ) := floor_linear_interval x (360/37) (420/43) 1 9
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(18:ℤ) := floor_linear_interval x (360/37) (420/43) (37/20) 18
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

theorem innerKernel_cell_059 (x : ℚ) (hl : (420/43)≤x) (hr : x<10) :
    innerKernel x = (181/20)*x+-117 := by
  have hf0 : ⌊(23/10)*x⌋=(22:ℤ) := floor_linear_interval x (420/43) 10 (23/10) 22
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(1:ℤ) := floor_linear_interval x (420/43) 10 (3/20) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(19:ℤ) := floor_linear_interval x (420/43) 10 2 19
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (420/43) 10 (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(9:ℤ) := floor_linear_interval x (420/43) 10 1 9
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(18:ℤ) := floor_linear_interval x (420/43) 10 (37/20) 18
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

theorem innerKernel_cell_060 (x : ℚ) (hl : 10≤x) (hr : x<(440/43)) :
    innerKernel x = (69/10)*x+-114 := by
  have hf0 : ⌊(23/10)*x⌋=(23:ℤ) := floor_linear_interval x 10 (440/43) (23/10) 23
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(1:ℤ) := floor_linear_interval x 10 (440/43) (3/20) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(20:ℤ) := floor_linear_interval x 10 (440/43) 2 20
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x 10 (440/43) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(10:ℤ) := floor_linear_interval x 10 (440/43) 1 10
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(18:ℤ) := floor_linear_interval x 10 (440/43) (37/20) 18
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

theorem innerKernel_cell_061 (x : ℚ) (hl : (440/43)≤x) (hr : x<(380/37)) :
    innerKernel x = (147/40)*x+-81 := by
  have hf0 : ⌊(23/10)*x⌋=(23:ℤ) := floor_linear_interval x (440/43) (380/37) (23/10) 23
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(1:ℤ) := floor_linear_interval x (440/43) (380/37) (3/20) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(20:ℤ) := floor_linear_interval x (440/43) (380/37) 2 20
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (440/43) (380/37) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(10:ℤ) := floor_linear_interval x (440/43) (380/37) 1 10
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(18:ℤ) := floor_linear_interval x (440/43) (380/37) (37/20) 18
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

theorem innerKernel_cell_062 (x : ℚ) (hl : (380/37)≤x) (hr : x<(240/23)) :
    innerKernel x = (221/40)*x+-100 := by
  have hf0 : ⌊(23/10)*x⌋=(23:ℤ) := floor_linear_interval x (380/37) (240/23) (23/10) 23
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(1:ℤ) := floor_linear_interval x (380/37) (240/23) (3/20) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(20:ℤ) := floor_linear_interval x (380/37) (240/23) 2 20
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (380/37) (240/23) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(10:ℤ) := floor_linear_interval x (380/37) (240/23) 1 10
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(19:ℤ) := floor_linear_interval x (380/37) (240/23) (37/20) 19
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
