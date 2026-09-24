import InnerPrimeCellBase

set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

noncomputable section
namespace Zeta5InnerAsymptotics

theorem innerKernel_cell_099 (x : ℚ) (hl : (540/37)≤x) (hr : x<(340/23)) :
    innerKernel x = (837/40)*x+-250 := by
  have hf0 : ⌊(23/10)*x⌋=(33:ℤ) := floor_linear_interval x (540/37) (340/23) (23/10) 33
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(2:ℤ) := floor_linear_interval x (540/37) (340/23) (3/20) 2
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(29:ℤ) := floor_linear_interval x (540/37) (340/23) 2 29
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(1:ℤ) := floor_linear_interval x (540/37) (340/23) (3/40) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(14:ℤ) := floor_linear_interval x (540/37) (340/23) 1 14
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(27:ℤ) := floor_linear_interval x (540/37) (340/23) (37/20) 27
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

theorem innerKernel_cell_100 (x : ℚ) (hl : (340/23)≤x) (hr : x<(640/43)) :
    innerKernel x = (791/40)*x+-233 := by
  have hf0 : ⌊(23/10)*x⌋=(34:ℤ) := floor_linear_interval x (340/23) (640/43) (23/10) 34
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(2:ℤ) := floor_linear_interval x (340/23) (640/43) (3/20) 2
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(29:ℤ) := floor_linear_interval x (340/23) (640/43) 2 29
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(1:ℤ) := floor_linear_interval x (340/23) (640/43) (3/40) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(14:ℤ) := floor_linear_interval x (340/23) (640/43) 1 14
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(27:ℤ) := floor_linear_interval x (340/23) (640/43) (37/20) 27
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

theorem innerKernel_cell_101 (x : ℚ) (hl : (640/43)≤x) (hr : x<15) :
    innerKernel x = (331/20)*x+-185 := by
  have hf0 : ⌊(23/10)*x⌋=(34:ℤ) := floor_linear_interval x (640/43) 15 (23/10) 34
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(2:ℤ) := floor_linear_interval x (640/43) 15 (3/20) 2
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(29:ℤ) := floor_linear_interval x (640/43) 15 2 29
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(1:ℤ) := floor_linear_interval x (640/43) 15 (3/40) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(14:ℤ) := floor_linear_interval x (640/43) 15 1 14
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(27:ℤ) := floor_linear_interval x (640/43) 15 (37/20) 27
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

theorem innerKernel_cell_102 (x : ℚ) (hl : 15≤x) (hr : x<(560/37)) :
    innerKernel x = (157/10)*x+-200 := by
  have hf0 : ⌊(23/10)*x⌋=(34:ℤ) := floor_linear_interval x 15 (560/37) (23/10) 34
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(2:ℤ) := floor_linear_interval x 15 (560/37) (3/20) 2
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(30:ℤ) := floor_linear_interval x 15 (560/37) 2 30
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(1:ℤ) := floor_linear_interval x 15 (560/37) (3/40) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(15:ℤ) := floor_linear_interval x 15 (560/37) 1 15
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(27:ℤ) := floor_linear_interval x 15 (560/37) (37/20) 27
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

theorem innerKernel_cell_103 (x : ℚ) (hl : (560/37)≤x) (hr : x<(350/23)) :
    innerKernel x = (813/40)*x+-270 := by
  have hf0 : ⌊(23/10)*x⌋=(34:ℤ) := floor_linear_interval x (560/37) (350/23) (23/10) 34
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(2:ℤ) := floor_linear_interval x (560/37) (350/23) (3/20) 2
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(30:ℤ) := floor_linear_interval x (560/37) (350/23) 2 30
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(1:ℤ) := floor_linear_interval x (560/37) (350/23) (3/40) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(15:ℤ) := floor_linear_interval x (560/37) (350/23) 1 15
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(28:ℤ) := floor_linear_interval x (560/37) (350/23) (37/20) 28
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

theorem innerKernel_cell_104 (x : ℚ) (hl : (350/23)≤x) (hr : x<(660/43)) :
    innerKernel x = (767/40)*x+(-505/2) := by
  have hf0 : ⌊(23/10)*x⌋=(35:ℤ) := floor_linear_interval x (350/23) (660/43) (23/10) 35
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(2:ℤ) := floor_linear_interval x (350/23) (660/43) (3/20) 2
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(30:ℤ) := floor_linear_interval x (350/23) (660/43) 2 30
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(1:ℤ) := floor_linear_interval x (350/23) (660/43) (3/40) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(15:ℤ) := floor_linear_interval x (350/23) (660/43) 1 15
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(28:ℤ) := floor_linear_interval x (350/23) (660/43) (37/20) 28
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

theorem innerKernel_cell_105 (x : ℚ) (hl : (660/43)≤x) (hr : x<(31/2)) :
    innerKernel x = (767/40)*x+(-505/2) := by
  have hf0 : ⌊(23/10)*x⌋=(35:ℤ) := floor_linear_interval x (660/43) (31/2) (23/10) 35
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(2:ℤ) := floor_linear_interval x (660/43) (31/2) (3/20) 2
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(30:ℤ) := floor_linear_interval x (660/43) (31/2) 2 30
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(1:ℤ) := floor_linear_interval x (660/43) (31/2) (3/40) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(15:ℤ) := floor_linear_interval x (660/43) (31/2) 1 15
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(28:ℤ) := floor_linear_interval x (660/43) (31/2) (37/20) 28
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

theorem innerKernel_cell_106 (x : ℚ) (hl : (31/2)≤x) (hr : x<(360/23)) :
    innerKernel x = (807/40)*x+-268 := by
  have hf0 : ⌊(23/10)*x⌋=(35:ℤ) := floor_linear_interval x (31/2) (360/23) (23/10) 35
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(2:ℤ) := floor_linear_interval x (31/2) (360/23) (3/20) 2
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(31:ℤ) := floor_linear_interval x (31/2) (360/23) 2 31
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(1:ℤ) := floor_linear_interval x (31/2) (360/23) (3/40) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(15:ℤ) := floor_linear_interval x (31/2) (360/23) 1 15
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(28:ℤ) := floor_linear_interval x (31/2) (360/23) (37/20) 28
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

theorem innerKernel_cell_107 (x : ℚ) (hl : (360/23)≤x) (hr : x<(580/37)) :
    innerKernel x = (761/40)*x+-250 := by
  have hf0 : ⌊(23/10)*x⌋=(36:ℤ) := floor_linear_interval x (360/23) (580/37) (23/10) 36
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(2:ℤ) := floor_linear_interval x (360/23) (580/37) (3/20) 2
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(31:ℤ) := floor_linear_interval x (360/23) (580/37) 2 31
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(1:ℤ) := floor_linear_interval x (360/23) (580/37) (3/40) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(15:ℤ) := floor_linear_interval x (360/23) (580/37) 1 15
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(28:ℤ) := floor_linear_interval x (360/23) (580/37) (37/20) 28
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
