import InnerPrimeCellBase

set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

noncomputable section
namespace Zeta5InnerAsymptotics

theorem innerKernel_cell_117 (x : ℚ) (hl : (720/43)≤x) (hr : x<(620/37)) :
    innerKernel x = (67/4)*x+(-483/2) := by
  have hf0 : ⌊(23/10)*x⌋=(38:ℤ) := floor_linear_interval x (720/43) (620/37) (23/10) 38
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(2:ℤ) := floor_linear_interval x (720/43) (620/37) (3/20) 2
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(33:ℤ) := floor_linear_interval x (720/43) (620/37) 2 33
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(1:ℤ) := floor_linear_interval x (720/43) (620/37) (3/40) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(16:ℤ) := floor_linear_interval x (720/43) (620/37) 1 16
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(30:ℤ) := floor_linear_interval x (720/43) (620/37) (37/20) 30
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

theorem innerKernel_cell_118 (x : ℚ) (hl : (620/37)≤x) (hr : x<(390/23)) :
    innerKernel x = (93/5)*x+(-545/2) := by
  have hf0 : ⌊(23/10)*x⌋=(38:ℤ) := floor_linear_interval x (620/37) (390/23) (23/10) 38
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(2:ℤ) := floor_linear_interval x (620/37) (390/23) (3/20) 2
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(33:ℤ) := floor_linear_interval x (620/37) (390/23) 2 33
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(1:ℤ) := floor_linear_interval x (620/37) (390/23) (3/40) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(16:ℤ) := floor_linear_interval x (620/37) (390/23) 1 16
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(31:ℤ) := floor_linear_interval x (620/37) (390/23) (37/20) 31
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

theorem innerKernel_cell_119 (x : ℚ) (hl : (390/23)≤x) (hr : x<17) :
    innerKernel x = (349/20)*x+-253 := by
  have hf0 : ⌊(23/10)*x⌋=(39:ℤ) := floor_linear_interval x (390/23) 17 (23/10) 39
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(2:ℤ) := floor_linear_interval x (390/23) 17 (3/20) 2
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(33:ℤ) := floor_linear_interval x (390/23) 17 2 33
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(1:ℤ) := floor_linear_interval x (390/23) 17 (3/40) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(16:ℤ) := floor_linear_interval x (390/23) 17 1 16
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(31:ℤ) := floor_linear_interval x (390/23) 17 (37/20) 31
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

theorem innerKernel_cell_120 (x : ℚ) (hl : 17≤x) (hr : x<(740/43)) :
    innerKernel x = (83/5)*x+-270 := by
  have hf0 : ⌊(23/10)*x⌋=(39:ℤ) := floor_linear_interval x 17 (740/43) (23/10) 39
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(2:ℤ) := floor_linear_interval x 17 (740/43) (3/20) 2
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(34:ℤ) := floor_linear_interval x 17 (740/43) 2 34
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(1:ℤ) := floor_linear_interval x 17 (740/43) (3/40) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(17:ℤ) := floor_linear_interval x 17 (740/43) 1 17
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(31:ℤ) := floor_linear_interval x 17 (740/43) (37/20) 31
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

theorem innerKernel_cell_121 (x : ℚ) (hl : (740/43)≤x) (hr : x<(640/37)) :
    innerKernel x = (83/5)*x+-270 := by
  have hf0 : ⌊(23/10)*x⌋=(39:ℤ) := floor_linear_interval x (740/43) (640/37) (23/10) 39
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(2:ℤ) := floor_linear_interval x (740/43) (640/37) (3/20) 2
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(34:ℤ) := floor_linear_interval x (740/43) (640/37) 2 34
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(1:ℤ) := floor_linear_interval x (740/43) (640/37) (3/40) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(17:ℤ) := floor_linear_interval x (740/43) (640/37) 1 17
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(31:ℤ) := floor_linear_interval x (740/43) (640/37) (37/20) 31
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

theorem innerKernel_cell_122 (x : ℚ) (hl : (640/37)≤x) (hr : x<(400/23)) :
    innerKernel x = (849/40)*x+-350 := by
  have hf0 : ⌊(23/10)*x⌋=(39:ℤ) := floor_linear_interval x (640/37) (400/23) (23/10) 39
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(2:ℤ) := floor_linear_interval x (640/37) (400/23) (3/20) 2
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(34:ℤ) := floor_linear_interval x (640/37) (400/23) 2 34
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(1:ℤ) := floor_linear_interval x (640/37) (400/23) (3/40) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(17:ℤ) := floor_linear_interval x (640/37) (400/23) 1 17
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(32:ℤ) := floor_linear_interval x (640/37) (400/23) (37/20) 32
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

theorem innerKernel_cell_123 (x : ℚ) (hl : (400/23)≤x) (hr : x<(35/2)) :
    innerKernel x = (803/40)*x+-330 := by
  have hf0 : ⌊(23/10)*x⌋=(40:ℤ) := floor_linear_interval x (400/23) (35/2) (23/10) 40
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(2:ℤ) := floor_linear_interval x (400/23) (35/2) (3/20) 2
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(34:ℤ) := floor_linear_interval x (400/23) (35/2) 2 34
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(1:ℤ) := floor_linear_interval x (400/23) (35/2) (3/40) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(17:ℤ) := floor_linear_interval x (400/23) (35/2) 1 17
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(32:ℤ) := floor_linear_interval x (400/23) (35/2) (37/20) 32
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

theorem innerKernel_cell_124 (x : ℚ) (hl : (35/2)≤x) (hr : x<(760/43)) :
    innerKernel x = (843/40)*x+(-695/2) := by
  have hf0 : ⌊(23/10)*x⌋=(40:ℤ) := floor_linear_interval x (35/2) (760/43) (23/10) 40
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(2:ℤ) := floor_linear_interval x (35/2) (760/43) (3/20) 2
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(35:ℤ) := floor_linear_interval x (35/2) (760/43) 2 35
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(1:ℤ) := floor_linear_interval x (35/2) (760/43) (3/40) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(17:ℤ) := floor_linear_interval x (35/2) (760/43) 1 17
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(32:ℤ) := floor_linear_interval x (35/2) (760/43) (37/20) 32
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

theorem innerKernel_cell_125 (x : ℚ) (hl : (760/43)≤x) (hr : x<(410/23)) :
    innerKernel x = (357/20)*x+(-581/2) := by
  have hf0 : ⌊(23/10)*x⌋=(40:ℤ) := floor_linear_interval x (760/43) (410/23) (23/10) 40
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(2:ℤ) := floor_linear_interval x (760/43) (410/23) (3/20) 2
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(35:ℤ) := floor_linear_interval x (760/43) (410/23) 2 35
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(1:ℤ) := floor_linear_interval x (760/43) (410/23) (3/40) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(17:ℤ) := floor_linear_interval x (760/43) (410/23) 1 17
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(32:ℤ) := floor_linear_interval x (760/43) (410/23) (37/20) 32
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
