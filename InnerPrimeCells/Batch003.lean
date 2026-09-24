import InnerPrimeCellBase

set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

noncomputable section
namespace Zeta5InnerAsymptotics

theorem innerKernel_cell_027 (x : ℚ) (hl : (260/43)≤x) (hr : x<(140/23)) :
    innerKernel x = (28/5)*x+-41 := by
  have hf0 : ⌊(23/10)*x⌋=(13:ℤ) := floor_linear_interval x (260/43) (140/23) (23/10) 13
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(0:ℤ) := floor_linear_interval x (260/43) (140/23) (3/20) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(12:ℤ) := floor_linear_interval x (260/43) (140/23) 2 12
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (260/43) (140/23) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(6:ℤ) := floor_linear_interval x (260/43) (140/23) 1 6
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(11:ℤ) := floor_linear_interval x (260/43) (140/23) (37/20) 11
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

theorem innerKernel_cell_028 (x : ℚ) (hl : (140/23)≤x) (hr : x<(240/37)) :
    innerKernel x = (89/20)*x+-34 := by
  have hf0 : ⌊(23/10)*x⌋=(14:ℤ) := floor_linear_interval x (140/23) (240/37) (23/10) 14
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(0:ℤ) := floor_linear_interval x (140/23) (240/37) (3/20) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(12:ℤ) := floor_linear_interval x (140/23) (240/37) 2 12
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (140/23) (240/37) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(6:ℤ) := floor_linear_interval x (140/23) (240/37) 1 6
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(11:ℤ) := floor_linear_interval x (140/23) (240/37) (37/20) 11
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

theorem innerKernel_cell_029 (x : ℚ) (hl : (240/37)≤x) (hr : x<(13/2)) :
    innerKernel x = (363/40)*x+-64 := by
  have hf0 : ⌊(23/10)*x⌋=(14:ℤ) := floor_linear_interval x (240/37) (13/2) (23/10) 14
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(0:ℤ) := floor_linear_interval x (240/37) (13/2) (3/20) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(12:ℤ) := floor_linear_interval x (240/37) (13/2) 2 12
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (240/37) (13/2) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(6:ℤ) := floor_linear_interval x (240/37) (13/2) 1 6
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(12:ℤ) := floor_linear_interval x (240/37) (13/2) (37/20) 12
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

theorem innerKernel_cell_030 (x : ℚ) (hl : (13/2)≤x) (hr : x<(280/43)) :
    innerKernel x = (403/40)*x+(-141/2) := by
  have hf0 : ⌊(23/10)*x⌋=(14:ℤ) := floor_linear_interval x (13/2) (280/43) (23/10) 14
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(0:ℤ) := floor_linear_interval x (13/2) (280/43) (3/20) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(13:ℤ) := floor_linear_interval x (13/2) (280/43) 2 13
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (13/2) (280/43) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(6:ℤ) := floor_linear_interval x (13/2) (280/43) 1 6
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(12:ℤ) := floor_linear_interval x (13/2) (280/43) (37/20) 12
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

theorem innerKernel_cell_031 (x : ℚ) (hl : (280/43)≤x) (hr : x<(150/23)) :
    innerKernel x = (137/20)*x+(-99/2) := by
  have hf0 : ⌊(23/10)*x⌋=(14:ℤ) := floor_linear_interval x (280/43) (150/23) (23/10) 14
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(0:ℤ) := floor_linear_interval x (280/43) (150/23) (3/20) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(13:ℤ) := floor_linear_interval x (280/43) (150/23) 2 13
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (280/43) (150/23) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(6:ℤ) := floor_linear_interval x (280/43) (150/23) 1 6
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(12:ℤ) := floor_linear_interval x (280/43) (150/23) (37/20) 12
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

theorem innerKernel_cell_032 (x : ℚ) (hl : (150/23)≤x) (hr : x<(20/3)) :
    innerKernel x = (57/10)*x+-42 := by
  have hf0 : ⌊(23/10)*x⌋=(15:ℤ) := floor_linear_interval x (150/23) (20/3) (23/10) 15
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(0:ℤ) := floor_linear_interval x (150/23) (20/3) (3/20) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(13:ℤ) := floor_linear_interval x (150/23) (20/3) 2 13
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (150/23) (20/3) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(6:ℤ) := floor_linear_interval x (150/23) (20/3) 1 6
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(12:ℤ) := floor_linear_interval x (150/23) (20/3) (37/20) 12
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

theorem innerKernel_cell_033 (x : ℚ) (hl : (20/3)≤x) (hr : x<(160/23)) :
    innerKernel x = (69/10)*x+-50 := by
  have hf0 : ⌊(23/10)*x⌋=(15:ℤ) := floor_linear_interval x (20/3) (160/23) (23/10) 15
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(1:ℤ) := floor_linear_interval x (20/3) (160/23) (3/20) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(13:ℤ) := floor_linear_interval x (20/3) (160/23) 2 13
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (20/3) (160/23) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(6:ℤ) := floor_linear_interval x (20/3) (160/23) 1 6
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(12:ℤ) := floor_linear_interval x (20/3) (160/23) (37/20) 12
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

theorem innerKernel_cell_034 (x : ℚ) (hl : (160/23)≤x) (hr : x<(300/43)) :
    innerKernel x = (23/4)*x+-42 := by
  have hf0 : ⌊(23/10)*x⌋=(16:ℤ) := floor_linear_interval x (160/23) (300/43) (23/10) 16
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(1:ℤ) := floor_linear_interval x (160/23) (300/43) (3/20) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(13:ℤ) := floor_linear_interval x (160/23) (300/43) 2 13
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (160/23) (300/43) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(6:ℤ) := floor_linear_interval x (160/23) (300/43) 1 6
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(12:ℤ) := floor_linear_interval x (160/23) (300/43) (37/20) 12
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

theorem innerKernel_cell_035 (x : ℚ) (hl : (300/43)≤x) (hr : x<7) :
    innerKernel x = (23/4)*x+-42 := by
  have hf0 : ⌊(23/10)*x⌋=(16:ℤ) := floor_linear_interval x (300/43) 7 (23/10) 16
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(1:ℤ) := floor_linear_interval x (300/43) 7 (3/20) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(13:ℤ) := floor_linear_interval x (300/43) 7 2 13
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (300/43) 7 (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(6:ℤ) := floor_linear_interval x (300/43) 7 1 6
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(12:ℤ) := floor_linear_interval x (300/43) 7 (37/20) 12
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
