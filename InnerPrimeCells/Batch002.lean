import InnerPrimeCellBase

set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

noncomputable section
namespace Zeta5InnerAsymptotics

theorem innerKernel_cell_018 (x : ℚ) (hl : 5≤x) (hr : x<(220/43)) :
    innerKernel x = (9/2)*x+-24 := by
  have hf0 : ⌊(23/10)*x⌋=(11:ℤ) := floor_linear_interval x 5 (220/43) (23/10) 11
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(0:ℤ) := floor_linear_interval x 5 (220/43) (3/20) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(10:ℤ) := floor_linear_interval x 5 (220/43) 2 10
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x 5 (220/43) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(5:ℤ) := floor_linear_interval x 5 (220/43) 1 5
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(9:ℤ) := floor_linear_interval x 5 (220/43) (37/20) 9
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

theorem innerKernel_cell_019 (x : ℚ) (hl : (220/43)≤x) (hr : x<(120/23)) :
    innerKernel x = (9/2)*x+-24 := by
  have hf0 : ⌊(23/10)*x⌋=(11:ℤ) := floor_linear_interval x (220/43) (120/23) (23/10) 11
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(0:ℤ) := floor_linear_interval x (220/43) (120/23) (3/20) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(10:ℤ) := floor_linear_interval x (220/43) (120/23) 2 10
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (220/43) (120/23) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(5:ℤ) := floor_linear_interval x (220/43) (120/23) 1 5
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(9:ℤ) := floor_linear_interval x (220/43) (120/23) (37/20) 9
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

theorem innerKernel_cell_020 (x : ℚ) (hl : (120/23)≤x) (hr : x<(200/37)) :
    innerKernel x = (67/20)*x+-18 := by
  have hf0 : ⌊(23/10)*x⌋=(12:ℤ) := floor_linear_interval x (120/23) (200/37) (23/10) 12
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(0:ℤ) := floor_linear_interval x (120/23) (200/37) (3/20) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(10:ℤ) := floor_linear_interval x (120/23) (200/37) 2 10
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (120/23) (200/37) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(5:ℤ) := floor_linear_interval x (120/23) (200/37) 1 5
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(9:ℤ) := floor_linear_interval x (120/23) (200/37) (37/20) 9
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

theorem innerKernel_cell_021 (x : ℚ) (hl : (200/37)≤x) (hr : x<(11/2)) :
    innerKernel x = (319/40)*x+-43 := by
  have hf0 : ⌊(23/10)*x⌋=(12:ℤ) := floor_linear_interval x (200/37) (11/2) (23/10) 12
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(0:ℤ) := floor_linear_interval x (200/37) (11/2) (3/20) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(10:ℤ) := floor_linear_interval x (200/37) (11/2) 2 10
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (200/37) (11/2) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(5:ℤ) := floor_linear_interval x (200/37) (11/2) 1 5
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(10:ℤ) := floor_linear_interval x (200/37) (11/2) (37/20) 10
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

theorem innerKernel_cell_022 (x : ℚ) (hl : (11/2)≤x) (hr : x<(240/43)) :
    innerKernel x = (359/40)*x+(-97/2) := by
  have hf0 : ⌊(23/10)*x⌋=(12:ℤ) := floor_linear_interval x (11/2) (240/43) (23/10) 12
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(0:ℤ) := floor_linear_interval x (11/2) (240/43) (3/20) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(11:ℤ) := floor_linear_interval x (11/2) (240/43) 2 11
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (11/2) (240/43) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(5:ℤ) := floor_linear_interval x (11/2) (240/43) 1 5
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(10:ℤ) := floor_linear_interval x (11/2) (240/43) (37/20) 10
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

theorem innerKernel_cell_023 (x : ℚ) (hl : (240/43)≤x) (hr : x<(130/23)) :
    innerKernel x = (23/4)*x+(-61/2) := by
  have hf0 : ⌊(23/10)*x⌋=(12:ℤ) := floor_linear_interval x (240/43) (130/23) (23/10) 12
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(0:ℤ) := floor_linear_interval x (240/43) (130/23) (3/20) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(11:ℤ) := floor_linear_interval x (240/43) (130/23) 2 11
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (240/43) (130/23) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(5:ℤ) := floor_linear_interval x (240/43) (130/23) 1 5
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(10:ℤ) := floor_linear_interval x (240/43) (130/23) (37/20) 10
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

theorem innerKernel_cell_024 (x : ℚ) (hl : (130/23)≤x) (hr : x<(220/37)) :
    innerKernel x = (23/5)*x+-24 := by
  have hf0 : ⌊(23/10)*x⌋=(13:ℤ) := floor_linear_interval x (130/23) (220/37) (23/10) 13
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(0:ℤ) := floor_linear_interval x (130/23) (220/37) (3/20) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(11:ℤ) := floor_linear_interval x (130/23) (220/37) 2 11
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (130/23) (220/37) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(5:ℤ) := floor_linear_interval x (130/23) (220/37) 1 5
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(10:ℤ) := floor_linear_interval x (130/23) (220/37) (37/20) 10
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

theorem innerKernel_cell_025 (x : ℚ) (hl : (220/37)≤x) (hr : x<6) :
    innerKernel x = (129/20)*x+-35 := by
  have hf0 : ⌊(23/10)*x⌋=(13:ℤ) := floor_linear_interval x (220/37) 6 (23/10) 13
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(0:ℤ) := floor_linear_interval x (220/37) 6 (3/20) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(11:ℤ) := floor_linear_interval x (220/37) 6 2 11
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (220/37) 6 (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(5:ℤ) := floor_linear_interval x (220/37) 6 1 5
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(11:ℤ) := floor_linear_interval x (220/37) 6 (37/20) 11
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

theorem innerKernel_cell_026 (x : ℚ) (hl : 6≤x) (hr : x<(260/43)) :
    innerKernel x = (28/5)*x+-41 := by
  have hf0 : ⌊(23/10)*x⌋=(13:ℤ) := floor_linear_interval x 6 (260/43) (23/10) 13
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(0:ℤ) := floor_linear_interval x 6 (260/43) (3/20) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(12:ℤ) := floor_linear_interval x 6 (260/43) 2 12
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x 6 (260/43) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(6:ℤ) := floor_linear_interval x 6 (260/43) 1 6
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(11:ℤ) := floor_linear_interval x 6 (260/43) (37/20) 11
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
