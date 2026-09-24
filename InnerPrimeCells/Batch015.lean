import InnerPrimeCellBase

set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

noncomputable section
namespace Zeta5InnerAsymptotics

theorem innerKernel_cell_135 (x : ℚ) (hl : (700/37)≤x) (hr : x<19) :
    innerKernel x = (393/20)*x+-357 := by
  have hf0 : ⌊(23/10)*x⌋=(43:ℤ) := floor_linear_interval x (700/37) 19 (23/10) 43
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(2:ℤ) := floor_linear_interval x (700/37) 19 (3/20) 2
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(37:ℤ) := floor_linear_interval x (700/37) 19 2 37
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(1:ℤ) := floor_linear_interval x (700/37) 19 (3/40) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(18:ℤ) := floor_linear_interval x (700/37) 19 1 18
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(35:ℤ) := floor_linear_interval x (700/37) 19 (37/20) 35
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

theorem innerKernel_cell_136 (x : ℚ) (hl : 19≤x) (hr : x<(820/43)) :
    innerKernel x = (94/5)*x+-376 := by
  have hf0 : ⌊(23/10)*x⌋=(43:ℤ) := floor_linear_interval x 19 (820/43) (23/10) 43
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(2:ℤ) := floor_linear_interval x 19 (820/43) (3/20) 2
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(38:ℤ) := floor_linear_interval x 19 (820/43) 2 38
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(1:ℤ) := floor_linear_interval x 19 (820/43) (3/40) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(19:ℤ) := floor_linear_interval x 19 (820/43) 1 19
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(35:ℤ) := floor_linear_interval x 19 (820/43) (37/20) 35
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

theorem innerKernel_cell_137 (x : ℚ) (hl : (820/43)≤x) (hr : x<(440/23)) :
    innerKernel x = (94/5)*x+-376 := by
  have hf0 : ⌊(23/10)*x⌋=(43:ℤ) := floor_linear_interval x (820/43) (440/23) (23/10) 43
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(2:ℤ) := floor_linear_interval x (820/43) (440/23) (3/20) 2
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(38:ℤ) := floor_linear_interval x (820/43) (440/23) 2 38
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(1:ℤ) := floor_linear_interval x (820/43) (440/23) (3/40) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(19:ℤ) := floor_linear_interval x (820/43) (440/23) 1 19
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(35:ℤ) := floor_linear_interval x (820/43) (440/23) (37/20) 35
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

theorem innerKernel_cell_138 (x : ℚ) (hl : (440/23)≤x) (hr : x<(720/37)) :
    innerKernel x = (353/20)*x+-354 := by
  have hf0 : ⌊(23/10)*x⌋=(44:ℤ) := floor_linear_interval x (440/23) (720/37) (23/10) 44
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(2:ℤ) := floor_linear_interval x (440/23) (720/37) (3/20) 2
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(38:ℤ) := floor_linear_interval x (440/23) (720/37) 2 38
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(1:ℤ) := floor_linear_interval x (440/23) (720/37) (3/40) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(19:ℤ) := floor_linear_interval x (440/23) (720/37) 1 19
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(35:ℤ) := floor_linear_interval x (440/23) (720/37) (37/20) 35
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

theorem innerKernel_cell_139 (x : ℚ) (hl : (720/37)≤x) (hr : x<(39/2)) :
    innerKernel x = (891/40)*x+-444 := by
  have hf0 : ⌊(23/10)*x⌋=(44:ℤ) := floor_linear_interval x (720/37) (39/2) (23/10) 44
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(2:ℤ) := floor_linear_interval x (720/37) (39/2) (3/20) 2
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(38:ℤ) := floor_linear_interval x (720/37) (39/2) 2 38
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(1:ℤ) := floor_linear_interval x (720/37) (39/2) (3/40) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(19:ℤ) := floor_linear_interval x (720/37) (39/2) 1 19
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(36:ℤ) := floor_linear_interval x (720/37) (39/2) (37/20) 36
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

theorem innerKernel_cell_140 (x : ℚ) (hl : (39/2)≤x) (hr : x<(840/43)) :
    innerKernel x = (931/40)*x+(-927/2) := by
  have hf0 : ⌊(23/10)*x⌋=(44:ℤ) := floor_linear_interval x (39/2) (840/43) (23/10) 44
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(2:ℤ) := floor_linear_interval x (39/2) (840/43) (3/20) 2
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(39:ℤ) := floor_linear_interval x (39/2) (840/43) 2 39
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(1:ℤ) := floor_linear_interval x (39/2) (840/43) (3/40) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(19:ℤ) := floor_linear_interval x (39/2) (840/43) 1 19
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(36:ℤ) := floor_linear_interval x (39/2) (840/43) (37/20) 36
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

theorem innerKernel_cell_141 (x : ℚ) (hl : (840/43)≤x) (hr : x<(450/23)) :
    innerKernel x = (401/20)*x+(-801/2) := by
  have hf0 : ⌊(23/10)*x⌋=(44:ℤ) := floor_linear_interval x (840/43) (450/23) (23/10) 44
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(2:ℤ) := floor_linear_interval x (840/43) (450/23) (3/20) 2
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(39:ℤ) := floor_linear_interval x (840/43) (450/23) 2 39
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(1:ℤ) := floor_linear_interval x (840/43) (450/23) (3/40) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(19:ℤ) := floor_linear_interval x (840/43) (450/23) 1 19
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(36:ℤ) := floor_linear_interval x (840/43) (450/23) (37/20) 36
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

theorem innerKernel_cell_142 (x : ℚ) (hl : (450/23)≤x) (hr : x<20) :
    innerKernel x = (189/10)*x+-378 := by
  have hf0 : ⌊(23/10)*x⌋=(45:ℤ) := floor_linear_interval x (450/23) 20 (23/10) 45
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(2:ℤ) := floor_linear_interval x (450/23) 20 (3/20) 2
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(39:ℤ) := floor_linear_interval x (450/23) 20 2 39
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(1:ℤ) := floor_linear_interval x (450/23) 20 (3/40) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(19:ℤ) := floor_linear_interval x (450/23) 20 1 19
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(36:ℤ) := floor_linear_interval x (450/23) 20 (37/20) 36
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
