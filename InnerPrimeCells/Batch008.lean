import InnerPrimeCellBase

set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

noncomputable section
namespace Zeta5InnerAsymptotics

theorem innerKernel_cell_072 (x : ℚ) (hl : (23/2)≤x) (hr : x<(500/43)) :
    innerKernel x = (259/40)*x+(-261/2) := by
  have hf0 : ⌊(23/10)*x⌋=(26:ℤ) := floor_linear_interval x (23/2) (500/43) (23/10) 26
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(1:ℤ) := floor_linear_interval x (23/2) (500/43) (3/20) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(23:ℤ) := floor_linear_interval x (23/2) (500/43) 2 23
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (23/2) (500/43) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(11:ℤ) := floor_linear_interval x (23/2) (500/43) 1 11
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(21:ℤ) := floor_linear_interval x (23/2) (500/43) (37/20) 21
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

theorem innerKernel_cell_073 (x : ℚ) (hl : (500/43)≤x) (hr : x<(270/23)) :
    innerKernel x = (259/40)*x+(-261/2) := by
  have hf0 : ⌊(23/10)*x⌋=(26:ℤ) := floor_linear_interval x (500/43) (270/23) (23/10) 26
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(1:ℤ) := floor_linear_interval x (500/43) (270/23) (3/20) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(23:ℤ) := floor_linear_interval x (500/43) (270/23) 2 23
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (500/43) (270/23) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(11:ℤ) := floor_linear_interval x (500/43) (270/23) 1 11
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(21:ℤ) := floor_linear_interval x (500/43) (270/23) (37/20) 21
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

theorem innerKernel_cell_074 (x : ℚ) (hl : (270/23)≤x) (hr : x<(440/37)) :
    innerKernel x = (213/40)*x+-117 := by
  have hf0 : ⌊(23/10)*x⌋=(27:ℤ) := floor_linear_interval x (270/23) (440/37) (23/10) 27
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(1:ℤ) := floor_linear_interval x (270/23) (440/37) (3/20) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(23:ℤ) := floor_linear_interval x (270/23) (440/37) 2 23
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (270/23) (440/37) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(11:ℤ) := floor_linear_interval x (270/23) (440/37) 1 11
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(21:ℤ) := floor_linear_interval x (270/23) (440/37) (37/20) 21
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

theorem innerKernel_cell_075 (x : ℚ) (hl : (440/37)≤x) (hr : x<12) :
    innerKernel x = (199/20)*x+-172 := by
  have hf0 : ⌊(23/10)*x⌋=(27:ℤ) := floor_linear_interval x (440/37) 12 (23/10) 27
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(1:ℤ) := floor_linear_interval x (440/37) 12 (3/20) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(23:ℤ) := floor_linear_interval x (440/37) 12 2 23
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (440/37) 12 (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(11:ℤ) := floor_linear_interval x (440/37) 12 1 11
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(22:ℤ) := floor_linear_interval x (440/37) 12 (37/20) 22
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

theorem innerKernel_cell_076 (x : ℚ) (hl : 12≤x) (hr : x<(520/43)) :
    innerKernel x = (91/10)*x+-184 := by
  have hf0 : ⌊(23/10)*x⌋=(27:ℤ) := floor_linear_interval x 12 (520/43) (23/10) 27
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(1:ℤ) := floor_linear_interval x 12 (520/43) (3/20) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(24:ℤ) := floor_linear_interval x 12 (520/43) 2 24
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x 12 (520/43) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(12:ℤ) := floor_linear_interval x 12 (520/43) 1 12
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(22:ℤ) := floor_linear_interval x 12 (520/43) (37/20) 22
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

theorem innerKernel_cell_077 (x : ℚ) (hl : (520/43)≤x) (hr : x<(280/23)) :
    innerKernel x = (47/8)*x+-145 := by
  have hf0 : ⌊(23/10)*x⌋=(27:ℤ) := floor_linear_interval x (520/43) (280/23) (23/10) 27
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(1:ℤ) := floor_linear_interval x (520/43) (280/23) (3/20) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(24:ℤ) := floor_linear_interval x (520/43) (280/23) 2 24
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (520/43) (280/23) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(12:ℤ) := floor_linear_interval x (520/43) (280/23) 1 12
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(22:ℤ) := floor_linear_interval x (520/43) (280/23) (37/20) 22
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

theorem innerKernel_cell_078 (x : ℚ) (hl : (280/23)≤x) (hr : x<(460/37)) :
    innerKernel x = (189/40)*x+-131 := by
  have hf0 : ⌊(23/10)*x⌋=(28:ℤ) := floor_linear_interval x (280/23) (460/37) (23/10) 28
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(1:ℤ) := floor_linear_interval x (280/23) (460/37) (3/20) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(24:ℤ) := floor_linear_interval x (280/23) (460/37) 2 24
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (280/23) (460/37) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(12:ℤ) := floor_linear_interval x (280/23) (460/37) 1 12
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(22:ℤ) := floor_linear_interval x (280/23) (460/37) (37/20) 22
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

theorem innerKernel_cell_079 (x : ℚ) (hl : (460/37)≤x) (hr : x<(25/2)) :
    innerKernel x = (263/40)*x+-154 := by
  have hf0 : ⌊(23/10)*x⌋=(28:ℤ) := floor_linear_interval x (460/37) (25/2) (23/10) 28
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(1:ℤ) := floor_linear_interval x (460/37) (25/2) (3/20) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(24:ℤ) := floor_linear_interval x (460/37) (25/2) 2 24
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (460/37) (25/2) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(12:ℤ) := floor_linear_interval x (460/37) (25/2) 1 12
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(23:ℤ) := floor_linear_interval x (460/37) (25/2) (37/20) 23
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

theorem innerKernel_cell_080 (x : ℚ) (hl : (25/2)≤x) (hr : x<(540/43)) :
    innerKernel x = (303/40)*x+(-333/2) := by
  have hf0 : ⌊(23/10)*x⌋=(28:ℤ) := floor_linear_interval x (25/2) (540/43) (23/10) 28
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf1 : ⌊(3/20)*x⌋=(1:ℤ) := floor_linear_interval x (25/2) (540/43) (3/20) 1
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊2*x⌋=(25:ℤ) := floor_linear_interval x (25/2) (540/43) 2 25
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf3 : ⌊(3/40)*x⌋=(0:ℤ) := floor_linear_interval x (25/2) (540/43) (3/40) 0
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf4 : ⌊1*x⌋=(12:ℤ) := floor_linear_interval x (25/2) (540/43) 1 12
    hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf5 : ⌊(37/20)*x⌋=(23:ℤ) := floor_linear_interval x (25/2) (540/43) (37/20) 23
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
