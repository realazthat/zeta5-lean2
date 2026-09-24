import OuterPrimeArithmetic
import Mathlib.Tactic

noncomputable section
namespace Zeta5OuterAsymptotics
open Zeta5InnerAsymptotics

private theorem floor_div_interval (y l r a : ℚ) (m : ℤ)
    (hy : 0<y) (hl : l<y) (hr : y≤r) (hm : 0≤(m:ℚ))
    (hlo : (m:ℚ)*r≤a) (hhi : a≤((m:ℚ)+1)*l) :
    ⌊a/y⌋=m := by
  apply Int.floor_eq_iff.mpr
  constructor
  · rw [le_div_iff₀ hy]
    nlinarith
  · rw [div_lt_iff₀ hy]
    nlinarith

theorem outerKernel_cell_00 (y : ℚ) (hl : (1/3)<y) (hr : y≤(43/120)) :
    outerKernel y = (36/5)+-9*y := by
  have hy : 0<y := by linarith
  have hf1 : ⌊(1:ℚ)/y⌋=(2:ℤ) := floor_div_interval y (1/3) (43/120) 1 2
    hy hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf0 : ⌊((3:ℚ)/40)/y⌋=(0:ℤ) := floor_div_interval y (1/3) (43/120) (3/40) 0
    hy hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊((37:ℚ)/20)/y⌋=(5:ℤ) := floor_div_interval y (1/3) (43/120) (37/20) 5
    hy hl hr (by norm_num) (by norm_num) (by norm_num)
  unfold outerKernel scalarLimit floorIntegral
  simp only [mul_one_div]
  rw [show 2*((37:ℚ)/40/y)=(37/20)/y by ring,hf1,hf0,hf2]
  norm_num
  unfold outerResidue outerResidueMass
  rw [if_neg (by linarith : ¬(1:ℚ)<y)]
  rw [if_neg (by linarith : ¬(1:ℚ)<2*y)]
  rw [min_eq_left (by linarith)]
  rw [max_eq_left (by linarith)]
  field_simp
  <;> ring

theorem outerKernel_cell_01 (y : ℚ) (hl : (43/120)<y) (hr : y≤(37/100)) :
    outerKernel y = (503/40)+-24*y := by
  have hy : 0<y := by linarith
  have hf1 : ⌊(1:ℚ)/y⌋=(2:ℤ) := floor_div_interval y (43/120) (37/100) 1 2
    hy hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf0 : ⌊((3:ℚ)/40)/y⌋=(0:ℤ) := floor_div_interval y (43/120) (37/100) (3/40) 0
    hy hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊((37:ℚ)/20)/y⌋=(5:ℤ) := floor_div_interval y (43/120) (37/100) (37/20) 5
    hy hl hr (by norm_num) (by norm_num) (by norm_num)
  unfold outerKernel scalarLimit floorIntegral
  simp only [mul_one_div]
  rw [show 2*((37:ℚ)/40/y)=(37/20)/y by ring,hf1,hf0,hf2]
  norm_num
  unfold outerResidue outerResidueMass
  rw [if_neg (by linarith : ¬(1:ℚ)<y)]
  rw [if_neg (by linarith : ¬(1:ℚ)<2*y)]
  rw [min_eq_left (by linarith)]
  rw [max_eq_right (by linarith)]
  field_simp
  <;> ring

theorem outerKernel_cell_02 (y : ℚ) (hl : (37/100)<y) (hr : y≤(13/30)) :
    outerKernel y = (429/40)+-19*y := by
  have hy : 0<y := by linarith
  have hf1 : ⌊(1:ℚ)/y⌋=(2:ℤ) := floor_div_interval y (37/100) (13/30) 1 2
    hy hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf0 : ⌊((3:ℚ)/40)/y⌋=(0:ℤ) := floor_div_interval y (37/100) (13/30) (3/40) 0
    hy hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊((37:ℚ)/20)/y⌋=(4:ℤ) := floor_div_interval y (37/100) (13/30) (37/20) 4
    hy hl hr (by norm_num) (by norm_num) (by norm_num)
  unfold outerKernel scalarLimit floorIntegral
  simp only [mul_one_div]
  rw [show 2*((37:ℚ)/40/y)=(37/20)/y by ring,hf1,hf0,hf2]
  norm_num
  unfold outerResidue outerResidueMass
  rw [if_neg (by linarith : ¬(1:ℚ)<y)]
  rw [if_neg (by linarith : ¬(1:ℚ)<2*y)]
  rw [min_eq_left (by linarith)]
  rw [max_eq_right (by linarith)]
  field_simp
  <;> ring

theorem outerKernel_cell_03 (y : ℚ) (hl : (13/30)<y) (hr : y≤(37/80)) :
    outerKernel y = (429/40)+-19*y := by
  have hy : 0<y := by linarith
  have hf1 : ⌊(1:ℚ)/y⌋=(2:ℤ) := floor_div_interval y (13/30) (37/80) 1 2
    hy hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf0 : ⌊((3:ℚ)/40)/y⌋=(0:ℤ) := floor_div_interval y (13/30) (37/80) (3/40) 0
    hy hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊((37:ℚ)/20)/y⌋=(4:ℤ) := floor_div_interval y (13/30) (37/80) (37/20) 4
    hy hl hr (by norm_num) (by norm_num) (by norm_num)
  unfold outerKernel scalarLimit floorIntegral
  simp only [mul_one_div]
  rw [show 2*((37:ℚ)/40/y)=(37/20)/y by ring,hf1,hf0,hf2]
  norm_num
  unfold outerResidue outerResidueMass
  rw [if_neg (by linarith : ¬(1:ℚ)<y)]
  rw [if_neg (by linarith : ¬(1:ℚ)<2*y)]
  rw [min_eq_left (by linarith)]
  rw [max_eq_right (by linarith)]
  field_simp
  <;> ring

theorem outerKernel_cell_04 (y : ℚ) (hl : (37/80)<y) (hr : y≤(1/2)) :
    outerKernel y = (17/4)+-5*y := by
  have hy : 0<y := by linarith
  have hf1 : ⌊(1:ℚ)/y⌋=(2:ℤ) := floor_div_interval y (37/80) (1/2) 1 2
    hy hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf0 : ⌊((3:ℚ)/40)/y⌋=(0:ℤ) := floor_div_interval y (37/80) (1/2) (3/40) 0
    hy hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊((37:ℚ)/20)/y⌋=(3:ℤ) := floor_div_interval y (37/80) (1/2) (37/20) 3
    hy hl hr (by norm_num) (by norm_num) (by norm_num)
  unfold outerKernel scalarLimit floorIntegral
  simp only [mul_one_div]
  rw [show 2*((37:ℚ)/40/y)=(37/20)/y by ring,hf1,hf0,hf2]
  norm_num
  unfold outerResidue outerResidueMass
  rw [if_neg (by linarith : ¬(1:ℚ)<y)]
  rw [if_neg (by linarith : ¬(1:ℚ)<2*y)]
  rw [min_eq_right (by linarith)]
  rw [max_eq_right (by linarith)]
  field_simp
  <;> ring

theorem outerKernel_cell_05 (y : ℚ) (hl : (1/2)<y) (hr : y≤(43/80)) :
    outerKernel y = (51/10)+-3*y := by
  have hy : 0<y := by linarith
  have hf1 : ⌊(1:ℚ)/y⌋=(1:ℤ) := floor_div_interval y (1/2) (43/80) 1 1
    hy hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf0 : ⌊((3:ℚ)/40)/y⌋=(0:ℤ) := floor_div_interval y (1/2) (43/80) (3/40) 0
    hy hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊((37:ℚ)/20)/y⌋=(3:ℤ) := floor_div_interval y (1/2) (43/80) (37/20) 3
    hy hl hr (by norm_num) (by norm_num) (by norm_num)
  unfold outerKernel scalarLimit floorIntegral
  simp only [mul_one_div]
  rw [show 2*((37:ℚ)/40/y)=(37/20)/y by ring,hf1,hf0,hf2]
  norm_num
  unfold outerResidue outerResidueMass
  rw [if_neg (by linarith : ¬(1:ℚ)<y)]
  rw [if_pos (by linarith : (1:ℚ)<2*y)]
  rw [min_eq_left (by linarith)]
  rw [max_eq_left (by linarith)]
  rw [max_eq_left (by linarith)]
  field_simp
  <;> ring

theorem outerKernel_cell_06 (y : ℚ) (hl : (43/80)<y) (hr : y≤(37/60)) :
    outerKernel y = (231/20)+-15*y := by
  have hy : 0<y := by linarith
  have hf1 : ⌊(1:ℚ)/y⌋=(1:ℤ) := floor_div_interval y (43/80) (37/60) 1 1
    hy hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf0 : ⌊((3:ℚ)/40)/y⌋=(0:ℤ) := floor_div_interval y (43/80) (37/60) (3/40) 0
    hy hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊((37:ℚ)/20)/y⌋=(3:ℤ) := floor_div_interval y (43/80) (37/60) (37/20) 3
    hy hl hr (by norm_num) (by norm_num) (by norm_num)
  unfold outerKernel scalarLimit floorIntegral
  simp only [mul_one_div]
  rw [show 2*((37:ℚ)/40/y)=(37/20)/y by ring,hf1,hf0,hf2]
  norm_num
  unfold outerResidue outerResidueMass
  rw [if_neg (by linarith : ¬(1:ℚ)<y)]
  rw [if_pos (by linarith : (1:ℚ)<2*y)]
  rw [min_eq_left (by linarith)]
  rw [max_eq_right (by linarith)]
  rw [max_eq_left (by linarith)]
  field_simp
  <;> ring

theorem outerKernel_cell_07 (y : ℚ) (hl : (37/60)<y) (hr : y≤(13/20)) :
    outerKernel y = (97/10)+-12*y := by
  have hy : 0<y := by linarith
  have hf1 : ⌊(1:ℚ)/y⌋=(1:ℤ) := floor_div_interval y (37/60) (13/20) 1 1
    hy hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf0 : ⌊((3:ℚ)/40)/y⌋=(0:ℤ) := floor_div_interval y (37/60) (13/20) (3/40) 0
    hy hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊((37:ℚ)/20)/y⌋=(2:ℤ) := floor_div_interval y (37/60) (13/20) (37/20) 2
    hy hl hr (by norm_num) (by norm_num) (by norm_num)
  unfold outerKernel scalarLimit floorIntegral
  simp only [mul_one_div]
  rw [show 2*((37:ℚ)/40/y)=(37/20)/y by ring,hf1,hf0,hf2]
  norm_num
  unfold outerResidue outerResidueMass
  rw [if_neg (by linarith : ¬(1:ℚ)<y)]
  rw [if_pos (by linarith : (1:ℚ)<2*y)]
  rw [min_eq_left (by linarith)]
  rw [max_eq_right (by linarith)]
  rw [max_eq_left (by linarith)]
  field_simp
  <;> ring

theorem outerKernel_cell_08 (y : ℚ) (hl : (13/20)<y) (hr : y≤(37/40)) :
    outerKernel y = (42/5)+-10*y := by
  have hy : 0<y := by linarith
  have hf1 : ⌊(1:ℚ)/y⌋=(1:ℤ) := floor_div_interval y (13/20) (37/40) 1 1
    hy hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf0 : ⌊((3:ℚ)/40)/y⌋=(0:ℤ) := floor_div_interval y (13/20) (37/40) (3/40) 0
    hy hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊((37:ℚ)/20)/y⌋=(2:ℤ) := floor_div_interval y (13/20) (37/40) (37/20) 2
    hy hl hr (by norm_num) (by norm_num) (by norm_num)
  unfold outerKernel scalarLimit floorIntegral
  simp only [mul_one_div]
  rw [show 2*((37:ℚ)/40/y)=(37/20)/y by ring,hf1,hf0,hf2]
  norm_num
  unfold outerResidue outerResidueMass
  rw [if_neg (by linarith : ¬(1:ℚ)<y)]
  rw [if_pos (by linarith : (1:ℚ)<2*y)]
  rw [min_eq_left (by linarith)]
  rw [max_eq_right (by linarith)]
  rw [max_eq_right (by linarith)]
  field_simp
  <;> ring

theorem outerKernel_cell_09 (y : ℚ) (hl : (37/40)<y) (hr : y≤1) :
    outerKernel y = 1+-2*y := by
  have hy : 0<y := by linarith
  have hf1 : ⌊(1:ℚ)/y⌋=(1:ℤ) := floor_div_interval y (37/40) 1 1 1
    hy hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf0 : ⌊((3:ℚ)/40)/y⌋=(0:ℤ) := floor_div_interval y (37/40) 1 (3/40) 0
    hy hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊((37:ℚ)/20)/y⌋=(1:ℤ) := floor_div_interval y (37/40) 1 (37/20) 1
    hy hl hr (by norm_num) (by norm_num) (by norm_num)
  unfold outerKernel scalarLimit floorIntegral
  simp only [mul_one_div]
  rw [show 2*((37:ℚ)/40/y)=(37/20)/y by ring,hf1,hf0,hf2]
  norm_num
  unfold outerResidue outerResidueMass
  rw [if_neg (by linarith : ¬(1:ℚ)<y)]
  rw [if_pos (by linarith : (1:ℚ)<2*y)]
  rw [min_eq_right (by linarith)]
  rw [max_eq_right (by linarith)]
  rw [max_eq_right (by linarith)]
  field_simp
  <;> ring

theorem outerKernel_cell_10 (y : ℚ) (hl : 1<y) (hr : y≤(37/20)) :
    outerKernel y = (37/20)+-1*y := by
  have hy : 0<y := by linarith
  have hf1 : ⌊(1:ℚ)/y⌋=(0:ℤ) := floor_div_interval y 1 (37/20) 1 0
    hy hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf0 : ⌊((3:ℚ)/40)/y⌋=(0:ℤ) := floor_div_interval y 1 (37/20) (3/40) 0
    hy hl hr (by norm_num) (by norm_num) (by norm_num)
  have hf2 : ⌊((37:ℚ)/20)/y⌋=(1:ℤ) := floor_div_interval y 1 (37/20) (37/20) 1
    hy hl hr (by norm_num) (by norm_num) (by norm_num)
  unfold outerKernel scalarLimit floorIntegral
  simp only [mul_one_div]
  rw [show 2*((37:ℚ)/40/y)=(37/20)/y by ring,hf1,hf0,hf2]
  norm_num
  unfold outerResidue outerResidueMass
  rw [if_pos (by linarith : (1:ℚ)<y)]
  field_simp
  <;> ring

def outerCellLeft : Fin 11 → ℚ := ![(1/3),(43/120),(37/100),(13/30),(37/80),(1/2),(43/80),(37/60),(13/20),(37/40),1]
def outerCellRight : Fin 11 → ℚ := ![(43/120),(37/100),(13/30),(37/80),(1/2),(43/80),(37/60),(13/20),(37/40),1,(37/20)]
def outerCellConstant : Fin 11 → ℚ := ![(36/5),(503/40),(429/40),(429/40),(17/4),(51/10),(231/20),(97/10),(42/5),1,(37/20)]
def outerCellSlope : Fin 11 → ℚ := ![-9,-24,-19,-19,-5,-3,-15,-12,-10,-2,-1]

theorem outerKernel_on_cells (i : Fin 11) (y : ℚ)
    (hl : outerCellLeft i<y) (hr : y≤outerCellRight i) :
    outerKernel y=outerCellConstant i+outerCellSlope i*y := by
  fin_cases i
  · exact outerKernel_cell_00 y hl hr
  · exact outerKernel_cell_01 y hl hr
  · exact outerKernel_cell_02 y hl hr
  · exact outerKernel_cell_03 y hl hr
  · exact outerKernel_cell_04 y hl hr
  · exact outerKernel_cell_05 y hl hr
  · exact outerKernel_cell_06 y hl hr
  · exact outerKernel_cell_07 y hl hr
  · exact outerKernel_cell_08 y hl hr
  · exact outerKernel_cell_09 y hl hr
  · exact outerKernel_cell_10 y hl hr

def outerIntegral : ℚ := ∑ i : Fin 11,
  (outerCellConstant i*(outerCellRight i-outerCellLeft i)+
  outerCellSlope i*((outerCellRight i)^2-(outerCellLeft i)^2)/2)

theorem outerIntegral_exact : outerIntegral=(127751:ℚ)/96000+9/640 := by
  norm_num [outerIntegral,outerCellConstant,outerCellSlope,outerCellRight,outerCellLeft,Fin.sum_univ_succ]

#print axioms outerKernel_on_cells
#print axioms outerIntegral_exact
end Zeta5OuterAsymptotics
