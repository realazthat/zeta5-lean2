import AppendixCellBase
import AppendixField.Batch081
import AppendixField.Batch082
import AppendixField.Batch083
import AppendixPotential.Batch082
import AppendixPotential.Batch083
import AppendixPotential.Batch084
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_656 : cellBound ((194899235804257/256000000000000 : ℚ) : ℝ) ((78210366862569/102400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (194899235804257/256000000000000 : ℝ) ≤ (-9872944647442491613/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_656 (by norm_num)
  have hUr : potential (78210366862569/102400000000000 : ℝ) ≤ (-9872944647442491613/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_657 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_656
  linarith only [hU, hF]

theorem cell_bound_657 : cellBound ((78210366862569/102400000000000 : ℚ) : ℝ) ((49038149627147/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (78210366862569/102400000000000 : ℝ) ≤ (-48925524430880574279/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_657 (by norm_num)
  have hUr : potential (49038149627147/64000000000000 : ℝ) ≤ (-48925524430880574279/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_658 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_657
  linarith only [hU, hF]

theorem cell_bound_658 : cellBound ((49038149627147/64000000000000 : ℚ) : ℝ) ((393558559721507/512000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (49038149627147/64000000000000 : ℝ) ≤ (-48490278315933392507/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_658 (by norm_num)
  have hUr : potential (393558559721507/512000000000000 : ℝ) ≤ (-48490278315933392507/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_659 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_658
  linarith only [hU, hF]

theorem cell_bound_659 : cellBound ((393558559721507/512000000000000 : ℚ) : ℝ) ((197405961212919/256000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (393558559721507/512000000000000 : ℝ) ≤ (-48058756049563777699/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_659 (by norm_num)
  have hUr : potential (197405961212919/256000000000000 : ℝ) ≤ (-48058756049563777699/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_660 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_659
  linarith only [hU, hF]

theorem cell_bound_660 : cellBound ((197405961212919/256000000000000 : ℚ) : ℝ) ((396065285130169/512000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (197405961212919/256000000000000 : ℝ) ≤ (-47630767127134964773/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_660 (by norm_num)
  have hUr : potential (396065285130169/512000000000000 : ℝ) ≤ (-47630767127134964773/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_661 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_660
  linarith only [hU, hF]

theorem cell_bound_661 : cellBound ((396065285130169/512000000000000 : ℚ) : ℝ) ((794637295669/1024000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (396065285130169/512000000000000 : ℝ) ≤ (-9441230029588570797/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_661 (by norm_num)
  have hUr : potential (794637295669/1024000000000 : ℝ) ≤ (-9441230029588570797/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_662 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_661
  linarith only [hU, hF]

theorem cell_bound_662 : cellBound ((794637295669/1024000000000 : ℚ) : ℝ) ((398572010538831/512000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (794637295669/1024000000000 : ℝ) ≤ (-11696191254902441639/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_662 (by norm_num)
  have hUr : potential (398572010538831/512000000000000 : ℝ) ≤ (-11696191254902441639/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_663 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_662
  linarith only [hU, hF]

theorem cell_bound_663 : cellBound ((398572010538831/512000000000000 : ℚ) : ℝ) ((199912686621581/256000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (398572010538831/512000000000000 : ℝ) ≤ (-46366488682696457961/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_663 (by norm_num)
  have hUr : potential (199912686621581/256000000000000 : ℝ) ≤ (-46366488682696457961/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_664 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_663
  linarith only [hU, hF]

theorem cell_bound_664 : cellBound ((199912686621581/256000000000000 : ℚ) : ℝ) ((25145756165739/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (199912686621581/256000000000000 : ℝ) ≤ (-45538833664648416689/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_664 (by norm_num)
  have hUr : potential (25145756165739/32000000000000 : ℝ) ≤ (-45538833664648416689/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_665 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_664
  linarith only [hU, hF]

theorem cell_bound_665 : cellBound ((25145756165739/32000000000000 : ℚ) : ℝ) ((202419412030243/256000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (25145756165739/32000000000000 : ℝ) ≤ (-894448564622428297/2000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_665 (by norm_num)
  have hUr : potential (202419412030243/256000000000000 : ℝ) ≤ (-894448564622428297/2000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_666 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_665
  linarith only [hU, hF]

theorem cell_bound_666 : cellBound ((202419412030243/256000000000000 : ℚ) : ℝ) ((101836387367287/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (202419412030243/256000000000000 : ℝ) ≤ (-10979160232574520107/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_666 (by norm_num)
  have hUr : potential (101836387367287/128000000000000 : ℝ) ≤ (-10979160232574520107/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_667 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_666
  linarith only [hU, hF]

theorem cell_bound_667 : cellBound ((101836387367287/128000000000000 : ℚ) : ℝ) ((40985227487781/51200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (101836387367287/128000000000000 : ℝ) ≤ (-43120930805945258891/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_667 (by norm_num)
  have hUr : potential (40985227487781/51200000000000 : ℝ) ≤ (-43120930805945258891/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_668 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_667
  linarith only [hU, hF]

theorem cell_bound_668 : cellBound ((40985227487781/51200000000000 : ℚ) : ℝ) ((51544875035809/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (40985227487781/51200000000000 : ℝ) ≤ (-21167414161187288159/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_668 (by norm_num)
  have hUr : potential (51544875035809/64000000000000 : ℝ) ≤ (-21167414161187288159/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_669 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_668
  linarith only [hU, hF]

theorem cell_bound_669 : cellBound ((51544875035809/64000000000000 : ℚ) : ℝ) ((104343112775949/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (51544875035809/64000000000000 : ℝ) ≤ (-20394914022721221953/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_669 (by norm_num)
  have hUr : potential (104343112775949/128000000000000 : ℝ) ≤ (-20394914022721221953/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_670 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_669
  linarith only [hU, hF]

theorem cell_bound_670 : cellBound ((104343112775949/128000000000000 : ℚ) : ℝ) ((2639911887007/3200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (104343112775949/128000000000000 : ℝ) ≤ (-9819700629393880359/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_670 (by norm_num)
  have hUr : potential (2639911887007/3200000000000 : ℝ) ≤ (-9819700629393880359/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_671 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_670
  linarith only [hU, hF]

theorem cell_bound_671 : cellBound ((2639911887007/3200000000000 : ℚ) : ℝ) ((106849838184611/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2639911887007/3200000000000 : ℝ) ≤ (-7559882206980521523/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_671 (by norm_num)
  have hUr : potential (106849838184611/128000000000000 : ℝ) ≤ (-7559882206980521523/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_672 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_671
  linarith only [hU, hF]

#print axioms cell_bound_671
end Zeta5AppendixNumerics
