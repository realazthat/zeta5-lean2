import AppendixCellBase
import AppendixField.Batch049
import AppendixField.Batch050
import AppendixField.Batch051
import AppendixPotential.Batch050
import AppendixPotential.Batch051
import AppendixPotential.Batch052
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_400 : cellBound ((12864925888431/32000000000000 : ℚ) : ℝ) ((1294864303869/3200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (12864925888431/32000000000000 : ℝ) ≤ (-165401711984698071/125000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_400 (by norm_num)
  have hUr : potential (1294864303869/3200000000000 : ℝ) ≤ (-165401711984698071/125000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_401 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_400
  linarith only [hU, hF]

theorem cell_bound_401 : cellBound ((1294864303869/3200000000000 : ℚ) : ℝ) ((13032360188949/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1294864303869/3200000000000 : ℝ) ≤ (-131728433012052986577/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_401 (by norm_num)
  have hUr : potential (13032360188949/32000000000000 : ℝ) ≤ (-131728433012052986577/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_402 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_401
  linarith only [hU, hF]

theorem cell_bound_402 : cellBound ((13032360188949/32000000000000 : ℚ) : ℝ) ((1639509667401/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (13032360188949/32000000000000 : ℝ) ≤ (-32785756952264584297/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_402 (by norm_num)
  have hUr : potential (1639509667401/4000000000000 : ℝ) ≤ (-32785756952264584297/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_403 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_402
  linarith only [hU, hF]

theorem cell_bound_403 : cellBound ((1639509667401/4000000000000 : ℚ) : ℝ) ((6641755819863/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1639509667401/4000000000000 : ℝ) ≤ (-25998731700465443147/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_403 (by norm_num)
  have hUr : potential (6641755819863/16000000000000 : ℝ) ≤ (-25998731700465443147/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_404 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_403
  linarith only [hU, hF]

theorem cell_bound_404 : cellBound ((6641755819863/16000000000000 : ℚ) : ℝ) ((3362736485061/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (6641755819863/16000000000000 : ℝ) ≤ (-8054448547503619819/6250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_404 (by norm_num)
  have hUr : potential (3362736485061/8000000000000 : ℝ) ≤ (-8054448547503619819/6250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_405 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_404
  linarith only [hU, hF]

theorem cell_bound_405 : cellBound ((3362736485061/8000000000000 : ℚ) : ℝ) ((6809190120381/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (3362736485061/8000000000000 : ℝ) ≤ (-127773793882587710957/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_405 (by norm_num)
  have hUr : potential (6809190120381/16000000000000 : ℝ) ≤ (-127773793882587710957/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_406 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_405
  linarith only [hU, hF]

theorem cell_bound_406 : cellBound ((6809190120381/16000000000000 : ℚ) : ℝ) ((86161340883/200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (6809190120381/16000000000000 : ℝ) ≤ (-63349977378847825983/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_406 (by norm_num)
  have hUr : potential (86161340883/200000000000 : ℝ) ≤ (-63349977378847825983/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_407 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_406
  linarith only [hU, hF]

theorem cell_bound_407 : cellBound ((86161340883/200000000000 : ℚ) : ℝ) ((54181913021/125000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (86161340883/200000000000 : ℝ) ≤ (-62464365819026938227/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_407 (by norm_num)
  have hUr : potential (54181913021/125000000000 : ℝ) ≤ (-62464365819026938227/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_408 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_407
  linarith only [hU, hF]

theorem cell_bound_408 : cellBound ((54181913021/125000000000 : ℚ) : ℝ) ((436103903921/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (54181913021/125000000000 : ℝ) ≤ (-123888943270306634623/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_408 (by norm_num)
  have hUr : potential (436103903921/1000000000000 : ℝ) ≤ (-123888943270306634623/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_409 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_408
  linarith only [hU, hF]

theorem cell_bound_409 : cellBound ((436103903921/1000000000000 : ℚ) : ℝ) ((219376251837/500000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (436103903921/1000000000000 : ℝ) ≤ (-61487223634067231353/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_409 (by norm_num)
  have hUr : potential (219376251837/500000000000 : ℝ) ≤ (-61487223634067231353/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_410 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_409
  linarith only [hU, hF]

theorem cell_bound_410 : cellBound ((219376251837/500000000000 : ℚ) : ℝ) ((880153607101/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (219376251837/500000000000 : ℝ) ≤ (-30636073454620462333/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_410 (by norm_num)
  have hUr : potential (880153607101/2000000000000 : ℝ) ≤ (-30636073454620462333/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_411 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_410
  linarith only [hU, hF]

theorem cell_bound_411 : cellBound ((880153607101/2000000000000 : ℚ) : ℝ) ((441401103427/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (880153607101/2000000000000 : ℝ) ≤ (-61063718690020233511/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_411 (by norm_num)
  have hUr : potential (441401103427/1000000000000 : ℝ) ≤ (-61063718690020233511/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_412 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_411
  linarith only [hU, hF]

theorem cell_bound_412 : cellBound ((441401103427/1000000000000 : ℚ) : ℝ) ((885450806607/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (441401103427/1000000000000 : ℝ) ≤ (-121721679958957971471/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_412 (by norm_num)
  have hUr : potential (885450806607/2000000000000 : ℝ) ≤ (-121721679958957971471/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_413 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_412
  linarith only [hU, hF]

theorem cell_bound_413 : cellBound ((885450806607/2000000000000 : ℚ) : ℝ) ((22202485159/50000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (885450806607/2000000000000 : ℝ) ≤ (-121325416150388901259/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_413 (by norm_num)
  have hUr : potential (22202485159/50000000000 : ℝ) ≤ (-121325416150388901259/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_414 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_413
  linarith only [hU, hF]

theorem cell_bound_414 : cellBound ((22202485159/50000000000 : ℚ) : ℝ) ((890748006113/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (22202485159/50000000000 : ℝ) ≤ (-12093742969142483103/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_414 (by norm_num)
  have hUr : potential (890748006113/2000000000000 : ℝ) ≤ (-12093742969142483103/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_415 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_414
  linarith only [hU, hF]

theorem cell_bound_415 : cellBound ((890748006113/2000000000000 : ℚ) : ℝ) ((446698302933/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (890748006113/2000000000000 : ℝ) ≤ (-120556771953482371347/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_415 (by norm_num)
  have hUr : potential (446698302933/1000000000000 : ℝ) ≤ (-120556771953482371347/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_416 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_415
  linarith only [hU, hF]

#print axioms cell_bound_415
end Zeta5AppendixNumerics
