import AppendixCellBase
import AppendixField.Batch000
import AppendixField.Batch001
import AppendixPotential.Batch000
import AppendixPotential.Batch001
import AppendixPotential.Batch002
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_0 : cellBound ((0/1 : ℚ) : ℝ) ((7174131/200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (0/1 : ℝ) ≤ (-68464141558273799123/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_0 (by norm_num)
  have hUr : potential (7174131/200000000000 : ℝ) ≤ (-68464141558273799123/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_1 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_1
  linarith only [hU, hF]

theorem cell_bound_1 : cellBound ((7174131/200000000000 : ℚ) : ℝ) ((21522393/400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (7174131/200000000000 : ℝ) ≤ (-8574738884247421353/3125000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_1 (by norm_num)
  have hUr : potential (21522393/400000000000 : ℝ) ≤ (-8574738884247421353/3125000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_2 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_2
  linarith only [hU, hF]

theorem cell_bound_2 : cellBound ((21522393/400000000000 : ℚ) : ℝ) ((7174131/100000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (21522393/400000000000 : ℝ) ≤ (-274692133157718167743/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_2 (by norm_num)
  have hUr : potential (7174131/100000000000 : ℝ) ≤ (-274692133157718167743/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_3 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_3
  linarith only [hU, hF]

theorem cell_bound_3 : cellBound ((7174131/100000000000 : ℚ) : ℝ) ((14825913/200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (7174131/100000000000 : ℝ) ≤ (-55008365314657841999/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_3 (by norm_num)
  have hUr : potential (14825913/200000000000 : ℝ) ≤ (-55008365314657841999/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_4 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_4
  linarith only [hU, hF]

theorem cell_bound_4 : cellBound ((14825913/200000000000 : ℚ) : ℝ) ((78667711/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (14825913/200000000000 : ℝ) ≤ (-68775319218261872217/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_4 (by norm_num)
  have hUr : potential (78667711/1000000000000 : ℝ) ≤ (-68775319218261872217/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_5 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_5
  linarith only [hU, hF]

theorem cell_bound_5 : cellBound ((78667711/1000000000000 : ℚ) : ℝ) ((85815639/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (78667711/1000000000000 : ℝ) ≤ (-275209485763087801601/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_5 (by norm_num)
  have hUr : potential (85815639/1000000000000 : ℝ) ≤ (-275209485763087801601/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_6 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_6
  linarith only [hU, hF]

theorem cell_bound_6 : cellBound ((85815639/1000000000000 : ℚ) : ℝ) ((19269871/200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (85815639/1000000000000 : ℝ) ≤ (-275372563466201784051/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_6 (by norm_num)
  have hUr : potential (19269871/200000000000 : ℝ) ≤ (-275372563466201784051/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_7 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_7
  linarith only [hU, hF]

theorem cell_bound_7 : cellBound ((19269871/200000000000 : ℚ) : ℝ) ((55761057/500000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (19269871/200000000000 : ℝ) ≤ (-27559828323998540637/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_7 (by norm_num)
  have hUr : potential (55761057/500000000000 : ℝ) ≤ (-27559828323998540637/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_8 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_8
  linarith only [hU, hF]

theorem cell_bound_8 : cellBound ((55761057/500000000000 : ℚ) : ℝ) ((33336783/250000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (55761057/500000000000 : ℝ) ≤ (-68974551508954592789/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_8 (by norm_num)
  have hUr : potential (33336783/250000000000 : ℝ) ≤ (-68974551508954592789/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_9 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_9
  linarith only [hU, hF]

theorem cell_bound_9 : cellBound ((33336783/250000000000 : ℚ) : ℝ) ((82548843/500000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (33336783/250000000000 : ℝ) ≤ (-276289594008561079549/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_9 (by norm_num)
  have hUr : potential (82548843/500000000000 : ℝ) ≤ (-276289594008561079549/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_10 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_10
  linarith only [hU, hF]

theorem cell_bound_10 : cellBound ((82548843/500000000000 : ℚ) : ℝ) ((53051547/250000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (82548843/500000000000 : ℝ) ≤ (-69198413673467443243/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_10 (by norm_num)
  have hUr : potential (53051547/250000000000 : ℝ) ≤ (-69198413673467443243/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_11 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_11
  linarith only [hU, hF]

theorem cell_bound_11 : cellBound ((53051547/250000000000 : ℚ) : ℝ) ((496117379/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (53051547/250000000000 : ℝ) ≤ (-277439850304707987667/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_11 (by norm_num)
  have hUr : potential (496117379/2000000000000 : ℝ) ≤ (-277439850304707987667/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_12 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_12
  linarith only [hU, hF]

theorem cell_bound_12 : cellBound ((496117379/2000000000000 : ℚ) : ℝ) ((283911191/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (496117379/2000000000000 : ℝ) ≤ (-277765955255403291529/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_12 (by norm_num)
  have hUr : potential (283911191/1000000000000 : ℝ) ≤ (-277765955255403291529/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_13 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_13
  linarith only [hU, hF]

theorem cell_bound_13 : cellBound ((283911191/1000000000000 : ℚ) : ℝ) ((170058951/500000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (283911191/1000000000000 : ℝ) ≤ (-278262783385883433301/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_13 (by norm_num)
  have hUr : potential (170058951/500000000000 : ℝ) ≤ (-278262783385883433301/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_14 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_14
  linarith only [hU, hF]

theorem cell_bound_14 : cellBound ((170058951/500000000000 : ℚ) : ℝ) ((396324613/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (170058951/500000000000 : ℝ) ≤ (-139332618727948692437/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_14 (by norm_num)
  have hUr : potential (396324613/1000000000000 : ℝ) ≤ (-139332618727948692437/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_15 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_15
  linarith only [hU, hF]

theorem cell_bound_15 : cellBound ((396324613/1000000000000 : ℚ) : ℝ) ((974522519/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (396324613/1000000000000 : ℝ) ≤ (-279305182137134784209/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_15 (by norm_num)
  have hUr : potential (974522519/2000000000000 : ℝ) ≤ (-279305182137134784209/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_16 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_16
  linarith only [hU, hF]

#print axioms cell_bound_15
end Zeta5AppendixNumerics
