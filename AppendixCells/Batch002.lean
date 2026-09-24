import AppendixCellBase
import AppendixField.Batch004
import AppendixField.Batch005
import AppendixNumericSpecial
import AppendixPotential.Batch004
import AppendixPotential.Batch005
import AppendixPotential.Batch006
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_32 : cellBound ((59205077/10000000000 : ℚ) : ℝ) ((59205079/10000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (59205077/10000000000 : ℝ) ≤ (-35853885368775070121/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_32 (by norm_num)
  have hUr : potential (59205079/10000000000 : ℝ) ≤ (-35853885368775070121/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_33 (by norm_num)
  have hU := max_le hUl hUr
  have hF := vstar_lower
  linarith only [hU, hF]

theorem cell_bound_33 : cellBound ((59205079/10000000000 : ℚ) : ℝ) ((8992695531/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (59205079/10000000000 : ℝ) ≤ (-35853885368775070121/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_33 (by norm_num)
  have hUr : potential (8992695531/1000000000000 : ℝ) ≤ (-35853885368775070121/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_34 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_33
  linarith only [hU, hF]

theorem cell_bound_34 : cellBound ((8992695531/1000000000000 : ℚ) : ℝ) ((19572466643/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (8992695531/1000000000000 : ℝ) ≤ (-35752570333635776921/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_34 (by norm_num)
  have hUr : potential (19572466643/2000000000000 : ℝ) ≤ (-35752570333635776921/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_35 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_34
  linarith only [hU, hF]

theorem cell_bound_35 : cellBound ((19572466643/2000000000000 : ℚ) : ℝ) ((40732008867/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (19572466643/2000000000000 : ℝ) ≤ (-35731207021943825891/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_35 (by norm_num)
  have hUr : potential (40732008867/4000000000000 : ℝ) ≤ (-35731207021943825891/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_36 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_35
  linarith only [hU, hF]

theorem cell_bound_36 : cellBound ((40732008867/4000000000000 : ℚ) : ℝ) ((1322471389/125000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (40732008867/4000000000000 : ℝ) ≤ (-71427521894559220797/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_36 (by norm_num)
  have hUr : potential (1322471389/125000000000 : ℝ) ≤ (-71427521894559220797/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_37 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_36
  linarith only [hU, hF]

theorem cell_bound_37 : cellBound ((1322471389/125000000000 : ℚ) : ℝ) ((4549323561/400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1322471389/125000000000 : ℝ) ≤ (-71371459507771400717/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_37 (by norm_num)
  have hUr : potential (4549323561/400000000000 : ℝ) ≤ (-71371459507771400717/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_38 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_37
  linarith only [hU, hF]

theorem cell_bound_38 : cellBound ((4549323561/400000000000 : ℚ) : ℝ) ((12166846693/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (4549323561/400000000000 : ℝ) ≤ (-35663331824515644831/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_38 (by norm_num)
  have hUr : potential (12166846693/1000000000000 : ℝ) ≤ (-35663331824515644831/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_39 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_38
  linarith only [hU, hF]

theorem cell_bound_39 : cellBound ((12166846693/1000000000000 : ℚ) : ℝ) ((3068199571/200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (12166846693/1000000000000 : ℝ) ≤ (-71202029435486253017/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_39 (by norm_num)
  have hUr : potential (3068199571/200000000000 : ℝ) ≤ (-71202029435486253017/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_40 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_39
  linarith only [hU, hF]

theorem cell_bound_40 : cellBound ((3068199571/200000000000 : ℚ) : ℝ) ((255845148549/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (3068199571/200000000000 : ℝ) ≤ (-283425812684169072343/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_40 (by norm_num)
  have hUr : potential (255845148549/16000000000000 : ℝ) ≤ (-283425812684169072343/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_41 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_40
  linarith only [hU, hF]

theorem cell_bound_41 : cellBound ((255845148549/16000000000000 : ℚ) : ℝ) ((133117165709/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (255845148549/16000000000000 : ℝ) ≤ (-70707001966488962787/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_41 (by norm_num)
  have hUr : potential (133117165709/8000000000000 : ℝ) ≤ (-70707001966488962787/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_42 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_41
  linarith only [hU, hF]

theorem cell_bound_42 : cellBound ((133117165709/8000000000000 : ℚ) : ℝ) ((108571569141/6400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (133117165709/8000000000000 : ℝ) ≤ (-2207700575134249039/781250000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_42 (by norm_num)
  have hUr : potential (108571569141/6400000000000 : ℝ) ≤ (-2207700575134249039/781250000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_43 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_42
  linarith only [hU, hF]

theorem cell_bound_43 : cellBound ((108571569141/6400000000000 : ℚ) : ℝ) ((276623514287/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (108571569141/6400000000000 : ℝ) ≤ (-35295812484256536473/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_43 (by norm_num)
  have hUr : potential (276623514287/16000000000000 : ℝ) ≤ (-35295812484256536473/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_44 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_43
  linarith only [hU, hF]

theorem cell_bound_44 : cellBound ((276623514287/16000000000000 : ℚ) : ℝ) ((563636211443/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (276623514287/16000000000000 : ℝ) ≤ (-282165177970172069769/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_44 (by norm_num)
  have hUr : potential (563636211443/32000000000000 : ℝ) ≤ (-282165177970172069769/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_45 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_44
  linarith only [hU, hF]

theorem cell_bound_45 : cellBound ((563636211443/32000000000000 : ℚ) : ℝ) ((71753174289/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (563636211443/32000000000000 : ℝ) ≤ (-281978213757091417579/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_45 (by norm_num)
  have hUr : potential (71753174289/4000000000000 : ℝ) ≤ (-281978213757091417579/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_46 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_45
  linarith only [hU, hF]

theorem cell_bound_46 : cellBound ((71753174289/4000000000000 : ℚ) : ℝ) ((584414577181/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (71753174289/4000000000000 : ℝ) ≤ (-70450788662467682973/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_46 (by norm_num)
  have hUr : potential (584414577181/32000000000000 : ℝ) ≤ (-70450788662467682973/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_47 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_46
  linarith only [hU, hF]

theorem cell_bound_47 : cellBound ((584414577181/32000000000000 : ℚ) : ℝ) ((11896075201/640000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (584414577181/32000000000000 : ℝ) ≤ (-70409548977118410071/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_47 (by norm_num)
  have hUr : potential (11896075201/640000000000 : ℝ) ≤ (-70409548977118410071/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_48 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_47
  linarith only [hU, hF]

#print axioms cell_bound_47
end Zeta5AppendixNumerics
