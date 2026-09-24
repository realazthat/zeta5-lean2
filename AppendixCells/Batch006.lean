import AppendixCellBase
import AppendixField.Batch011
import AppendixField.Batch012
import AppendixField.Batch013
import AppendixPotential.Batch012
import AppendixPotential.Batch013
import AppendixPotential.Batch014
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_96 : cellBound ((646573553607/12800000000000 : ℚ) : ℝ) ((407101159919/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (646573553607/12800000000000 : ℝ) ≤ (-65659580772353539647/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_96 (by norm_num)
  have hUr : potential (407101159919/8000000000000 : ℝ) ≤ (-65659580772353539647/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_97 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_96
  linarith only [hU, hF]

theorem cell_bound_97 : cellBound ((407101159919/8000000000000 : ℚ) : ℝ) ((1652346150993/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (407101159919/8000000000000 : ℝ) ≤ (-131138725467913094251/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_97 (by norm_num)
  have hUr : potential (1652346150993/32000000000000 : ℝ) ≤ (-131138725467913094251/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_98 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_97
  linarith only [hU, hF]

theorem cell_bound_98 : cellBound ((1652346150993/32000000000000 : ℚ) : ℝ) ((167628766231/3200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1652346150993/32000000000000 : ℝ) ≤ (-65482187363802643949/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_98 (by norm_num)
  have hUr : potential (167628766231/3200000000000 : ℝ) ≤ (-65482187363802643949/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_99 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_98
  linarith only [hU, hF]

theorem cell_bound_99 : cellBound ((167628766231/3200000000000 : ℚ) : ℝ) ((1700229173627/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (167628766231/3200000000000 : ℝ) ≤ (-130795580588340684277/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_99 (by norm_num)
  have hUr : potential (1700229173627/32000000000000 : ℝ) ≤ (-130795580588340684277/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_100 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_99
  linarith only [hU, hF]

theorem cell_bound_100 : cellBound ((1700229173627/32000000000000 : ℚ) : ℝ) ((107760667809/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1700229173627/32000000000000 : ℝ) ≤ (-130631893280052577271/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_100 (by norm_num)
  have hUr : potential (107760667809/2000000000000 : ℝ) ≤ (-130631893280052577271/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_101 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_100
  linarith only [hU, hF]

theorem cell_bound_101 : cellBound ((107760667809/2000000000000 : ℚ) : ℝ) ((886026853789/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (107760667809/2000000000000 : ℝ) ≤ (-52127336480584724941/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_101 (by norm_num)
  have hUr : potential (886026853789/16000000000000 : ℝ) ≤ (-52127336480584724941/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_102 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_101
  linarith only [hU, hF]

theorem cell_bound_102 : cellBound ((886026853789/16000000000000 : ℚ) : ℝ) ((454984182553/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (886026853789/16000000000000 : ℝ) ≤ (-52008469484842783913/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_102 (by norm_num)
  have hUr : potential (454984182553/8000000000000 : ℝ) ≤ (-52008469484842783913/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_103 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_102
  linarith only [hU, hF]

theorem cell_bound_103 : cellBound ((454984182553/8000000000000 : ℚ) : ℝ) ((47892569387/800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (454984182553/8000000000000 : ℝ) ≤ (-258936880167634030823/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_103 (by norm_num)
  have hUr : potential (47892569387/800000000000 : ℝ) ≤ (-258936880167634030823/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_104 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_103
  linarith only [hU, hF]

theorem cell_bound_104 : cellBound ((47892569387/800000000000 : ℚ) : ℝ) ((502867205187/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (47892569387/800000000000 : ℝ) ≤ (-32240479457964304007/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_104 (by norm_num)
  have hUr : potential (502867205187/8000000000000 : ℝ) ≤ (-32240479457964304007/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_105 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_104
  linarith only [hU, hF]

theorem cell_bound_105 : cellBound ((502867205187/8000000000000 : ℚ) : ℝ) ((65851089563/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (502867205187/8000000000000 : ℝ) ≤ (-256986944007423015351/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_105 (by norm_num)
  have hUr : potential (65851089563/1000000000000 : ℝ) ≤ (-256986944007423015351/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_106 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_105
  linarith only [hU, hF]

theorem cell_bound_106 : cellBound ((65851089563/1000000000000 : ℚ) : ℝ) ((2140864814337/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (65851089563/1000000000000 : ℝ) ≤ (-25492634944567365961/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_106 (by norm_num)
  have hUr : potential (2140864814337/32000000000000 : ℝ) ≤ (-25492634944567365961/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_107 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_106
  linarith only [hU, hF]

theorem cell_bound_107 : cellBound ((2140864814337/32000000000000 : ℚ) : ℝ) ((1087247381329/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2140864814337/32000000000000 : ℝ) ≤ (-63475827445435829939/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_107 (by norm_num)
  have hUr : potential (1087247381329/16000000000000 : ℝ) ≤ (-63475827445435829939/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_108 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_107
  linarith only [hU, hF]

theorem cell_bound_108 : cellBound ((1087247381329/16000000000000 : ℚ) : ℝ) ((2208124710979/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1087247381329/16000000000000 : ℝ) ≤ (-253058576297634968471/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_108 (by norm_num)
  have hUr : potential (2208124710979/32000000000000 : ℝ) ≤ (-253058576297634968471/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_109 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_108
  linarith only [hU, hF]

theorem cell_bound_109 : cellBound ((2208124710979/32000000000000 : ℚ) : ℝ) ((4449879370279/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2208124710979/32000000000000 : ℝ) ≤ (-252674756981933066689/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_109 (by norm_num)
  have hUr : potential (4449879370279/64000000000000 : ℝ) ≤ (-252674756981933066689/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_110 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_109
  linarith only [hU, hF]

theorem cell_bound_110 : cellBound ((4449879370279/64000000000000 : ℚ) : ℝ) ((22417546593/320000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (4449879370279/64000000000000 : ℝ) ≤ (-252309826956255674213/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_110 (by norm_num)
  have hUr : potential (22417546593/320000000000 : ℝ) ≤ (-252309826956255674213/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_111 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_110
  linarith only [hU, hF]

theorem cell_bound_111 : cellBound ((22417546593/320000000000 : ℚ) : ℝ) ((4517139266921/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (22417546593/320000000000 : ℝ) ≤ (-31495079594033890791/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_111 (by norm_num)
  have hUr : potential (4517139266921/64000000000000 : ℝ) ≤ (-31495079594033890791/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_112 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_111
  linarith only [hU, hF]

#print axioms cell_bound_111
end Zeta5AppendixNumerics
