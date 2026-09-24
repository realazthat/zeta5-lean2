import AppendixCellBase
import AppendixField.Batch013
import AppendixField.Batch014
import AppendixField.Batch015
import AppendixPotential.Batch014
import AppendixPotential.Batch015
import AppendixPotential.Batch016
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_112 : cellBound ((4517139266921/64000000000000 : ℚ) : ℝ) ((2275384607621/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (4517139266921/64000000000000 : ℝ) ≤ (-251624880261940289059/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_112 (by norm_num)
  have hUr : potential (2275384607621/32000000000000 : ℝ) ≤ (-251624880261940289059/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_113 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_112
  linarith only [hU, hF]

theorem cell_bound_113 : cellBound ((2275384607621/32000000000000 : ℚ) : ℝ) ((4584399163563/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2275384607621/32000000000000 : ℝ) ≤ (-31412600760500411463/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_113 (by norm_num)
  have hUr : potential (4584399163563/64000000000000 : ℝ) ≤ (-31412600760500411463/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_114 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_113
  linarith only [hU, hF]

theorem cell_bound_114 : cellBound ((4584399163563/64000000000000 : ℚ) : ℝ) ((1154507277971/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (4584399163563/64000000000000 : ℝ) ≤ (-125493522133894421147/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_114 (by norm_num)
  have hUr : potential (1154507277971/16000000000000 : ℝ) ≤ (-125493522133894421147/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_115 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_114
  linarith only [hU, hF]

theorem cell_bound_115 : cellBound ((1154507277971/16000000000000 : ℚ) : ℝ) ((930331812041/12800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1154507277971/16000000000000 : ℝ) ≤ (-250682498181097561513/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_115 (by norm_num)
  have hUr : potential (930331812041/12800000000000 : ℝ) ≤ (-250682498181097561513/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_116 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_115
  linarith only [hU, hF]

theorem cell_bound_116 : cellBound ((930331812041/12800000000000 : ℚ) : ℝ) ((2342644504263/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (930331812041/12800000000000 : ℝ) ≤ (-7824570989493812283/3125000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_116 (by norm_num)
  have hUr : potential (2342644504263/32000000000000 : ℝ) ≤ (-7824570989493812283/3125000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_117 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_116
  linarith only [hU, hF]

theorem cell_bound_117 : cellBound ((2342644504263/32000000000000 : ℚ) : ℝ) ((9404207965373/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2342644504263/32000000000000 : ℝ) ≤ (-125120520405917488217/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_117 (by norm_num)
  have hUr : potential (9404207965373/128000000000000 : ℝ) ≤ (-125120520405917488217/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_118 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_117
  linarith only [hU, hF]

theorem cell_bound_118 : cellBound ((9404207965373/128000000000000 : ℚ) : ℝ) ((4718918956847/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (9404207965373/128000000000000 : ℝ) ≤ (-125048810322265713771/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_118 (by norm_num)
  have hUr : potential (4718918956847/64000000000000 : ℝ) ≤ (-125048810322265713771/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_119 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_118
  linarith only [hU, hF]

theorem cell_bound_119 : cellBound ((4718918956847/64000000000000 : ℚ) : ℝ) ((1894293572403/25600000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (4718918956847/64000000000000 : ℝ) ≤ (-1249779680858776899/500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_119 (by norm_num)
  have hUr : potential (1894293572403/25600000000000 : ℝ) ≤ (-1249779680858776899/500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_120 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_119
  linarith only [hU, hF]

theorem cell_bound_120 : cellBound ((1894293572403/25600000000000 : ℚ) : ℝ) ((297034306573/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1894293572403/25600000000000 : ℝ) ≤ (-249815918109864422171/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_120 (by norm_num)
  have hUr : potential (297034306573/4000000000000 : ℝ) ≤ (-249815918109864422171/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_121 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_120
  linarith only [hU, hF]

theorem cell_bound_121 : cellBound ((297034306573/4000000000000 : ℚ) : ℝ) ((9538727758657/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (297034306573/4000000000000 : ℝ) ≤ (-243825685979437263/97656250000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_121 (by norm_num)
  have hUr : potential (9538727758657/128000000000000 : ℝ) ≤ (-243825685979437263/97656250000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_122 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_121
  linarith only [hU, hF]

theorem cell_bound_122 : cellBound ((9538727758657/128000000000000 : ℚ) : ℝ) ((4786178853489/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (9538727758657/128000000000000 : ℝ) ≤ (-249540629376702671897/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_122 (by norm_num)
  have hUr : potential (4786178853489/64000000000000 : ℝ) ≤ (-249540629376702671897/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_123 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_122
  linarith only [hU, hF]

theorem cell_bound_123 : cellBound ((4786178853489/64000000000000 : ℚ) : ℝ) ((9605987655299/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (4786178853489/64000000000000 : ℝ) ≤ (-124702621804777156837/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_123 (by norm_num)
  have hUr : potential (9605987655299/128000000000000 : ℝ) ≤ (-124702621804777156837/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_124 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_123
  linarith only [hU, hF]

theorem cell_bound_124 : cellBound ((9605987655299/128000000000000 : ℚ) : ℝ) ((481980880181/6400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (9605987655299/128000000000000 : ℝ) ≤ (-486857994821506521/195312500000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_124 (by norm_num)
  have hUr : potential (481980880181/6400000000000 : ℝ) ≤ (-486857994821506521/195312500000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_125 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_124
  linarith only [hU, hF]

theorem cell_bound_125 : cellBound ((481980880181/6400000000000 : ℚ) : ℝ) ((9673247551941/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (481980880181/6400000000000 : ℝ) ≤ (-31142341251932608577/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_125 (by norm_num)
  have hUr : potential (9673247551941/128000000000000 : ℝ) ≤ (-31142341251932608577/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_126 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_125
  linarith only [hU, hF]

theorem cell_bound_126 : cellBound ((9673247551941/128000000000000 : ℚ) : ℝ) ((4853438750131/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (9673247551941/128000000000000 : ℝ) ≤ (-249007508550402279723/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_126 (by norm_num)
  have hUr : potential (4853438750131/64000000000000 : ℝ) ≤ (-249007508550402279723/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_127 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_126
  linarith only [hU, hF]

theorem cell_bound_127 : cellBound ((4853438750131/64000000000000 : ℚ) : ℝ) ((1221767174613/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (4853438750131/64000000000000 : ℝ) ≤ (-12437446127121252131/5000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_127 (by norm_num)
  have hUr : potential (1221767174613/16000000000000 : ℝ) ≤ (-12437446127121252131/5000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_128 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_127
  linarith only [hU, hF]

#print axioms cell_bound_127
end Zeta5AppendixNumerics
