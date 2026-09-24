import AppendixCellBase
import AppendixField.Batch015
import AppendixField.Batch016
import AppendixField.Batch017
import AppendixPotential.Batch016
import AppendixPotential.Batch017
import AppendixPotential.Batch018
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_128 : cellBound ((1221767174613/16000000000000 : ℚ) : ℝ) ((4920698646773/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1221767174613/16000000000000 : ℝ) ≤ (-248495223864978324943/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_128 (by norm_num)
  have hUr : potential (4920698646773/64000000000000 : ℝ) ≤ (-248495223864978324943/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_129 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_128
  linarith only [hU, hF]

theorem cell_bound_129 : cellBound ((4920698646773/64000000000000 : ℚ) : ℝ) ((2477164297547/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (4920698646773/64000000000000 : ℝ) ≤ (-31030766848978955211/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_129 (by norm_num)
  have hUr : potential (2477164297547/32000000000000 : ℝ) ≤ (-31030766848978955211/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_130 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_129
  linarith only [hU, hF]

theorem cell_bound_130 : cellBound ((2477164297547/32000000000000 : ℚ) : ℝ) ((997591708683/12800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2477164297547/32000000000000 : ℝ) ≤ (-248001406673303942621/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_130 (by norm_num)
  have hUr : potential (997591708683/12800000000000 : ℝ) ≤ (-248001406673303942621/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_131 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_130
  linarith only [hU, hF]

theorem cell_bound_131 : cellBound ((997591708683/12800000000000 : ℚ) : ℝ) ((627698561467/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (997591708683/12800000000000 : ℝ) ≤ (-247760815408205250181/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_131 (by norm_num)
  have hUr : potential (627698561467/8000000000000 : ℝ) ≤ (-247760815408205250181/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_132 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_131
  linarith only [hU, hF]

theorem cell_bound_132 : cellBound ((627698561467/8000000000000 : ℚ) : ℝ) ((5055218440057/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (627698561467/8000000000000 : ℝ) ≤ (-154702598807675231/62500000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_132 (by norm_num)
  have hUr : potential (5055218440057/64000000000000 : ℝ) ≤ (-154702598807675231/62500000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_133 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_132
  linarith only [hU, hF]

theorem cell_bound_133 : cellBound ((5055218440057/64000000000000 : ℚ) : ℝ) ((2544424194189/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (5055218440057/64000000000000 : ℝ) ≤ (-247291250232214341959/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_133 (by norm_num)
  have hUr : potential (2544424194189/32000000000000 : ℝ) ≤ (-247291250232214341959/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_134 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_133
  linarith only [hU, hF]

theorem cell_bound_134 : cellBound ((2544424194189/32000000000000 : ℚ) : ℝ) ((5122478336699/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2544424194189/32000000000000 : ℝ) ≤ (-247061923048060036579/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_134 (by norm_num)
  have hUr : potential (5122478336699/64000000000000 : ℝ) ≤ (-247061923048060036579/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_135 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_134
  linarith only [hU, hF]

theorem cell_bound_135 : cellBound ((5122478336699/64000000000000 : ℚ) : ℝ) ((257805414251/3200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (5122478336699/64000000000000 : ℝ) ≤ (-771362568411207537/312500000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_135 (by norm_num)
  have hUr : potential (257805414251/3200000000000 : ℝ) ≤ (-771362568411207537/312500000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_136 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_135
  linarith only [hU, hF]

theorem cell_bound_136 : cellBound ((257805414251/3200000000000 : ℚ) : ℝ) ((2611684090831/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (257805414251/3200000000000 : ℝ) ≤ (-123196969547776496793/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_136 (by norm_num)
  have hUr : potential (2611684090831/32000000000000 : ℝ) ≤ (-123196969547776496793/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_137 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_136
  linarith only [hU, hF]

theorem cell_bound_137 : cellBound ((2611684090831/32000000000000 : ℚ) : ℝ) ((165332127447/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2611684090831/32000000000000 : ℝ) ≤ (-61490996662670670009/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_137 (by norm_num)
  have hUr : potential (165332127447/2000000000000 : ℝ) ≤ (-61490996662670670009/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_138 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_137
  linarith only [hU, hF]

theorem cell_bound_138 : cellBound ((165332127447/2000000000000 : ℚ) : ℝ) ((2678943987473/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (165332127447/2000000000000 : ℝ) ≤ (-24554528841353024477/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_138 (by norm_num)
  have hUr : potential (2678943987473/32000000000000 : ℝ) ≤ (-24554528841353024477/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_139 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_138
  linarith only [hU, hF]

theorem cell_bound_139 : cellBound ((2678943987473/32000000000000 : ℚ) : ℝ) ((1356286967897/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2678943987473/32000000000000 : ℝ) ≤ (-49027416189847128967/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_139 (by norm_num)
  have hUr : potential (1356286967897/16000000000000 : ℝ) ≤ (-49027416189847128967/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_140 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_139
  linarith only [hU, hF]

theorem cell_bound_140 : cellBound ((1356286967897/16000000000000 : ℚ) : ℝ) ((694958458109/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1356286967897/16000000000000 : ℝ) ≤ (-244349528249046460837/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_140 (by norm_num)
  have hUr : potential (694958458109/8000000000000 : ℝ) ≤ (-244349528249046460837/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_141 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_140
  linarith only [hU, hF]

theorem cell_bound_141 : cellBound ((694958458109/8000000000000 : ℚ) : ℝ) ((1423546864539/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (694958458109/8000000000000 : ℝ) ≤ (-30449599719236789023/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_141 (by norm_num)
  have hUr : potential (1423546864539/16000000000000 : ℝ) ≤ (-30449599719236789023/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_142 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_141
  linarith only [hU, hF]

theorem cell_bound_142 : cellBound ((1423546864539/16000000000000 : ℚ) : ℝ) ((72858840643/800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1423546864539/16000000000000 : ℝ) ≤ (-48575047439270053729/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_142 (by norm_num)
  have hUr : potential (72858840643/800000000000 : ℝ) ≤ (-48575047439270053729/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_143 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_142
  linarith only [hU, hF]

theorem cell_bound_143 : cellBound ((72858840643/800000000000 : ℚ) : ℝ) ((762218354751/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (72858840643/800000000000 : ℝ) ≤ (-60378518825469251233/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_143 (by norm_num)
  have hUr : potential (762218354751/8000000000000 : ℝ) ≤ (-60378518825469251233/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_144 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_143
  linarith only [hU, hF]

#print axioms cell_bound_143
end Zeta5AppendixNumerics
