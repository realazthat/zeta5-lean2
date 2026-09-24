import AppendixCellBase
import AppendixField.Batch023
import AppendixField.Batch024
import AppendixField.Batch025
import AppendixPotential.Batch024
import AppendixPotential.Batch025
import AppendixPotential.Batch026
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_192 : cellBound ((4675203313927/32000000000000 : ℚ) : ℝ) ((2365991674599/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (4675203313927/32000000000000 : ℝ) ≤ (-108351765300096517701/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_192 (by norm_num)
  have hUr : potential (2365991674599/16000000000000 : ℝ) ≤ (-108351765300096517701/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_193 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_192
  linarith only [hU, hF]

theorem cell_bound_193 : cellBound ((2365991674599/16000000000000 : ℚ) : ℝ) ((4788763384469/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2365991674599/16000000000000 : ℝ) ≤ (-215650334507742007369/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_193 (by norm_num)
  have hUr : potential (4788763384469/32000000000000 : ℝ) ≤ (-215650334507742007369/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_194 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_193
  linarith only [hU, hF]

theorem cell_bound_194 : cellBound ((4788763384469/32000000000000 : ℚ) : ℝ) ((9634306804209/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (4788763384469/32000000000000 : ℝ) ≤ (-215165357004839604619/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_194 (by norm_num)
  have hUr : potential (9634306804209/64000000000000 : ℝ) ≤ (-215165357004839604619/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_195 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_194
  linarith only [hU, hF]

theorem cell_bound_195 : cellBound ((9634306804209/64000000000000 : ℚ) : ℝ) ((242277170987/1600000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (9634306804209/64000000000000 : ℝ) ≤ (-214700826818163375437/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_195 (by norm_num)
  have hUr : potential (242277170987/1600000000000 : ℝ) ≤ (-214700826818163375437/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_196 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_195
  linarith only [hU, hF]

theorem cell_bound_196 : cellBound ((242277170987/1600000000000 : ℚ) : ℝ) ((9747866874751/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (242277170987/1600000000000 : ℝ) ≤ (-21425337025435109587/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_196 (by norm_num)
  have hUr : potential (9747866874751/64000000000000 : ℝ) ≤ (-21425337025435109587/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_197 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_196
  linarith only [hU, hF]

theorem cell_bound_197 : cellBound ((9747866874751/64000000000000 : ℚ) : ℝ) ((4902323455011/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (9747866874751/64000000000000 : ℝ) ≤ (-53455129600806697663/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_197 (by norm_num)
  have hUr : potential (4902323455011/32000000000000 : ℝ) ≤ (-53455129600806697663/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_198 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_197
  linarith only [hU, hF]

theorem cell_bound_198 : cellBound ((4902323455011/32000000000000 : ℚ) : ℝ) ((9861426945293/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (4902323455011/32000000000000 : ℝ) ≤ (-213400397197492203977/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_198 (by norm_num)
  have hUr : potential (9861426945293/64000000000000 : ℝ) ≤ (-213400397197492203977/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_199 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_198
  linarith only [hU, hF]

theorem cell_bound_199 : cellBound ((9861426945293/64000000000000 : ℚ) : ℝ) ((2479551745141/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (9861426945293/64000000000000 : ℝ) ≤ (-53247885496898506491/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_199 (by norm_num)
  have hUr : potential (2479551745141/16000000000000 : ℝ) ≤ (-53247885496898506491/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_200 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_199
  linarith only [hU, hF]

theorem cell_bound_200 : cellBound ((2479551745141/16000000000000 : ℚ) : ℝ) ((19893193996399/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2479551745141/16000000000000 : ℝ) ≤ (-106395481811887639113/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_200 (by norm_num)
  have hUr : potential (19893193996399/128000000000000 : ℝ) ≤ (-106395481811887639113/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_201 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_200
  linarith only [hU, hF]

theorem cell_bound_201 : cellBound ((19893193996399/128000000000000 : ℚ) : ℝ) ((1994997403167/12800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (19893193996399/128000000000000 : ℝ) ≤ (-212592780296548598167/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_201 (by norm_num)
  have hUr : potential (1994997403167/12800000000000 : ℝ) ≤ (-212592780296548598167/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_202 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_201
  linarith only [hU, hF]

theorem cell_bound_202 : cellBound ((1994997403167/12800000000000 : ℚ) : ℝ) ((20006754066941/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1994997403167/12800000000000 : ℝ) ≤ (-212396878567840040743/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_202 (by norm_num)
  have hUr : potential (20006754066941/128000000000000 : ℝ) ≤ (-212396878567840040743/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_203 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_202
  linarith only [hU, hF]

theorem cell_bound_203 : cellBound ((20006754066941/128000000000000 : ℚ) : ℝ) ((5015883525553/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (20006754066941/128000000000000 : ℝ) ≤ (-21220315507978818519/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_203 (by norm_num)
  have hUr : potential (5015883525553/32000000000000 : ℝ) ≤ (-21220315507978818519/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_204 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_203
  linarith only [hU, hF]

theorem cell_bound_204 : cellBound ((5015883525553/32000000000000 : ℚ) : ℝ) ((20120314137483/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (5015883525553/32000000000000 : ℝ) ≤ (-212011514933354143337/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_204 (by norm_num)
  have hUr : potential (20120314137483/128000000000000 : ℝ) ≤ (-212011514933354143337/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_205 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_204
  linarith only [hU, hF]

theorem cell_bound_205 : cellBound ((20120314137483/128000000000000 : ℚ) : ℝ) ((10088547086377/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (20120314137483/128000000000000 : ℝ) ≤ (-6619433484097332699/3125000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_205 (by norm_num)
  have hUr : potential (10088547086377/64000000000000 : ℝ) ≤ (-6619433484097332699/3125000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_206 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_205
  linarith only [hU, hF]

theorem cell_bound_206 : cellBound ((10088547086377/64000000000000 : ℚ) : ℝ) ((809354968321/5120000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (10088547086377/64000000000000 : ℝ) ≤ (-52908536144419670629/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_206 (by norm_num)
  have hUr : potential (809354968321/5120000000000 : ℝ) ≤ (-52908536144419670629/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_207 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_206
  linarith only [hU, hF]

theorem cell_bound_207 : cellBound ((809354968321/5120000000000 : ℚ) : ℝ) ((634082945103/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (809354968321/5120000000000 : ℝ) ≤ (-4228965210229871721/2000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_207 (by norm_num)
  have hUr : potential (634082945103/4000000000000 : ℝ) ≤ (-4228965210229871721/2000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_208 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_207
  linarith only [hU, hF]

#print axioms cell_bound_207
end Zeta5AppendixNumerics
