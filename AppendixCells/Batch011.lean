import AppendixCellBase
import AppendixField.Batch021
import AppendixField.Batch022
import AppendixField.Batch023
import AppendixPotential.Batch022
import AppendixPotential.Batch023
import AppendixPotential.Batch024
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_176 : cellBound ((465191185897/4000000000000 : ℚ) : ℝ) ((3743951831963/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (465191185897/4000000000000 : ℝ) ≤ (-45854418287828764797/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_176 (by norm_num)
  have hUr : potential (3743951831963/32000000000000 : ℝ) ≤ (-45854418287828764797/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_177 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_176
  linarith only [hU, hF]

theorem cell_bound_177 : cellBound ((3743951831963/32000000000000 : ℚ) : ℝ) ((15065496707/128000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (3743951831963/32000000000000 : ℝ) ≤ (-228990396613534358313/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_177 (by norm_num)
  have hUr : potential (15065496707/128000000000 : ℝ) ≤ (-228990396613534358313/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_178 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_177
  linarith only [hU, hF]

theorem cell_bound_178 : cellBound ((15065496707/128000000000 : ℚ) : ℝ) ((3788796521537/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (15065496707/128000000000 : ℝ) ≤ (-28589082202573929489/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_178 (by norm_num)
  have hUr : potential (3788796521537/32000000000000 : ℝ) ≤ (-28589082202573929489/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_179 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_178
  linarith only [hU, hF]

theorem cell_bound_179 : cellBound ((3788796521537/32000000000000 : ℚ) : ℝ) ((952804716581/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (3788796521537/32000000000000 : ℝ) ≤ (-45687741812758166617/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_179 (by norm_num)
  have hUr : potential (952804716581/8000000000000 : ℝ) ≤ (-45687741812758166617/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_180 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_179
  linarith only [hU, hF]

theorem cell_bound_180 : cellBound ((952804716581/8000000000000 : ℚ) : ℝ) ((3833641211111/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (952804716581/8000000000000 : ℝ) ≤ (-45633679798467016877/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_180 (by norm_num)
  have hUr : potential (3833641211111/32000000000000 : ℝ) ≤ (-45633679798467016877/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_181 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_180
  linarith only [hU, hF]

theorem cell_bound_181 : cellBound ((3833641211111/32000000000000 : ℚ) : ℝ) ((1928031777949/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (3833641211111/32000000000000 : ℝ) ≤ (-56975396646352209089/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_181 (by norm_num)
  have hUr : potential (1928031777949/16000000000000 : ℝ) ≤ (-56975396646352209089/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_182 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_181
  linarith only [hU, hF]

theorem cell_bound_182 : cellBound ((1928031777949/16000000000000 : ℚ) : ℝ) ((121903382671/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1928031777949/16000000000000 : ℝ) ≤ (-113688971443943523879/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_182 (by norm_num)
  have hUr : potential (121903382671/1000000000000 : ℝ) ≤ (-113688971443943523879/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_183 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_182
  linarith only [hU, hF]

theorem cell_bound_183 : cellBound ((121903382671/1000000000000 : ℚ) : ℝ) ((1972876467523/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (121903382671/1000000000000 : ℝ) ≤ (-45373368050891882111/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_183 (by norm_num)
  have hUr : potential (1972876467523/16000000000000 : ℝ) ≤ (-45373368050891882111/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_184 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_183
  linarith only [hU, hF]

theorem cell_bound_184 : cellBound ((1972876467523/16000000000000 : ℚ) : ℝ) ((199529881231/1600000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1972876467523/16000000000000 : ℝ) ≤ (-226367460648895874239/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_184 (by norm_num)
  have hUr : potential (199529881231/1600000000000 : ℝ) ≤ (-226367460648895874239/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_185 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_184
  linarith only [hU, hF]

theorem cell_bound_185 : cellBound ((199529881231/1600000000000 : ℚ) : ℝ) ((2017721157097/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (199529881231/1600000000000 : ℝ) ≤ (-225879083485139331351/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_185 (by norm_num)
  have hUr : potential (2017721157097/16000000000000 : ℝ) ≤ (-225879083485139331351/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_186 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_185
  linarith only [hU, hF]

theorem cell_bound_186 : cellBound ((2017721157097/16000000000000 : ℚ) : ℝ) ((510035875471/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2017721157097/16000000000000 : ℝ) ≤ (-22540106914453362493/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_186 (by norm_num)
  have hUr : potential (510035875471/4000000000000 : ℝ) ≤ (-22540106914453362493/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_187 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_186
  linarith only [hU, hF]

theorem cell_bound_187 : cellBound ((510035875471/4000000000000 : ℚ) : ℝ) ((1042494095729/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (510035875471/4000000000000 : ℝ) ≤ (-224473899181239306607/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_187 (by norm_num)
  have hUr : potential (1042494095729/8000000000000 : ℝ) ≤ (-224473899181239306607/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_188 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_187
  linarith only [hU, hF]

theorem cell_bound_188 : cellBound ((1042494095729/8000000000000 : ℚ) : ℝ) ((266229110129/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1042494095729/8000000000000 : ℝ) ≤ (-223582014830677285851/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_188 (by norm_num)
  have hUr : potential (266229110129/2000000000000 : ℝ) ≤ (-223582014830677285851/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_189 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_188
  linarith only [hU, hF]

theorem cell_bound_189 : cellBound ((266229110129/2000000000000 : ℚ) : ℝ) ((110976113009/800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (266229110129/2000000000000 : ℝ) ≤ (-44378322237474152161/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_189 (by norm_num)
  have hUr : potential (110976113009/800000000000 : ℝ) ≤ (-44378322237474152161/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_190 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_189
  linarith only [hU, hF]

theorem cell_bound_190 : cellBound ((110976113009/800000000000 : ℚ) : ℝ) ((72162863729/500000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (110976113009/800000000000 : ℝ) ≤ (-220309373254637685199/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_190 (by norm_num)
  have hUr : potential (72162863729/500000000000 : ℝ) ≤ (-220309373254637685199/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_191 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_190
  linarith only [hU, hF]

theorem cell_bound_191 : cellBound ((72162863729/500000000000 : ℚ) : ℝ) ((4675203313927/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (72162863729/500000000000 : ℝ) ≤ (-217948749324457128731/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_191 (by norm_num)
  have hUr : potential (4675203313927/32000000000000 : ℝ) ≤ (-217948749324457128731/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_192 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_191
  linarith only [hU, hF]

#print axioms cell_bound_191
end Zeta5AppendixNumerics
