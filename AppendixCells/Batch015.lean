import AppendixCellBase
import AppendixField.Batch029
import AppendixField.Batch030
import AppendixField.Batch031
import AppendixPotential.Batch030
import AppendixPotential.Batch031
import AppendixPotential.Batch032
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_240 : cellBound ((1552066066561/8000000000000 : ℚ) : ℝ) ((201105762729/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1552066066561/8000000000000 : ℝ) ≤ (-198031331211554974431/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_240 (by norm_num)
  have hUr : potential (201105762729/1000000000000 : ℝ) ≤ (-198031331211554974431/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_241 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_240
  linarith only [hU, hF]

theorem cell_bound_241 : cellBound ((201105762729/1000000000000 : ℚ) : ℝ) ((3251812320751/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (201105762729/1000000000000 : ℝ) ≤ (-97839100413972422761/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_241 (by norm_num)
  have hUr : potential (3251812320751/16000000000000 : ℝ) ≤ (-97839100413972422761/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_242 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_241
  linarith only [hU, hF]

theorem cell_bound_242 : cellBound ((3251812320751/16000000000000 : ℚ) : ℝ) ((1642966218919/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (3251812320751/16000000000000 : ℝ) ≤ (-97201671166191273813/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_242 (by norm_num)
  have hUr : potential (1642966218919/8000000000000 : ℝ) ≤ (-97201671166191273813/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_243 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_242
  linarith only [hU, hF]

theorem cell_bound_243 : cellBound ((1642966218919/8000000000000 : ℚ) : ℝ) ((132802102197/640000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1642966218919/8000000000000 : ℝ) ≤ (-96657009994511961501/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_243 (by norm_num)
  have hUr : potential (132802102197/640000000000 : ℝ) ≤ (-96657009994511961501/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_244 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_243
  linarith only [hU, hF]

theorem cell_bound_244 : cellBound ((132802102197/640000000000 : ℚ) : ℝ) ((6674225226937/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (132802102197/640000000000 : ℝ) ≤ (-24101197238506914467/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_244 (by norm_num)
  have hUr : potential (6674225226937/32000000000000 : ℝ) ≤ (-24101197238506914467/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_245 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_244
  linarith only [hU, hF]

theorem cell_bound_245 : cellBound ((6674225226937/32000000000000 : ℚ) : ℝ) ((838543168003/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (6674225226937/32000000000000 : ℝ) ≤ (-6010153148018309039/3125000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_245 (by norm_num)
  have hUr : potential (838543168003/4000000000000 : ℝ) ≤ (-6010153148018309039/3125000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_246 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_245
  linarith only [hU, hF]

theorem cell_bound_246 : cellBound ((838543168003/4000000000000 : ℚ) : ℝ) ((6742465461111/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (838543168003/4000000000000 : ℝ) ≤ (-3837134657315892999/2000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_246 (by norm_num)
  have hUr : potential (6742465461111/32000000000000 : ℝ) ≤ (-3837134657315892999/2000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_247 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_246
  linarith only [hU, hF]

theorem cell_bound_247 : cellBound ((6742465461111/32000000000000 : ℚ) : ℝ) ((3388292789099/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (6742465461111/32000000000000 : ℝ) ≤ (-38280538612173904593/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_247 (by norm_num)
  have hUr : potential (3388292789099/16000000000000 : ℝ) ≤ (-38280538612173904593/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_248 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_247
  linarith only [hU, hF]

theorem cell_bound_248 : cellBound ((3388292789099/16000000000000 : ℚ) : ℝ) ((1362141139057/6400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (3388292789099/16000000000000 : ℝ) ≤ (-95480487227438250321/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_248 (by norm_num)
  have hUr : potential (1362141139057/6400000000000 : ℝ) ≤ (-95480487227438250321/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_249 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_248
  linarith only [hU, hF]

theorem cell_bound_249 : cellBound ((1362141139057/6400000000000 : ℚ) : ℝ) ((1711206453093/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1362141139057/6400000000000 : ℝ) ≤ (-95265082760479284151/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_249 (by norm_num)
  have hUr : potential (1711206453093/8000000000000 : ℝ) ≤ (-95265082760479284151/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_250 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_249
  linarith only [hU, hF]

theorem cell_bound_250 : cellBound ((1711206453093/8000000000000 : ℚ) : ℝ) ((13723771741831/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1711206453093/8000000000000 : ℝ) ≤ (-95159245277207912673/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_250 (by norm_num)
  have hUr : potential (13723771741831/64000000000000 : ℝ) ≤ (-95159245277207912673/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_251 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_250
  linarith only [hU, hF]

theorem cell_bound_251 : cellBound ((13723771741831/64000000000000 : ℚ) : ℝ) ((6878945929459/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (13723771741831/64000000000000 : ℝ) ≤ (-95054568613264018713/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_251 (by norm_num)
  have hUr : potential (6878945929459/32000000000000 : ℝ) ≤ (-95054568613264018713/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_252 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_251
  linarith only [hU, hF]

theorem cell_bound_252 : cellBound ((6878945929459/32000000000000 : ℚ) : ℝ) ((2758402395201/12800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (6878945929459/32000000000000 : ℝ) ≤ (-949509980320099503/500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_252 (by norm_num)
  have hUr : potential (2758402395201/12800000000000 : ℝ) ≤ (-949509980320099503/500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_253 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_252
  linarith only [hU, hF]

theorem cell_bound_253 : cellBound ((2758402395201/12800000000000 : ℚ) : ℝ) ((3456533023273/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2758402395201/12800000000000 : ℝ) ≤ (-189696967777581515479/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_253 (by norm_num)
  have hUr : potential (3456533023273/16000000000000 : ℝ) ≤ (-189696967777581515479/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_254 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_253
  linarith only [hU, hF]

theorem cell_bound_254 : cellBound ((3456533023273/16000000000000 : ℚ) : ℝ) ((13860252210179/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (3456533023273/16000000000000 : ℝ) ≤ (-189493961182893102687/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_254 (by norm_num)
  have hUr : potential (13860252210179/64000000000000 : ℝ) ≤ (-189493961182893102687/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_255 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_254
  linarith only [hU, hF]

theorem cell_bound_255 : cellBound ((13860252210179/64000000000000 : ℚ) : ℝ) ((6947186163633/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (13860252210179/64000000000000 : ℝ) ≤ (-23661611599415158419/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_255 (by norm_num)
  have hUr : potential (6947186163633/32000000000000 : ℝ) ≤ (-23661611599415158419/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_256 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_255
  linarith only [hU, hF]

#print axioms cell_bound_255
end Zeta5AppendixNumerics
