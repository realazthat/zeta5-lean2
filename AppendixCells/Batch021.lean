import AppendixCellBase
import AppendixField.Batch041
import AppendixField.Batch042
import AppendixField.Batch043
import AppendixPotential.Batch042
import AppendixPotential.Batch043
import AppendixPotential.Batch044
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_336 : cellBound ((3929638815327/12800000000000 : ℚ) : ℝ) ((616435551059/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (3929638815327/12800000000000 : ℝ) ≤ (-159548078192063723803/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_336 (by norm_num)
  have hUr : potential (616435551059/2000000000000 : ℝ) ≤ (-159548078192063723803/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_337 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_336
  linarith only [hU, hF]

theorem cell_bound_337 : cellBound ((616435551059/2000000000000 : ℚ) : ℝ) ((19803681191141/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (616435551059/2000000000000 : ℝ) ≤ (-159219405836479295333/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_337 (by norm_num)
  have hUr : potential (19803681191141/64000000000000 : ℝ) ≤ (-159219405836479295333/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_338 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_337
  linarith only [hU, hF]

theorem cell_bound_338 : cellBound ((19803681191141/64000000000000 : ℚ) : ℝ) ((9940712374197/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (19803681191141/64000000000000 : ℝ) ≤ (-1241356604158285961/781250000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_338 (by norm_num)
  have hUr : potential (9940712374197/32000000000000 : ℝ) ≤ (-1241356604158285961/781250000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_339 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_338
  linarith only [hU, hF]

theorem cell_bound_339 : cellBound ((9940712374197/32000000000000 : ℚ) : ℝ) ((200369118629/640000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (9940712374197/32000000000000 : ℝ) ≤ (-79125260852045926809/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_339 (by norm_num)
  have hUr : potential (200369118629/640000000000 : ℝ) ≤ (-79125260852045926809/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_340 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_339
  linarith only [hU, hF]

theorem cell_bound_340 : cellBound ((200369118629/640000000000 : ℚ) : ℝ) ((10096199488703/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (200369118629/640000000000 : ℝ) ≤ (-3940451996311219041/2500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_340 (by norm_num)
  have hUr : potential (10096199488703/32000000000000 : ℝ) ≤ (-3940451996311219041/2500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_341 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_340
  linarith only [hU, hF]

theorem cell_bound_341 : cellBound ((10096199488703/32000000000000 : ℚ) : ℝ) ((2543485761489/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (10096199488703/32000000000000 : ℝ) ≤ (-31399152390602169523/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_341 (by norm_num)
  have hUr : potential (2543485761489/8000000000000 : ℝ) ≤ (-31399152390602169523/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_342 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_341
  linarith only [hU, hF]

theorem cell_bound_342 : cellBound ((2543485761489/8000000000000 : ℚ) : ℝ) ((10251686603209/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2543485761489/8000000000000 : ℝ) ≤ (-9773941803973907243/6250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_342 (by norm_num)
  have hUr : potential (10251686603209/32000000000000 : ℝ) ≤ (-9773941803973907243/6250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_343 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_342
  linarith only [hU, hF]

theorem cell_bound_343 : cellBound ((10251686603209/32000000000000 : ℚ) : ℝ) ((5164715080231/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (10251686603209/32000000000000 : ℝ) ≤ (-31155910221480454477/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_343 (by norm_num)
  have hUr : potential (5164715080231/16000000000000 : ℝ) ≤ (-31155910221480454477/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_344 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_343
  linarith only [hU, hF]

theorem cell_bound_344 : cellBound ((5164715080231/16000000000000 : ℚ) : ℝ) ((1310614659371/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (5164715080231/16000000000000 : ℝ) ≤ (-30919689502899789431/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_344 (by norm_num)
  have hUr : potential (1310614659371/4000000000000 : ℝ) ≤ (-30919689502899789431/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_345 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_344
  linarith only [hU, hF]

theorem cell_bound_345 : cellBound ((1310614659371/4000000000000 : ℚ) : ℝ) ((5320202194737/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1310614659371/4000000000000 : ℝ) ≤ (-153449597200013137211/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_345 (by norm_num)
  have hUr : potential (5320202194737/16000000000000 : ℝ) ≤ (-153449597200013137211/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_346 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_345
  linarith only [hU, hF]

theorem cell_bound_346 : cellBound ((5320202194737/16000000000000 : ℚ) : ℝ) ((539794575199/1600000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (5320202194737/16000000000000 : ℝ) ≤ (-152330589243018065517/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_346 (by norm_num)
  have hUr : potential (539794575199/1600000000000 : ℝ) ≤ (-152330589243018065517/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_347 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_346
  linarith only [hU, hF]

theorem cell_bound_347 : cellBound ((539794575199/1600000000000 : ℚ) : ℝ) ((5475689309243/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (539794575199/1600000000000 : ℝ) ≤ (-1512393545971372599/1000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_347 (by norm_num)
  have hUr : potential (5475689309243/16000000000000 : ℝ) ≤ (-1512393545971372599/1000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_348 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_347
  linarith only [hU, hF]

theorem cell_bound_348 : cellBound ((5475689309243/16000000000000 : ℚ) : ℝ) ((86772388539/250000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (5475689309243/16000000000000 : ℝ) ≤ (-150174095025189471549/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_348 (by norm_num)
  have hUr : potential (86772388539/250000000000 : ℝ) ≤ (-150174095025189471549/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_349 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_348
  linarith only [hU, hF]

theorem cell_bound_349 : cellBound ((86772388539/250000000000 : ℚ) : ℝ) ((11190582883251/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (86772388539/250000000000 : ℝ) ≤ (-74064098436194522659/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_349 (by norm_num)
  have hUr : potential (11190582883251/32000000000000 : ℝ) ≤ (-74064098436194522659/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_350 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_349
  linarith only [hU, hF]

theorem cell_bound_350 : cellBound ((11190582883251/32000000000000 : ℚ) : ℝ) ((1127430003351/3200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (11190582883251/32000000000000 : ℝ) ≤ (-117568164794942241/80000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_350 (by norm_num)
  have hUr : potential (1127430003351/3200000000000 : ℝ) ≤ (-117568164794942241/80000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_351 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_350
  linarith only [hU, hF]

theorem cell_bound_351 : cellBound ((1127430003351/3200000000000 : ℚ) : ℝ) ((11358017183769/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1127430003351/3200000000000 : ℝ) ≤ (-145942882896987346601/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_351 (by norm_num)
  have hUr : potential (11358017183769/32000000000000 : ℝ) ≤ (-145942882896987346601/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_352 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_351
  linarith only [hU, hF]

#print axioms cell_bound_351
end Zeta5AppendixNumerics
