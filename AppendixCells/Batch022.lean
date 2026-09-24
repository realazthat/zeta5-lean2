import AppendixCellBase
import AppendixField.Batch043
import AppendixField.Batch044
import AppendixField.Batch045
import AppendixPotential.Batch044
import AppendixPotential.Batch045
import AppendixPotential.Batch046
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_352 : cellBound ((11358017183769/32000000000000 : ℚ) : ℝ) ((22799751517797/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (11358017183769/32000000000000 : ℝ) ≤ (-18183355257558500957/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_352 (by norm_num)
  have hUr : potential (22799751517797/64000000000000 : ℝ) ≤ (-18183355257558500957/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_353 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_352
  linarith only [hU, hF]

theorem cell_bound_353 : cellBound ((22799751517797/64000000000000 : ℚ) : ℝ) ((2860433583507/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (22799751517797/64000000000000 : ℝ) ≤ (-18125852805348883297/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_353 (by norm_num)
  have hUr : potential (2860433583507/8000000000000 : ℝ) ≤ (-18125852805348883297/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_354 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_353
  linarith only [hU, hF]

theorem cell_bound_354 : cellBound ((2860433583507/8000000000000 : ℚ) : ℝ) ((4593437163663/12800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2860433583507/8000000000000 : ℝ) ≤ (-36140045534925996791/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_354 (by norm_num)
  have hUr : potential (4593437163663/12800000000000 : ℝ) ≤ (-36140045534925996791/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_355 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_354
  linarith only [hU, hF]

theorem cell_bound_355 : cellBound ((4593437163663/12800000000000 : ℚ) : ℝ) ((11525451484287/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (4593437163663/12800000000000 : ℝ) ≤ (-144124990651532956617/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_355 (by norm_num)
  have hUr : potential (11525451484287/32000000000000 : ℝ) ≤ (-144124990651532956617/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_356 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_355
  linarith only [hU, hF]

theorem cell_bound_356 : cellBound ((11525451484287/32000000000000 : ℚ) : ℝ) ((23134620118833/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (11525451484287/32000000000000 : ℝ) ≤ (-143699784443670693707/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_356 (by norm_num)
  have hUr : potential (23134620118833/64000000000000 : ℝ) ≤ (-143699784443670693707/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_357 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_356
  linarith only [hU, hF]

theorem cell_bound_357 : cellBound ((23134620118833/64000000000000 : ℚ) : ℝ) ((5804584317273/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (23134620118833/64000000000000 : ℝ) ≤ (-143283421711610395197/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_357 (by norm_num)
  have hUr : potential (5804584317273/16000000000000 : ℝ) ≤ (-143283421711610395197/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_358 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_357
  linarith only [hU, hF]

theorem cell_bound_358 : cellBound ((5804584317273/16000000000000 : ℚ) : ℝ) ((46520391688443/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (5804584317273/16000000000000 : ℝ) ≤ (-143078264320155271051/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_358 (by norm_num)
  have hUr : potential (46520391688443/128000000000000 : ℝ) ≤ (-143078264320155271051/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_359 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_358
  linarith only [hU, hF]

theorem cell_bound_359 : cellBound ((46520391688443/128000000000000 : ℚ) : ℝ) ((23302054419351/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (46520391688443/128000000000000 : ℝ) ≤ (-142874989912090301389/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_359 (by norm_num)
  have hUr : potential (23302054419351/64000000000000 : ℝ) ≤ (-142874989912090301389/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_360 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_359
  linarith only [hU, hF]

theorem cell_bound_360 : cellBound ((23302054419351/64000000000000 : ℚ) : ℝ) ((46687825988961/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (23302054419351/64000000000000 : ℝ) ≤ (-142673510124909957981/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_360 (by norm_num)
  have hUr : potential (46687825988961/128000000000000 : ℝ) ≤ (-142673510124909957981/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_361 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_360
  linarith only [hU, hF]

theorem cell_bound_361 : cellBound ((46687825988961/128000000000000 : ℚ) : ℝ) ((2338577156961/6400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (46687825988961/128000000000000 : ℝ) ≤ (-71236872466908647691/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_361 (by norm_num)
  have hUr : potential (2338577156961/6400000000000 : ℝ) ≤ (-71236872466908647691/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_362 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_361
  linarith only [hU, hF]

theorem cell_bound_362 : cellBound ((2338577156961/6400000000000 : ℚ) : ℝ) ((46855260289479/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2338577156961/6400000000000 : ℝ) ≤ (-28455124156061312997/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_362 (by norm_num)
  have hUr : potential (46855260289479/128000000000000 : ℝ) ≤ (-28455124156061312997/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_363 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_362
  linarith only [hU, hF]

theorem cell_bound_363 : cellBound ((46855260289479/128000000000000 : ℚ) : ℝ) ((23469488719869/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (46855260289479/128000000000000 : ℝ) ≤ (-142079070600170055583/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_363 (by norm_num)
  have hUr : potential (23469488719869/64000000000000 : ℝ) ≤ (-142079070600170055583/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_364 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_363
  linarith only [hU, hF]

theorem cell_bound_364 : cellBound ((23469488719869/64000000000000 : ℚ) : ℝ) ((47022694589997/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (23469488719869/64000000000000 : ℝ) ≤ (-70942016013050336551/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_364 (by norm_num)
  have hUr : potential (47022694589997/128000000000000 : ℝ) ≤ (-70942016013050336551/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_365 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_364
  linarith only [hU, hF]

theorem cell_bound_365 : cellBound ((47022694589997/128000000000000 : ℚ) : ℝ) ((1472075366883/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (47022694589997/128000000000000 : ℝ) ≤ (-141690448361853503469/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_365 (by norm_num)
  have hUr : potential (1472075366883/4000000000000 : ℝ) ≤ (-141690448361853503469/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_366 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_365
  linarith only [hU, hF]

theorem cell_bound_366 : cellBound ((1472075366883/4000000000000 : ℚ) : ℝ) ((9438025778103/25600000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1472075366883/4000000000000 : ℝ) ≤ (-141498266387551845161/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_366 (by norm_num)
  have hUr : potential (9438025778103/25600000000000 : ℝ) ≤ (-141498266387551845161/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_367 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_366
  linarith only [hU, hF]

theorem cell_bound_367 : cellBound ((9438025778103/25600000000000 : ℚ) : ℝ) ((23636923020387/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (9438025778103/25600000000000 : ℝ) ≤ (-14130743703133955607/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_367 (by norm_num)
  have hUr : potential (23636923020387/64000000000000 : ℝ) ≤ (-14130743703133955607/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_368 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_367
  linarith only [hU, hF]

#print axioms cell_bound_367
end Zeta5AppendixNumerics
