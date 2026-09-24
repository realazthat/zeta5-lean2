import AppendixCellBase
import AppendixField.Batch051
import AppendixField.Batch052
import AppendixField.Batch053
import AppendixPotential.Batch052
import AppendixPotential.Batch053
import AppendixPotential.Batch054
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_416 : cellBound ((446698302933/1000000000000 : ℚ) : ℝ) ((896045205619/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (446698302933/1000000000000 : ℝ) ≤ (-120182685782322383467/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_416 (by norm_num)
  have hUr : potential (896045205619/2000000000000 : ℝ) ≤ (-120182685782322383467/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_417 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_416
  linarith only [hU, hF]

theorem cell_bound_417 : cellBound ((896045205619/2000000000000 : ℚ) : ℝ) ((1794739010991/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (896045205619/2000000000000 : ℝ) ≤ (-23999581894026629497/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_417 (by norm_num)
  have hUr : potential (1794739010991/4000000000000 : ℝ) ≤ (-23999581894026629497/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_418 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_417
  linarith only [hU, hF]

theorem cell_bound_418 : cellBound ((1794739010991/4000000000000 : ℚ) : ℝ) ((224673451343/500000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1794739010991/4000000000000 : ℝ) ≤ (-119814553591418354909/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_418 (by norm_num)
  have hUr : potential (224673451343/500000000000 : ℝ) ≤ (-119814553591418354909/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_419 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_418
  linarith only [hU, hF]

theorem cell_bound_419 : cellBound ((224673451343/500000000000 : ℚ) : ℝ) ((1800036210497/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (224673451343/500000000000 : ℝ) ≤ (-59816278547100337921/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_419 (by norm_num)
  have hUr : potential (1800036210497/4000000000000 : ℝ) ≤ (-59816278547100337921/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_420 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_419
  linarith only [hU, hF]

theorem cell_bound_420 : cellBound ((1800036210497/4000000000000 : ℚ) : ℝ) ((7210739241/16000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1800036210497/4000000000000 : ℝ) ≤ (-23890372856263037409/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_420 (by norm_num)
  have hUr : potential (7210739241/16000000000 : ℝ) ≤ (-23890372856263037409/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_421 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_420
  linarith only [hU, hF]

theorem cell_bound_421 : cellBound ((7210739241/16000000000 : ℚ) : ℝ) ((1805333410003/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (7210739241/16000000000 : ℝ) ≤ (-119272423811880859329/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_421 (by norm_num)
  have hUr : potential (1805333410003/4000000000000 : ℝ) ≤ (-119272423811880859329/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_422 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_421
  linarith only [hU, hF]

theorem cell_bound_422 : cellBound ((1805333410003/4000000000000 : ℚ) : ℝ) ((451995502439/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1805333410003/4000000000000 : ℝ) ≤ (-29773547137490026147/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_422 (by norm_num)
  have hUr : potential (451995502439/1000000000000 : ℝ) ≤ (-29773547137490026147/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_423 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_422
  linarith only [hU, hF]

theorem cell_bound_423 : cellBound ((451995502439/1000000000000 : ℚ) : ℝ) ((1810630609509/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (451995502439/1000000000000 : ℝ) ≤ (-118917114440940248487/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_423 (by norm_num)
  have hUr : potential (1810630609509/4000000000000 : ℝ) ≤ (-118917114440940248487/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_424 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_423
  linarith only [hU, hF]

theorem cell_bound_424 : cellBound ((1810630609509/4000000000000 : ℚ) : ℝ) ((906639604631/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1810630609509/4000000000000 : ℝ) ≤ (-23748232217585668613/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_424 (by norm_num)
  have hUr : potential (906639604631/2000000000000 : ℝ) ≤ (-23748232217585668613/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_425 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_424
  linarith only [hU, hF]

theorem cell_bound_425 : cellBound ((906639604631/2000000000000 : ℚ) : ℝ) ((363185561803/800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (906639604631/2000000000000 : ℝ) ≤ (-29641572674985113963/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_425 (by norm_num)
  have hUr : potential (363185561803/800000000000 : ℝ) ≤ (-29641572674985113963/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_426 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_425
  linarith only [hU, hF]

theorem cell_bound_426 : cellBound ((363185561803/800000000000 : ℚ) : ℝ) ((28415256387/62500000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (363185561803/800000000000 : ℝ) ≤ (-118392467856086975601/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_426 (by norm_num)
  have hUr : potential (28415256387/62500000000 : ℝ) ≤ (-118392467856086975601/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_427 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_426
  linarith only [hU, hF]

theorem cell_bound_427 : cellBound ((28415256387/62500000000 : ℚ) : ℝ) ((1821225008521/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (28415256387/62500000000 : ℝ) ≤ (-59109829877920159961/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_427 (by norm_num)
  have hUr : potential (1821225008521/4000000000000 : ℝ) ≤ (-59109829877920159961/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_428 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_427
  linarith only [hU, hF]

theorem cell_bound_428 : cellBound ((1821225008521/4000000000000 : ℚ) : ℝ) ((911936804137/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1821225008521/4000000000000 : ℝ) ≤ (-118047835679081803957/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_428 (by norm_num)
  have hUr : potential (911936804137/2000000000000 : ℝ) ≤ (-118047835679081803957/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_429 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_428
  linarith only [hU, hF]

theorem cell_bound_429 : cellBound ((911936804137/2000000000000 : ℚ) : ℝ) ((1826522208027/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (911936804137/2000000000000 : ℝ) ≤ (-23575393367254431093/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_429 (by norm_num)
  have hUr : potential (1826522208027/4000000000000 : ℝ) ≤ (-23575393367254431093/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_430 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_429
  linarith only [hU, hF]

theorem cell_bound_430 : cellBound ((1826522208027/4000000000000 : ℚ) : ℝ) ((91458540389/200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1826522208027/4000000000000 : ℝ) ≤ (-117707026059553453181/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_430 (by norm_num)
  have hUr : potential (91458540389/200000000000 : ℝ) ≤ (-117707026059553453181/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_431 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_430
  linarith only [hU, hF]

theorem cell_bound_431 : cellBound ((91458540389/200000000000 : ℚ) : ℝ) ((1831819407533/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (91458540389/200000000000 : ℝ) ≤ (-23507597578557752549/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_431 (by norm_num)
  have hUr : potential (1831819407533/4000000000000 : ℝ) ≤ (-23507597578557752549/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_432 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_431
  linarith only [hU, hF]

#print axioms cell_bound_431
end Zeta5AppendixNumerics
