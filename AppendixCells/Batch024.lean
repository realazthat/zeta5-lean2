import AppendixCellBase
import AppendixField.Batch047
import AppendixField.Batch048
import AppendixField.Batch049
import AppendixPotential.Batch048
import AppendixPotential.Batch049
import AppendixPotential.Batch050
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_384 : cellBound ((24306660222459/64000000000000 : ℚ) : ℝ) ((48697037595177/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (24306660222459/64000000000000 : ℝ) ≤ (-13823536077316868753/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_384 (by norm_num)
  have hUr : potential (48697037595177/128000000000000 : ℝ) ≤ (-13823536077316868753/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_385 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_384
  linarith only [hU, hF]

theorem cell_bound_385 : cellBound ((48697037595177/128000000000000 : ℚ) : ℝ) ((12195188686359/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (48697037595177/128000000000000 : ℝ) ≤ (-69031614817474103853/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_385 (by norm_num)
  have hUr : potential (12195188686359/32000000000000 : ℝ) ≤ (-69031614817474103853/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_386 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_385
  linarith only [hU, hF]

theorem cell_bound_386 : cellBound ((12195188686359/32000000000000 : ℚ) : ℝ) ((9772894379139/25600000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (12195188686359/32000000000000 : ℝ) ≤ (-13789192127962126743/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_386 (by norm_num)
  have hUr : potential (9772894379139/25600000000000 : ℝ) ≤ (-13789192127962126743/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_387 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_386
  linarith only [hU, hF]

theorem cell_bound_387 : cellBound ((9772894379139/25600000000000 : ℚ) : ℝ) ((24474094522977/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (9772894379139/25600000000000 : ℝ) ≤ (-34430354869273403561/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_387 (by norm_num)
  have hUr : potential (24474094522977/64000000000000 : ℝ) ≤ (-34430354869273403561/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_388 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_387
  linarith only [hU, hF]

theorem cell_bound_388 : cellBound ((24474094522977/64000000000000 : ℚ) : ℝ) ((6139452918309/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (24474094522977/64000000000000 : ℝ) ≤ (-137382775202194839509/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_388 (by norm_num)
  have hUr : potential (6139452918309/16000000000000 : ℝ) ≤ (-137382775202194839509/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_389 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_388
  linarith only [hU, hF]

theorem cell_bound_389 : cellBound ((6139452918309/16000000000000 : ℚ) : ℝ) ((4928305764699/12800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (6139452918309/16000000000000 : ℝ) ≤ (-137047180764546325439/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_389 (by norm_num)
  have hUr : potential (4928305764699/12800000000000 : ℝ) ≤ (-137047180764546325439/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_390 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_389
  linarith only [hU, hF]

theorem cell_bound_390 : cellBound ((4928305764699/12800000000000 : ℚ) : ℝ) ((12362622986877/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (4928305764699/12800000000000 : ℝ) ≤ (-27342906019937915583/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_390 (by norm_num)
  have hUr : potential (12362622986877/32000000000000 : ℝ) ≤ (-27342906019937915583/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_391 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_390
  linarith only [hU, hF]

theorem cell_bound_391 : cellBound ((12362622986877/32000000000000 : ℚ) : ℝ) ((24808963124013/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (12362622986877/32000000000000 : ℝ) ≤ (-27276944792294163977/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_391 (by norm_num)
  have hUr : potential (24808963124013/64000000000000 : ℝ) ≤ (-27276944792294163977/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_392 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_391
  linarith only [hU, hF]

theorem cell_bound_392 : cellBound ((24808963124013/64000000000000 : ℚ) : ℝ) ((777896258571/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (24808963124013/64000000000000 : ℝ) ≤ (-136057670777301820481/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_392 (by norm_num)
  have hUr : potential (777896258571/2000000000000 : ℝ) ≤ (-136057670777301820481/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_393 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_392
  linarith only [hU, hF]

theorem cell_bound_393 : cellBound ((777896258571/2000000000000 : ℚ) : ℝ) ((24976397424531/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (777896258571/2000000000000 : ℝ) ≤ (-5429331400880416053/4000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_393 (by norm_num)
  have hUr : potential (24976397424531/64000000000000 : ℝ) ≤ (-5429331400880416053/4000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_394 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_393
  linarith only [hU, hF]

theorem cell_bound_394 : cellBound ((24976397424531/64000000000000 : ℚ) : ℝ) ((2506011457479/6400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (24976397424531/64000000000000 : ℝ) ≤ (-33852871691358143751/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_394 (by norm_num)
  have hUr : potential (2506011457479/6400000000000 : ℝ) ≤ (-33852871691358143751/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_395 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_394
  linarith only [hU, hF]

theorem cell_bound_395 : cellBound ((2506011457479/6400000000000 : ℚ) : ℝ) ((25143831725049/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2506011457479/6400000000000 : ℝ) ≤ (-27018440301267965659/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_395 (by norm_num)
  have hUr : potential (25143831725049/64000000000000 : ℝ) ≤ (-27018440301267965659/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_396 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_395
  linarith only [hU, hF]

theorem cell_bound_396 : cellBound ((25143831725049/64000000000000 : ℚ) : ℝ) ((6306887218827/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (25143831725049/64000000000000 : ℝ) ≤ (-134775359025520276561/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_396 (by norm_num)
  have hUr : potential (6306887218827/16000000000000 : ℝ) ≤ (-134775359025520276561/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_397 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_396
  linarith only [hU, hF]

theorem cell_bound_397 : cellBound ((6306887218827/16000000000000 : ℚ) : ℝ) ((12697491587913/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (6306887218827/16000000000000 : ℝ) ≤ (-67074371163051851599/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_397 (by norm_num)
  have hUr : potential (12697491587913/32000000000000 : ℝ) ≤ (-67074371163051851599/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_398 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_397
  linarith only [hU, hF]

theorem cell_bound_398 : cellBound ((12697491587913/32000000000000 : ℚ) : ℝ) ((3195302184543/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (12697491587913/32000000000000 : ℝ) ≤ (-66765576514962445409/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_398 (by norm_num)
  have hUr : potential (3195302184543/8000000000000 : ℝ) ≤ (-66765576514962445409/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_399 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_398
  linarith only [hU, hF]

theorem cell_bound_399 : cellBound ((3195302184543/8000000000000 : ℚ) : ℝ) ((12864925888431/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (3195302184543/8000000000000 : ℝ) ≤ (-132922158519936424321/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_399 (by norm_num)
  have hUr : potential (12864925888431/32000000000000 : ℝ) ≤ (-132922158519936424321/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_400 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_399
  linarith only [hU, hF]

#print axioms cell_bound_399
end Zeta5AppendixNumerics
