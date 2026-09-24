import AppendixCellBase
import AppendixField.Batch055
import AppendixField.Batch056
import AppendixField.Batch057
import AppendixPotential.Batch056
import AppendixPotential.Batch057
import AppendixPotential.Batch058
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_448 : cellBound ((47053570071/100000000000 : ℚ) : ℝ) ((943720001173/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (47053570071/100000000000 : ℝ) ≤ (-114163202331566941999/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_448 (by norm_num)
  have hUr : potential (943720001173/2000000000000 : ℝ) ≤ (-114163202331566941999/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_449 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_448
  linarith only [hU, hF]

theorem cell_bound_449 : cellBound ((943720001173/2000000000000 : ℚ) : ℝ) ((473184300463/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (943720001173/2000000000000 : ℝ) ≤ (-28464154990383765911/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_449 (by norm_num)
  have hUr : potential (473184300463/1000000000000 : ℝ) ≤ (-28464154990383765911/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_450 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_449
  linarith only [hU, hF]

theorem cell_bound_450 : cellBound ((473184300463/1000000000000 : ℚ) : ℝ) ((949017200679/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (473184300463/1000000000000 : ℝ) ≤ (-113552260280721841407/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_450 (by norm_num)
  have hUr : potential (949017200679/2000000000000 : ℝ) ≤ (-113552260280721841407/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_451 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_450
  linarith only [hU, hF]

theorem cell_bound_451 : cellBound ((949017200679/2000000000000 : ℚ) : ℝ) ((59479112527/125000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (949017200679/2000000000000 : ℝ) ≤ (-113250057901493320671/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_451 (by norm_num)
  have hUr : potential (59479112527/125000000000 : ℝ) ≤ (-113250057901493320671/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_452 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_451
  linarith only [hU, hF]

theorem cell_bound_452 : cellBound ((59479112527/125000000000 : ℚ) : ℝ) ((190862880037/400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (59479112527/125000000000 : ℝ) ≤ (-3529685991809762371/3125000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_452 (by norm_num)
  have hUr : potential (190862880037/400000000000 : ℝ) ≤ (-3529685991809762371/3125000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_453 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_452
  linarith only [hU, hF]

theorem cell_bound_453 : cellBound ((190862880037/400000000000 : ℚ) : ℝ) ((478481499969/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (190862880037/400000000000 : ℝ) ≤ (-112651884507907006579/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_453 (by norm_num)
  have hUr : potential (478481499969/1000000000000 : ℝ) ≤ (-112651884507907006579/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_454 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_453
  linarith only [hU, hF]

theorem cell_bound_454 : cellBound ((478481499969/1000000000000 : ℚ) : ℝ) ((959611599691/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (478481499969/1000000000000 : ℝ) ≤ (-112355802442665961579/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_454 (by norm_num)
  have hUr : potential (959611599691/2000000000000 : ℝ) ≤ (-112355802442665961579/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_455 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_454
  linarith only [hU, hF]

theorem cell_bound_455 : cellBound ((959611599691/2000000000000 : ℚ) : ℝ) ((240565049861/500000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (959611599691/2000000000000 : ℝ) ≤ (-112061654756110297327/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_455 (by norm_num)
  have hUr : potential (240565049861/500000000000 : ℝ) ≤ (-112061654756110297327/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_456 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_455
  linarith only [hU, hF]

theorem cell_bound_456 : cellBound ((240565049861/500000000000 : ℚ) : ℝ) ((19351147979/40000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (240565049861/500000000000 : ℝ) ≤ (-27869743542579942577/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_456 (by norm_num)
  have hUr : potential (19351147979/40000000000 : ℝ) ≤ (-27869743542579942577/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_457 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_456
  linarith only [hU, hF]

theorem cell_bound_457 : cellBound ((19351147979/40000000000 : ℚ) : ℝ) ((121606824807/250000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (19351147979/40000000000 : ℝ) ≤ (-27725872492518644477/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_457 (by norm_num)
  have hUr : potential (121606824807/250000000000 : ℝ) ≤ (-27725872492518644477/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_458 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_457
  linarith only [hU, hF]

theorem cell_bound_458 : cellBound ((121606824807/250000000000 : ℚ) : ℝ) ((489075898981/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (121606824807/250000000000 : ℝ) ≤ (-2206697702154394529/2000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_458 (by norm_num)
  have hUr : potential (489075898981/1000000000000 : ℝ) ≤ (-2206697702154394529/2000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_459 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_458
  linarith only [hU, hF]

theorem cell_bound_459 : cellBound ((489075898981/1000000000000 : ℚ) : ℝ) ((245862249367/500000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (489075898981/1000000000000 : ℝ) ≤ (-109772872852122934463/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_459 (by norm_num)
  have hUr : potential (245862249367/500000000000 : ℝ) ≤ (-109772872852122934463/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_460 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_459
  linarith only [hU, hF]

theorem cell_bound_460 : cellBound ((245862249367/500000000000 : ℚ) : ℝ) ((494373098487/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (245862249367/500000000000 : ℝ) ≤ (-54608595885859130209/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_460 (by norm_num)
  have hUr : potential (494373098487/1000000000000 : ℝ) ≤ (-54608595885859130209/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_461 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_460
  linarith only [hU, hF]

theorem cell_bound_461 : cellBound ((494373098487/1000000000000 : ℚ) : ℝ) ((1553192807/3125000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (494373098487/1000000000000 : ℝ) ≤ (-108667603158713893069/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_461 (by norm_num)
  have hUr : potential (1553192807/3125000000 : ℝ) ≤ (-108667603158713893069/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_462 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_461
  linarith only [hU, hF]

theorem cell_bound_462 : cellBound ((1553192807/3125000000 : ℚ) : ℝ) ((499670297993/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1553192807/3125000000 : ℝ) ≤ (-108123887724589318831/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_462 (by norm_num)
  have hUr : potential (499670297993/1000000000000 : ℝ) ≤ (-108123887724589318831/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_463 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_462
  linarith only [hU, hF]

theorem cell_bound_463 : cellBound ((499670297993/1000000000000 : ℚ) : ℝ) ((504967497499/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (499670297993/1000000000000 : ℝ) ≤ (-107053280628239716843/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_463 (by norm_num)
  have hUr : potential (504967497499/1000000000000 : ℝ) ≤ (-107053280628239716843/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_464 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_463
  linarith only [hU, hF]

#print axioms cell_bound_463
end Zeta5AppendixNumerics
