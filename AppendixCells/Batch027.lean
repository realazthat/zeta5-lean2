import AppendixCellBase
import AppendixField.Batch053
import AppendixField.Batch054
import AppendixField.Batch055
import AppendixPotential.Batch054
import AppendixPotential.Batch055
import AppendixPotential.Batch056
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_432 : cellBound ((1831819407533/4000000000000 : ℚ) : ℝ) ((917234003643/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1831819407533/4000000000000 : ℝ) ≤ (-58684914105373099173/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_432 (by norm_num)
  have hUr : potential (917234003643/2000000000000 : ℝ) ≤ (-58684914105373099173/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_433 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_432
  linarith only [hU, hF]

theorem cell_bound_433 : cellBound ((917234003643/2000000000000 : ℚ) : ℝ) ((1837116607039/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (917234003643/2000000000000 : ℝ) ≤ (-11720252423701605107/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_433 (by norm_num)
  have hUr : potential (1837116607039/4000000000000 : ℝ) ≤ (-11720252423701605107/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_434 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_433
  linarith only [hU, hF]

theorem cell_bound_434 : cellBound ((1837116607039/4000000000000 : ℚ) : ℝ) ((229970650849/500000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1837116607039/4000000000000 : ℝ) ≤ (-117036054702331535937/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_434 (by norm_num)
  have hUr : potential (229970650849/500000000000 : ℝ) ≤ (-117036054702331535937/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_435 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_434
  linarith only [hU, hF]

theorem cell_bound_435 : cellBound ((229970650849/500000000000 : ℚ) : ℝ) ((368482761309/800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (229970650849/500000000000 : ℝ) ≤ (-11687039919036812333/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_435 (by norm_num)
  have hUr : potential (368482761309/800000000000 : ℝ) ≤ (-11687039919036812333/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_436 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_435
  linarith only [hU, hF]

theorem cell_bound_436 : cellBound ((368482761309/800000000000 : ℚ) : ℝ) ((922531203149/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (368482761309/800000000000 : ℝ) ≤ (-11670553834956354811/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_436 (by norm_num)
  have hUr : potential (922531203149/2000000000000 : ℝ) ≤ (-11670553834956354811/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_437 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_436
  linarith only [hU, hF]

theorem cell_bound_437 : cellBound ((922531203149/2000000000000 : ℚ) : ℝ) ((1847711006051/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (922531203149/2000000000000 : ℝ) ≤ (-116541453996673553633/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_437 (by norm_num)
  have hUr : potential (1847711006051/4000000000000 : ℝ) ≤ (-116541453996673553633/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_438 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_437
  linarith only [hU, hF]

theorem cell_bound_438 : cellBound ((1847711006051/4000000000000 : ℚ) : ℝ) ((462589901451/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1847711006051/4000000000000 : ℝ) ≤ (-116378128547248647123/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_438 (by norm_num)
  have hUr : potential (462589901451/1000000000000 : ℝ) ≤ (-116378128547248647123/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_439 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_438
  linarith only [hU, hF]

theorem cell_bound_439 : cellBound ((462589901451/1000000000000 : ℚ) : ℝ) ((1853008205557/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (462589901451/1000000000000 : ℝ) ≤ (-116215545441678666687/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_439 (by norm_num)
  have hUr : potential (1853008205557/4000000000000 : ℝ) ≤ (-116215545441678666687/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_440 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_439
  linarith only [hU, hF]

theorem cell_bound_440 : cellBound ((1853008205557/4000000000000 : ℚ) : ℝ) ((185565680531/400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1853008205557/4000000000000 : ℝ) ≤ (-116053688975071483133/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_440 (by norm_num)
  have hUr : potential (185565680531/400000000000 : ℝ) ≤ (-116053688975071483133/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_441 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_440
  linarith only [hU, hF]

theorem cell_bound_441 : cellBound ((185565680531/400000000000 : ℚ) : ℝ) ((1858305405063/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (185565680531/400000000000 : ℝ) ≤ (-115892544000854271261/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_441 (by norm_num)
  have hUr : potential (1858305405063/4000000000000 : ℝ) ≤ (-115892544000854271261/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_442 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_441
  linarith only [hU, hF]

theorem cell_bound_442 : cellBound ((1858305405063/4000000000000 : ℚ) : ℝ) ((116309625301/250000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1858305405063/4000000000000 : ℝ) ≤ (-115732096332816522089/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_442 (by norm_num)
  have hUr : potential (116309625301/250000000000 : ℝ) ≤ (-115732096332816522089/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_443 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_442
  linarith only [hU, hF]

theorem cell_bound_443 : cellBound ((116309625301/250000000000 : ℚ) : ℝ) ((1863602604569/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (116309625301/250000000000 : ℝ) ≤ (-57786166003012420219/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_443 (by norm_num)
  have hUr : potential (1863602604569/4000000000000 : ℝ) ≤ (-57786166003012420219/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_444 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_443
  linarith only [hU, hF]

theorem cell_bound_444 : cellBound ((1863602604569/4000000000000 : ℚ) : ℝ) ((933125602161/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1863602604569/4000000000000 : ℝ) ≤ (-115413238027610106011/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_444 (by norm_num)
  have hUr : potential (933125602161/2000000000000 : ℝ) ≤ (-115413238027610106011/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_445 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_444
  linarith only [hU, hF]

theorem cell_bound_445 : cellBound ((933125602161/2000000000000 : ℚ) : ℝ) ((467887100957/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (933125602161/2000000000000 : ℝ) ≤ (-115097010598791423493/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_445 (by norm_num)
  have hUr : potential (467887100957/1000000000000 : ℝ) ≤ (-115097010598791423493/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_446 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_445
  linarith only [hU, hF]

theorem cell_bound_446 : cellBound ((467887100957/1000000000000 : ℚ) : ℝ) ((938422801667/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (467887100957/1000000000000 : ℝ) ≤ (-22956663908978690757/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_446 (by norm_num)
  have hUr : potential (938422801667/2000000000000 : ℝ) ≤ (-22956663908978690757/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_447 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_446
  linarith only [hU, hF]

theorem cell_bound_447 : cellBound ((938422801667/2000000000000 : ℚ) : ℝ) ((47053570071/100000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (938422801667/2000000000000 : ℝ) ≤ (-57236038478498646311/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_447 (by norm_num)
  have hUr : potential (47053570071/100000000000 : ℝ) ≤ (-57236038478498646311/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_448 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_447
  linarith only [hU, hF]

#print axioms cell_bound_447
end Zeta5AppendixNumerics
