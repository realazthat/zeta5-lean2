import CertificateTactics
import AppendixCellBase
import AppendixField.Batch053
import AppendixField.Batch054
import AppendixField.Batch055
import AppendixPotential.Batch054
import AppendixPotential.Batch055
import AppendixPotential.Batch056
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_432 : cellBound ((1831819407533/4000000000000 : ℚ) : ℝ) ((917234003643/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_432 potential_upper_433 field_lower_432

theorem cell_bound_433 : cellBound ((917234003643/2000000000000 : ℚ) : ℝ) ((1837116607039/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_433 potential_upper_434 field_lower_433

theorem cell_bound_434 : cellBound ((1837116607039/4000000000000 : ℚ) : ℝ) ((229970650849/500000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_434 potential_upper_435 field_lower_434

theorem cell_bound_435 : cellBound ((229970650849/500000000000 : ℚ) : ℝ) ((368482761309/800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_435 potential_upper_436 field_lower_435

theorem cell_bound_436 : cellBound ((368482761309/800000000000 : ℚ) : ℝ) ((922531203149/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_436 potential_upper_437 field_lower_436

theorem cell_bound_437 : cellBound ((922531203149/2000000000000 : ℚ) : ℝ) ((1847711006051/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_437 potential_upper_438 field_lower_437

theorem cell_bound_438 : cellBound ((1847711006051/4000000000000 : ℚ) : ℝ) ((462589901451/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_438 potential_upper_439 field_lower_438

theorem cell_bound_439 : cellBound ((462589901451/1000000000000 : ℚ) : ℝ) ((1853008205557/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_439 potential_upper_440 field_lower_439

theorem cell_bound_440 : cellBound ((1853008205557/4000000000000 : ℚ) : ℝ) ((185565680531/400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_440 potential_upper_441 field_lower_440

theorem cell_bound_441 : cellBound ((185565680531/400000000000 : ℚ) : ℝ) ((1858305405063/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_441 potential_upper_442 field_lower_441

theorem cell_bound_442 : cellBound ((1858305405063/4000000000000 : ℚ) : ℝ) ((116309625301/250000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_442 potential_upper_443 field_lower_442

theorem cell_bound_443 : cellBound ((116309625301/250000000000 : ℚ) : ℝ) ((1863602604569/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_443 potential_upper_444 field_lower_443

theorem cell_bound_444 : cellBound ((1863602604569/4000000000000 : ℚ) : ℝ) ((933125602161/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_444 potential_upper_445 field_lower_444

theorem cell_bound_445 : cellBound ((933125602161/2000000000000 : ℚ) : ℝ) ((467887100957/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_445 potential_upper_446 field_lower_445

theorem cell_bound_446 : cellBound ((467887100957/1000000000000 : ℚ) : ℝ) ((938422801667/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_446 potential_upper_447 field_lower_446

theorem cell_bound_447 : cellBound ((938422801667/2000000000000 : ℚ) : ℝ) ((47053570071/100000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_447 potential_upper_448 field_lower_447

end Zeta5AppendixNumerics
