import CertificateTactics
import AppendixCellBase
import AppendixField.Batch055
import AppendixField.Batch056
import AppendixField.Batch057
import AppendixPotential.Batch056
import AppendixPotential.Batch057
import AppendixPotential.Batch058
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_448 : cellBound ((47053570071/100000000000 : ℚ) : ℝ) ((943720001173/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_448 potential_upper_449 field_lower_448

theorem cell_bound_449 : cellBound ((943720001173/2000000000000 : ℚ) : ℝ) ((473184300463/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_449 potential_upper_450 field_lower_449

theorem cell_bound_450 : cellBound ((473184300463/1000000000000 : ℚ) : ℝ) ((949017200679/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_450 potential_upper_451 field_lower_450

theorem cell_bound_451 : cellBound ((949017200679/2000000000000 : ℚ) : ℝ) ((59479112527/125000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_451 potential_upper_452 field_lower_451

theorem cell_bound_452 : cellBound ((59479112527/125000000000 : ℚ) : ℝ) ((190862880037/400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_452 potential_upper_453 field_lower_452

theorem cell_bound_453 : cellBound ((190862880037/400000000000 : ℚ) : ℝ) ((478481499969/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_453 potential_upper_454 field_lower_453

theorem cell_bound_454 : cellBound ((478481499969/1000000000000 : ℚ) : ℝ) ((959611599691/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_454 potential_upper_455 field_lower_454

theorem cell_bound_455 : cellBound ((959611599691/2000000000000 : ℚ) : ℝ) ((240565049861/500000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_455 potential_upper_456 field_lower_455

theorem cell_bound_456 : cellBound ((240565049861/500000000000 : ℚ) : ℝ) ((19351147979/40000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_456 potential_upper_457 field_lower_456

theorem cell_bound_457 : cellBound ((19351147979/40000000000 : ℚ) : ℝ) ((121606824807/250000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_457 potential_upper_458 field_lower_457

theorem cell_bound_458 : cellBound ((121606824807/250000000000 : ℚ) : ℝ) ((489075898981/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_458 potential_upper_459 field_lower_458

theorem cell_bound_459 : cellBound ((489075898981/1000000000000 : ℚ) : ℝ) ((245862249367/500000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_459 potential_upper_460 field_lower_459

theorem cell_bound_460 : cellBound ((245862249367/500000000000 : ℚ) : ℝ) ((494373098487/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_460 potential_upper_461 field_lower_460

theorem cell_bound_461 : cellBound ((494373098487/1000000000000 : ℚ) : ℝ) ((1553192807/3125000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_461 potential_upper_462 field_lower_461

theorem cell_bound_462 : cellBound ((1553192807/3125000000 : ℚ) : ℝ) ((499670297993/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_462 potential_upper_463 field_lower_462

theorem cell_bound_463 : cellBound ((499670297993/1000000000000 : ℚ) : ℝ) ((504967497499/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_463 potential_upper_464 field_lower_463

end Zeta5AppendixNumerics
