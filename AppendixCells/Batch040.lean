import CertificateTactics
import AppendixCellBase
import AppendixField.Batch079
import AppendixField.Batch080
import AppendixField.Batch081
import AppendixPotential.Batch080
import AppendixPotential.Batch081
import AppendixPotential.Batch082
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_640 : cellBound ((11854766575033/16000000000000 : ℚ) : ℝ) ((23740009868623/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_640 potential_upper_641 field_lower_640

theorem cell_bound_641 : cellBound ((23740009868623/32000000000000 : ℚ) : ℝ) ((1188524329359/1600000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_641 potential_upper_642 field_lower_641

theorem cell_bound_642 : cellBound ((1188524329359/1600000000000 : ℚ) : ℝ) ((23800963305737/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_642 potential_upper_643 field_lower_642

theorem cell_bound_643 : cellBound ((23800963305737/32000000000000 : ℚ) : ℝ) ((11915720012147/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_643 potential_upper_644 field_lower_643

theorem cell_bound_644 : cellBound ((11915720012147/16000000000000 : ℚ) : ℝ) ((746637295669/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_644 potential_upper_645 field_lower_644

theorem cell_bound_645 : cellBound ((746637295669/1000000000000 : ℚ) : ℝ) ((765809953469387/1024000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_645 potential_upper_646 field_lower_645

theorem cell_bound_646 : cellBound ((765809953469387/1024000000000000 : ℚ) : ℝ) ((383531658086859/512000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_646 potential_upper_647 field_lower_646

theorem cell_bound_647 : cellBound ((383531658086859/512000000000000 : ℚ) : ℝ) ((768316678878049/1024000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_647 potential_upper_648 field_lower_647

theorem cell_bound_648 : cellBound ((768316678878049/1024000000000000 : ℚ) : ℝ) ((38478502079119/51200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_648 potential_upper_649 field_lower_648

theorem cell_bound_649 : cellBound ((38478502079119/51200000000000 : ℚ) : ℝ) ((770823404286711/1024000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_649 potential_upper_650 field_lower_649

theorem cell_bound_650 : cellBound ((770823404286711/1024000000000000 : ℚ) : ℝ) ((386038383495521/512000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_650 potential_upper_651 field_lower_650

theorem cell_bound_651 : cellBound ((386038383495521/512000000000000 : ℚ) : ℝ) ((773330129695373/1024000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_651 potential_upper_652 field_lower_651

theorem cell_bound_652 : cellBound ((773330129695373/1024000000000000 : ℚ) : ℝ) ((96822936549963/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_652 potential_upper_653 field_lower_652

theorem cell_bound_653 : cellBound ((96822936549963/128000000000000 : ℚ) : ℝ) ((155167371020807/204800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_653 potential_upper_654 field_lower_653

theorem cell_bound_654 : cellBound ((155167371020807/204800000000000 : ℚ) : ℝ) ((388545108904183/512000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_654 potential_upper_655 field_lower_654

theorem cell_bound_655 : cellBound ((388545108904183/512000000000000 : ℚ) : ℝ) ((194899235804257/256000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_655 potential_upper_656 field_lower_655

end Zeta5AppendixNumerics
