import CertificateTactics
import AppendixCellBase
import AppendixField.Batch077
import AppendixField.Batch078
import AppendixField.Batch079
import AppendixPotential.Batch078
import AppendixPotential.Batch079
import AppendixPotential.Batch080
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_624 : cellBound ((11610952826577/16000000000000 : ℚ) : ℝ) ((23252382371711/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_624 potential_upper_625 field_lower_624

theorem cell_bound_625 : cellBound ((23252382371711/32000000000000 : ℚ) : ℝ) ((5820714772567/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_625 potential_upper_626 field_lower_625

theorem cell_bound_626 : cellBound ((5820714772567/8000000000000 : ℚ) : ℝ) ((932533432353/1280000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_626 potential_upper_627 field_lower_626

theorem cell_bound_627 : cellBound ((932533432353/1280000000000 : ℚ) : ℝ) ((11671906263691/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_627 potential_upper_628 field_lower_627

theorem cell_bound_628 : cellBound ((11671906263691/16000000000000 : ℚ) : ℝ) ((23374289245939/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_628 potential_upper_629 field_lower_628

theorem cell_bound_629 : cellBound ((23374289245939/32000000000000 : ℚ) : ℝ) ((1462797872781/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_629 potential_upper_630 field_lower_629

theorem cell_bound_630 : cellBound ((1462797872781/2000000000000 : ℚ) : ℝ) ((23435242683053/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_630 potential_upper_631 field_lower_630

theorem cell_bound_631 : cellBound ((23435242683053/32000000000000 : ℚ) : ℝ) ((2346571940161/3200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_631 potential_upper_632 field_lower_631

theorem cell_bound_632 : cellBound ((2346571940161/3200000000000 : ℚ) : ℝ) ((23496196120167/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_632 potential_upper_633 field_lower_632

theorem cell_bound_633 : cellBound ((23496196120167/32000000000000 : ℚ) : ℝ) ((5881668209681/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_633 potential_upper_634 field_lower_633

theorem cell_bound_634 : cellBound ((5881668209681/8000000000000 : ℚ) : ℝ) ((23557149557281/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_634 potential_upper_635 field_lower_634

theorem cell_bound_635 : cellBound ((23557149557281/32000000000000 : ℚ) : ℝ) ((11793813137919/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_635 potential_upper_636 field_lower_635

theorem cell_bound_636 : cellBound ((11793813137919/16000000000000 : ℚ) : ℝ) ((4723620598879/6400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_636 potential_upper_637 field_lower_636

theorem cell_bound_637 : cellBound ((4723620598879/6400000000000 : ℚ) : ℝ) ((2956072464119/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_637 potential_upper_638 field_lower_637

theorem cell_bound_638 : cellBound ((2956072464119/4000000000000 : ℚ) : ℝ) ((23679056431509/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_638 potential_upper_639 field_lower_638

theorem cell_bound_639 : cellBound ((23679056431509/32000000000000 : ℚ) : ℝ) ((11854766575033/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_639 potential_upper_640 field_lower_639

end Zeta5AppendixNumerics
