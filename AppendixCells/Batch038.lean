import CertificateTactics
import AppendixCellBase
import AppendixField.Batch075
import AppendixField.Batch076
import AppendixField.Batch077
import AppendixPotential.Batch076
import AppendixPotential.Batch077
import AppendixPotential.Batch078
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_608 : cellBound ((2812723114819/4000000000000 : ℚ) : ℝ) ((22553704112181/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_608 potential_upper_609 field_lower_608

theorem cell_bound_609 : cellBound ((22553704112181/32000000000000 : ℚ) : ℝ) ((2260562330581/3200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_609 potential_upper_610 field_lower_609

theorem cell_bound_610 : cellBound ((2260562330581/3200000000000 : ℚ) : ℝ) ((22657542499439/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_610 potential_upper_611 field_lower_610

theorem cell_bound_611 : cellBound ((22657542499439/32000000000000 : ℚ) : ℝ) ((5677365423267/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_611 potential_upper_612 field_lower_611

theorem cell_bound_612 : cellBound ((5677365423267/8000000000000 : ℚ) : ℝ) ((22761380886697/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_612 potential_upper_613 field_lower_612

theorem cell_bound_613 : cellBound ((22761380886697/32000000000000 : ℚ) : ℝ) ((11406650040163/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_613 potential_upper_614 field_lower_613

theorem cell_bound_614 : cellBound ((11406650040163/16000000000000 : ℚ) : ℝ) ((89520072139/125000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_614 potential_upper_615 field_lower_614

theorem cell_bound_615 : cellBound ((89520072139/125000000000 : ℚ) : ℝ) ((11489045952349/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_615 potential_upper_616 field_lower_615

theorem cell_bound_616 : cellBound ((11489045952349/16000000000000 : ℚ) : ℝ) ((4601713724651/6400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_616 potential_upper_617 field_lower_616

theorem cell_bound_617 : cellBound ((4601713724651/6400000000000 : ℚ) : ℝ) ((5759761335453/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_617 potential_upper_618 field_lower_617

theorem cell_bound_618 : cellBound ((5759761335453/8000000000000 : ℚ) : ℝ) ((23069522060369/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_618 potential_upper_619 field_lower_618

theorem cell_bound_619 : cellBound ((23069522060369/32000000000000 : ℚ) : ℝ) ((11549999389463/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_619 potential_upper_620 field_lower_619

theorem cell_bound_620 : cellBound ((11549999389463/16000000000000 : ℚ) : ℝ) ((23130475497483/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_620 potential_upper_621 field_lower_620

theorem cell_bound_621 : cellBound ((23130475497483/32000000000000 : ℚ) : ℝ) ((579023805401/800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_621 potential_upper_622 field_lower_621

theorem cell_bound_622 : cellBound ((579023805401/800000000000 : ℚ) : ℝ) ((23191428934597/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_622 potential_upper_623 field_lower_622

theorem cell_bound_623 : cellBound ((23191428934597/32000000000000 : ℚ) : ℝ) ((11610952826577/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_623 potential_upper_624 field_lower_623

end Zeta5AppendixNumerics
