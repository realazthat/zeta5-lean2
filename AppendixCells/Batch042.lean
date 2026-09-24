import CertificateTactics
import AppendixCellBase
import AppendixField.Batch083
import AppendixField.Batch084
import AppendixField.Batch085
import AppendixPotential.Batch084
import AppendixPotential.Batch085
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_672 : cellBound ((106849838184611/128000000000000 : ℚ) : ℝ) ((54051600444471/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_672 potential_upper_673 field_lower_672

theorem cell_bound_673 : cellBound ((54051600444471/64000000000000 : ℚ) : ℝ) ((27652481574401/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_673 potential_upper_674 field_lower_673

theorem cell_bound_674 : cellBound ((27652481574401/32000000000000 : ℚ) : ℝ) ((56558325853133/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_674 potential_upper_675 field_lower_674

theorem cell_bound_675 : cellBound ((56558325853133/64000000000000 : ℚ) : ℝ) ((7226461069683/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_675 potential_upper_676 field_lower_675

theorem cell_bound_676 : cellBound ((7226461069683/8000000000000 : ℚ) : ℝ) ((30159206983063/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_676 potential_upper_677 field_lower_676

theorem cell_bound_677 : cellBound ((30159206983063/32000000000000 : ℚ) : ℝ) ((15706284843697/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_677 potential_upper_678 field_lower_677

theorem cell_bound_678 : cellBound ((15706284843697/16000000000000 : ℚ) : ℝ) ((4239911887007/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_678 potential_upper_679 field_lower_678

theorem cell_bound_679 : cellBound ((4239911887007/4000000000000 : ℚ) : ℝ) ((18213010252359/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_679 potential_upper_680 field_lower_679

theorem cell_bound_680 : cellBound ((18213010252359/16000000000000 : ℚ) : ℝ) ((1946637295669/1600000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_680 potential_upper_681 field_lower_680

theorem cell_bound_681 : cellBound ((1946637295669/1600000000000 : ℚ) : ℝ) ((2746637295669/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_681 potential_upper_682 field_lower_681

theorem cell_bound_682 : cellBound ((2746637295669/2000000000000 : ℚ) : ℝ) ((6746637295669/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_682 potential_upper_683 field_lower_682

theorem cell_bound_683 : cellBound ((6746637295669/4000000000000 : ℚ) : ℝ) ((2/1 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_683 potential_upper_684 field_lower_683

end Zeta5AppendixNumerics
