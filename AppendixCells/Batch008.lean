import CertificateTactics
import AppendixCellBase
import AppendixField.Batch015
import AppendixField.Batch016
import AppendixField.Batch017
import AppendixPotential.Batch016
import AppendixPotential.Batch017
import AppendixPotential.Batch018
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_128 : cellBound ((1221767174613/16000000000000 : ℚ) : ℝ) ((4920698646773/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_128 potential_upper_129 field_lower_128

theorem cell_bound_129 : cellBound ((4920698646773/64000000000000 : ℚ) : ℝ) ((2477164297547/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_129 potential_upper_130 field_lower_129

theorem cell_bound_130 : cellBound ((2477164297547/32000000000000 : ℚ) : ℝ) ((997591708683/12800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_130 potential_upper_131 field_lower_130

theorem cell_bound_131 : cellBound ((997591708683/12800000000000 : ℚ) : ℝ) ((627698561467/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_131 potential_upper_132 field_lower_131

theorem cell_bound_132 : cellBound ((627698561467/8000000000000 : ℚ) : ℝ) ((5055218440057/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_132 potential_upper_133 field_lower_132

theorem cell_bound_133 : cellBound ((5055218440057/64000000000000 : ℚ) : ℝ) ((2544424194189/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_133 potential_upper_134 field_lower_133

theorem cell_bound_134 : cellBound ((2544424194189/32000000000000 : ℚ) : ℝ) ((5122478336699/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_134 potential_upper_135 field_lower_134

theorem cell_bound_135 : cellBound ((5122478336699/64000000000000 : ℚ) : ℝ) ((257805414251/3200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_135 potential_upper_136 field_lower_135

theorem cell_bound_136 : cellBound ((257805414251/3200000000000 : ℚ) : ℝ) ((2611684090831/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_136 potential_upper_137 field_lower_136

theorem cell_bound_137 : cellBound ((2611684090831/32000000000000 : ℚ) : ℝ) ((165332127447/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_137 potential_upper_138 field_lower_137

theorem cell_bound_138 : cellBound ((165332127447/2000000000000 : ℚ) : ℝ) ((2678943987473/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_138 potential_upper_139 field_lower_138

theorem cell_bound_139 : cellBound ((2678943987473/32000000000000 : ℚ) : ℝ) ((1356286967897/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_139 potential_upper_140 field_lower_139

theorem cell_bound_140 : cellBound ((1356286967897/16000000000000 : ℚ) : ℝ) ((694958458109/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_140 potential_upper_141 field_lower_140

theorem cell_bound_141 : cellBound ((694958458109/8000000000000 : ℚ) : ℝ) ((1423546864539/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_141 potential_upper_142 field_lower_141

theorem cell_bound_142 : cellBound ((1423546864539/16000000000000 : ℚ) : ℝ) ((72858840643/800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_142 potential_upper_143 field_lower_142

theorem cell_bound_143 : cellBound ((72858840643/800000000000 : ℚ) : ℝ) ((762218354751/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_143 potential_upper_144 field_lower_143

end Zeta5AppendixNumerics
