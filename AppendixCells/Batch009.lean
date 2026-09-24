import CertificateTactics
import AppendixCellBase
import AppendixField.Batch017
import AppendixField.Batch018
import AppendixField.Batch019
import AppendixPotential.Batch018
import AppendixPotential.Batch019
import AppendixPotential.Batch020
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_144 : cellBound ((762218354751/8000000000000 : ℚ) : ℝ) ((24870259471/250000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_144 potential_upper_145 field_lower_144

theorem cell_bound_145 : cellBound ((24870259471/250000000000 : ℚ) : ℝ) ((1614118950931/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_145 potential_upper_146 field_lower_145

theorem cell_bound_146 : cellBound ((1614118950931/16000000000000 : ℚ) : ℝ) ((818270647859/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_146 potential_upper_147 field_lower_146

theorem cell_bound_147 : cellBound ((818270647859/8000000000000 : ℚ) : ℝ) ((331792728101/3200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_147 potential_upper_148 field_lower_147

theorem cell_bound_148 : cellBound ((331792728101/3200000000000 : ℚ) : ℝ) ((3340349625797/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_148 potential_upper_149 field_lower_148

theorem cell_bound_149 : cellBound ((3340349625797/32000000000000 : ℚ) : ℝ) ((420346496323/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_149 potential_upper_150 field_lower_149

theorem cell_bound_150 : cellBound ((420346496323/4000000000000 : ℚ) : ℝ) ((3385194315371/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_150 potential_upper_151 field_lower_150

theorem cell_bound_151 : cellBound ((3385194315371/32000000000000 : ℚ) : ℝ) ((1703808330079/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_151 potential_upper_152 field_lower_151

theorem cell_bound_152 : cellBound ((1703808330079/16000000000000 : ℚ) : ℝ) ((686007800989/6400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_152 potential_upper_153 field_lower_152

theorem cell_bound_153 : cellBound ((686007800989/6400000000000 : ℚ) : ℝ) ((863115337433/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_153 potential_upper_154 field_lower_153

theorem cell_bound_154 : cellBound ((863115337433/8000000000000 : ℚ) : ℝ) ((6927345044251/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_154 potential_upper_155 field_lower_154

theorem cell_bound_155 : cellBound ((6927345044251/64000000000000 : ℚ) : ℝ) ((3474883694519/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_155 potential_upper_156 field_lower_155

theorem cell_bound_156 : cellBound ((3474883694519/32000000000000 : ℚ) : ℝ) ((278887589353/2560000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_156 potential_upper_157 field_lower_156

theorem cell_bound_157 : cellBound ((278887589353/2560000000000 : ℚ) : ℝ) ((1748653019653/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_157 potential_upper_158 field_lower_157

theorem cell_bound_158 : cellBound ((1748653019653/16000000000000 : ℚ) : ℝ) ((7017034423399/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_158 potential_upper_159 field_lower_158

theorem cell_bound_159 : cellBound ((7017034423399/64000000000000 : ℚ) : ℝ) ((3519728384093/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_159 potential_upper_160 field_lower_159

end Zeta5AppendixNumerics
