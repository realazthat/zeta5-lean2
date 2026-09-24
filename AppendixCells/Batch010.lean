import CertificateTactics
import AppendixCellBase
import AppendixField.Batch019
import AppendixField.Batch020
import AppendixField.Batch021
import AppendixPotential.Batch020
import AppendixPotential.Batch021
import AppendixPotential.Batch022
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_160 : cellBound ((3519728384093/32000000000000 : ℚ) : ℝ) ((7061879112973/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_160 potential_upper_161 field_lower_160

theorem cell_bound_161 : cellBound ((7061879112973/64000000000000 : ℚ) : ℝ) ((44276884111/400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_161 potential_upper_162 field_lower_161

theorem cell_bound_162 : cellBound ((44276884111/400000000000 : ℚ) : ℝ) ((7106723802547/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_162 potential_upper_163 field_lower_162

theorem cell_bound_163 : cellBound ((7106723802547/64000000000000 : ℚ) : ℝ) ((3564573073667/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_163 potential_upper_164 field_lower_163

theorem cell_bound_164 : cellBound ((3564573073667/32000000000000 : ℚ) : ℝ) ((7151568492121/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_164 potential_upper_165 field_lower_164

theorem cell_bound_165 : cellBound ((7151568492121/64000000000000 : ℚ) : ℝ) ((1793497709227/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_165 potential_upper_166 field_lower_165

theorem cell_bound_166 : cellBound ((1793497709227/16000000000000 : ℚ) : ℝ) ((1439282636339/12800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_166 potential_upper_167 field_lower_166

theorem cell_bound_167 : cellBound ((1439282636339/12800000000000 : ℚ) : ℝ) ((3609417763241/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_167 potential_upper_168 field_lower_167

theorem cell_bound_168 : cellBound ((3609417763241/32000000000000 : ℚ) : ℝ) ((7241257871269/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_168 potential_upper_169 field_lower_168

theorem cell_bound_169 : cellBound ((7241257871269/64000000000000 : ℚ) : ℝ) ((907960027007/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_169 potential_upper_170 field_lower_169

theorem cell_bound_170 : cellBound ((907960027007/8000000000000 : ℚ) : ℝ) ((7286102560843/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_170 potential_upper_171 field_lower_170

theorem cell_bound_171 : cellBound ((7286102560843/64000000000000 : ℚ) : ℝ) ((730852490563/6400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_171 potential_upper_172 field_lower_171

theorem cell_bound_172 : cellBound ((730852490563/6400000000000 : ℚ) : ℝ) ((7330947250417/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_172 potential_upper_173 field_lower_172

theorem cell_bound_173 : cellBound ((7330947250417/64000000000000 : ℚ) : ℝ) ((1838342398801/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_173 potential_upper_174 field_lower_173

theorem cell_bound_174 : cellBound ((1838342398801/16000000000000 : ℚ) : ℝ) ((3699107142389/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_174 potential_upper_175 field_lower_174

theorem cell_bound_175 : cellBound ((3699107142389/32000000000000 : ℚ) : ℝ) ((465191185897/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_175 potential_upper_176 field_lower_175

end Zeta5AppendixNumerics
