import CertificateTactics
import AppendixCellBase
import AppendixField.Batch021
import AppendixField.Batch022
import AppendixField.Batch023
import AppendixPotential.Batch022
import AppendixPotential.Batch023
import AppendixPotential.Batch024
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_176 : cellBound ((465191185897/4000000000000 : ℚ) : ℝ) ((3743951831963/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_176 potential_upper_177 field_lower_176

theorem cell_bound_177 : cellBound ((3743951831963/32000000000000 : ℚ) : ℝ) ((15065496707/128000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_177 potential_upper_178 field_lower_177

theorem cell_bound_178 : cellBound ((15065496707/128000000000 : ℚ) : ℝ) ((3788796521537/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_178 potential_upper_179 field_lower_178

theorem cell_bound_179 : cellBound ((3788796521537/32000000000000 : ℚ) : ℝ) ((952804716581/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_179 potential_upper_180 field_lower_179

theorem cell_bound_180 : cellBound ((952804716581/8000000000000 : ℚ) : ℝ) ((3833641211111/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_180 potential_upper_181 field_lower_180

theorem cell_bound_181 : cellBound ((3833641211111/32000000000000 : ℚ) : ℝ) ((1928031777949/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_181 potential_upper_182 field_lower_181

theorem cell_bound_182 : cellBound ((1928031777949/16000000000000 : ℚ) : ℝ) ((121903382671/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_182 potential_upper_183 field_lower_182

theorem cell_bound_183 : cellBound ((121903382671/1000000000000 : ℚ) : ℝ) ((1972876467523/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_183 potential_upper_184 field_lower_183

theorem cell_bound_184 : cellBound ((1972876467523/16000000000000 : ℚ) : ℝ) ((199529881231/1600000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_184 potential_upper_185 field_lower_184

theorem cell_bound_185 : cellBound ((199529881231/1600000000000 : ℚ) : ℝ) ((2017721157097/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_185 potential_upper_186 field_lower_185

theorem cell_bound_186 : cellBound ((2017721157097/16000000000000 : ℚ) : ℝ) ((510035875471/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_186 potential_upper_187 field_lower_186

theorem cell_bound_187 : cellBound ((510035875471/4000000000000 : ℚ) : ℝ) ((1042494095729/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_187 potential_upper_188 field_lower_187

theorem cell_bound_188 : cellBound ((1042494095729/8000000000000 : ℚ) : ℝ) ((266229110129/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_188 potential_upper_189 field_lower_188

theorem cell_bound_189 : cellBound ((266229110129/2000000000000 : ℚ) : ℝ) ((110976113009/800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_189 potential_upper_190 field_lower_189

theorem cell_bound_190 : cellBound ((110976113009/800000000000 : ℚ) : ℝ) ((72162863729/500000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_190 potential_upper_191 field_lower_190

theorem cell_bound_191 : cellBound ((72162863729/500000000000 : ℚ) : ℝ) ((4675203313927/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_191 potential_upper_192 field_lower_191

end Zeta5AppendixNumerics
