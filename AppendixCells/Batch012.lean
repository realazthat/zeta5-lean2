import CertificateTactics
import AppendixCellBase
import AppendixField.Batch023
import AppendixField.Batch024
import AppendixField.Batch025
import AppendixPotential.Batch024
import AppendixPotential.Batch025
import AppendixPotential.Batch026
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_192 : cellBound ((4675203313927/32000000000000 : ℚ) : ℝ) ((2365991674599/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_192 potential_upper_193 field_lower_192

theorem cell_bound_193 : cellBound ((2365991674599/16000000000000 : ℚ) : ℝ) ((4788763384469/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_193 potential_upper_194 field_lower_193

theorem cell_bound_194 : cellBound ((4788763384469/32000000000000 : ℚ) : ℝ) ((9634306804209/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_194 potential_upper_195 field_lower_194

theorem cell_bound_195 : cellBound ((9634306804209/64000000000000 : ℚ) : ℝ) ((242277170987/1600000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_195 potential_upper_196 field_lower_195

theorem cell_bound_196 : cellBound ((242277170987/1600000000000 : ℚ) : ℝ) ((9747866874751/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_196 potential_upper_197 field_lower_196

theorem cell_bound_197 : cellBound ((9747866874751/64000000000000 : ℚ) : ℝ) ((4902323455011/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_197 potential_upper_198 field_lower_197

theorem cell_bound_198 : cellBound ((4902323455011/32000000000000 : ℚ) : ℝ) ((9861426945293/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_198 potential_upper_199 field_lower_198

theorem cell_bound_199 : cellBound ((9861426945293/64000000000000 : ℚ) : ℝ) ((2479551745141/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_199 potential_upper_200 field_lower_199

theorem cell_bound_200 : cellBound ((2479551745141/16000000000000 : ℚ) : ℝ) ((19893193996399/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_200 potential_upper_201 field_lower_200

theorem cell_bound_201 : cellBound ((19893193996399/128000000000000 : ℚ) : ℝ) ((1994997403167/12800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_201 potential_upper_202 field_lower_201

theorem cell_bound_202 : cellBound ((1994997403167/12800000000000 : ℚ) : ℝ) ((20006754066941/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_202 potential_upper_203 field_lower_202

theorem cell_bound_203 : cellBound ((20006754066941/128000000000000 : ℚ) : ℝ) ((5015883525553/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_203 potential_upper_204 field_lower_203

theorem cell_bound_204 : cellBound ((5015883525553/32000000000000 : ℚ) : ℝ) ((20120314137483/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_204 potential_upper_205 field_lower_204

theorem cell_bound_205 : cellBound ((20120314137483/128000000000000 : ℚ) : ℝ) ((10088547086377/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_205 potential_upper_206 field_lower_205

theorem cell_bound_206 : cellBound ((10088547086377/64000000000000 : ℚ) : ℝ) ((809354968321/5120000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_206 potential_upper_207 field_lower_206

theorem cell_bound_207 : cellBound ((809354968321/5120000000000 : ℚ) : ℝ) ((634082945103/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_207 potential_upper_208 field_lower_207

end Zeta5AppendixNumerics
