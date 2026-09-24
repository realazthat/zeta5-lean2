import CertificateTactics
import AppendixCellBase
import AppendixField.Batch027
import AppendixField.Batch028
import AppendixField.Batch029
import AppendixPotential.Batch028
import AppendixPotential.Batch029
import AppendixPotential.Batch030
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_224 : cellBound ((1324945925477/8000000000000 : ℚ) : ℝ) ((10656347439087/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_224 potential_upper_225 field_lower_224

theorem cell_bound_225 : cellBound ((10656347439087/64000000000000 : ℚ) : ℝ) ((5356563737179/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_225 potential_upper_226 field_lower_225

theorem cell_bound_226 : cellBound ((5356563737179/32000000000000 : ℚ) : ℝ) ((10769907509629/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_226 potential_upper_227 field_lower_226

theorem cell_bound_227 : cellBound ((10769907509629/64000000000000 : ℚ) : ℝ) ((108266875449/640000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_227 potential_upper_228 field_lower_227

theorem cell_bound_228 : cellBound ((108266875449/640000000000 : ℚ) : ℝ) ((10883467580171/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_228 potential_upper_229 field_lower_228

theorem cell_bound_229 : cellBound ((10883467580171/64000000000000 : ℚ) : ℝ) ((5470123807721/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_229 potential_upper_230 field_lower_229

theorem cell_bound_230 : cellBound ((5470123807721/32000000000000 : ℚ) : ℝ) ((10997027650713/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_230 potential_upper_231 field_lower_230

theorem cell_bound_231 : cellBound ((10997027650713/64000000000000 : ℚ) : ℝ) ((345431490187/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_231 potential_upper_232 field_lower_231

theorem cell_bound_232 : cellBound ((345431490187/2000000000000 : ℚ) : ℝ) ((5583683878263/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_232 potential_upper_233 field_lower_232

theorem cell_bound_233 : cellBound ((5583683878263/32000000000000 : ℚ) : ℝ) ((2820231956767/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_233 potential_upper_234 field_lower_233

theorem cell_bound_234 : cellBound ((2820231956767/16000000000000 : ℚ) : ℝ) ((1139448789761/6400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_234 potential_upper_235 field_lower_234

theorem cell_bound_235 : cellBound ((1139448789761/6400000000000 : ℚ) : ℝ) ((1438505996019/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_235 potential_upper_236 field_lower_235

theorem cell_bound_236 : cellBound ((1438505996019/8000000000000 : ℚ) : ℝ) ((2933792027309/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_236 potential_upper_237 field_lower_236

theorem cell_bound_237 : cellBound ((2933792027309/16000000000000 : ℚ) : ℝ) ((149528603129/800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_237 potential_upper_238 field_lower_237

theorem cell_bound_238 : cellBound ((149528603129/800000000000 : ℚ) : ℝ) ((3047352097851/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_238 potential_upper_239 field_lower_238

theorem cell_bound_239 : cellBound ((3047352097851/16000000000000 : ℚ) : ℝ) ((1552066066561/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_239 potential_upper_240 field_lower_239

end Zeta5AppendixNumerics
