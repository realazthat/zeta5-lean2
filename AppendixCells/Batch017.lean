import CertificateTactics
import AppendixCellBase
import AppendixField.Batch033
import AppendixField.Batch034
import AppendixField.Batch035
import AppendixPotential.Batch034
import AppendixPotential.Batch035
import AppendixPotential.Batch036
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_272 : cellBound ((7220147100329/32000000000000 : ℚ) : ℝ) ((2894882863549/12800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_272 potential_upper_273 field_lower_272

theorem cell_bound_273 : cellBound ((2894882863549/12800000000000 : ℚ) : ℝ) ((906783402177/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_273 potential_upper_274 field_lower_273

theorem cell_bound_274 : cellBound ((906783402177/4000000000000 : ℚ) : ℝ) ((14542654551919/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_274 potential_upper_275 field_lower_274

theorem cell_bound_275 : cellBound ((14542654551919/64000000000000 : ℚ) : ℝ) ((7288387334503/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_275 potential_upper_276 field_lower_275

theorem cell_bound_276 : cellBound ((7288387334503/32000000000000 : ℚ) : ℝ) ((732250745159/3200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_276 potential_upper_277 field_lower_276

theorem cell_bound_277 : cellBound ((732250745159/3200000000000 : ℚ) : ℝ) ((7356627568677/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_277 potential_upper_278 field_lower_277

theorem cell_bound_278 : cellBound ((7356627568677/32000000000000 : ℚ) : ℝ) ((1847686921441/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_278 potential_upper_279 field_lower_278

theorem cell_bound_279 : cellBound ((1847686921441/8000000000000 : ℚ) : ℝ) ((7424867802851/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_279 potential_upper_280 field_lower_279

theorem cell_bound_280 : cellBound ((7424867802851/32000000000000 : ℚ) : ℝ) ((3729493959969/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_280 potential_upper_281 field_lower_280

theorem cell_bound_281 : cellBound ((3729493959969/16000000000000 : ℚ) : ℝ) ((299724321481/1280000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_281 potential_upper_282 field_lower_281

theorem cell_bound_282 : cellBound ((299724321481/1280000000000 : ℚ) : ℝ) ((29403234977/125000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_282 potential_upper_283 field_lower_282

theorem cell_bound_283 : cellBound ((29403234977/125000000000 : ℚ) : ℝ) ((7561348271199/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_283 potential_upper_284 field_lower_283

theorem cell_bound_284 : cellBound ((7561348271199/32000000000000 : ℚ) : ℝ) ((3797734194143/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_284 potential_upper_285 field_lower_284

theorem cell_bound_285 : cellBound ((3797734194143/16000000000000 : ℚ) : ℝ) ((383185431123/1600000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_285 potential_upper_286 field_lower_285

theorem cell_bound_286 : cellBound ((383185431123/1600000000000 : ℚ) : ℝ) ((3865974428317/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_286 potential_upper_287 field_lower_286

theorem cell_bound_287 : cellBound ((3865974428317/16000000000000 : ℚ) : ℝ) ((975023636351/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_287 potential_upper_288 field_lower_287

end Zeta5AppendixNumerics
