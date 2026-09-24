import CertificateTactics
import AppendixCellBase
import AppendixField.Batch029
import AppendixField.Batch030
import AppendixField.Batch031
import AppendixPotential.Batch030
import AppendixPotential.Batch031
import AppendixPotential.Batch032
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_240 : cellBound ((1552066066561/8000000000000 : ℚ) : ℝ) ((201105762729/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_240 potential_upper_241 field_lower_240

theorem cell_bound_241 : cellBound ((201105762729/1000000000000 : ℚ) : ℝ) ((3251812320751/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_241 potential_upper_242 field_lower_241

theorem cell_bound_242 : cellBound ((3251812320751/16000000000000 : ℚ) : ℝ) ((1642966218919/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_242 potential_upper_243 field_lower_242

theorem cell_bound_243 : cellBound ((1642966218919/8000000000000 : ℚ) : ℝ) ((132802102197/640000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_243 potential_upper_244 field_lower_243

theorem cell_bound_244 : cellBound ((132802102197/640000000000 : ℚ) : ℝ) ((6674225226937/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_244 potential_upper_245 field_lower_244

theorem cell_bound_245 : cellBound ((6674225226937/32000000000000 : ℚ) : ℝ) ((838543168003/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_245 potential_upper_246 field_lower_245

theorem cell_bound_246 : cellBound ((838543168003/4000000000000 : ℚ) : ℝ) ((6742465461111/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_246 potential_upper_247 field_lower_246

theorem cell_bound_247 : cellBound ((6742465461111/32000000000000 : ℚ) : ℝ) ((3388292789099/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_247 potential_upper_248 field_lower_247

theorem cell_bound_248 : cellBound ((3388292789099/16000000000000 : ℚ) : ℝ) ((1362141139057/6400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_248 potential_upper_249 field_lower_248

theorem cell_bound_249 : cellBound ((1362141139057/6400000000000 : ℚ) : ℝ) ((1711206453093/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_249 potential_upper_250 field_lower_249

theorem cell_bound_250 : cellBound ((1711206453093/8000000000000 : ℚ) : ℝ) ((13723771741831/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_250 potential_upper_251 field_lower_250

theorem cell_bound_251 : cellBound ((13723771741831/64000000000000 : ℚ) : ℝ) ((6878945929459/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_251 potential_upper_252 field_lower_251

theorem cell_bound_252 : cellBound ((6878945929459/32000000000000 : ℚ) : ℝ) ((2758402395201/12800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_252 potential_upper_253 field_lower_252

theorem cell_bound_253 : cellBound ((2758402395201/12800000000000 : ℚ) : ℝ) ((3456533023273/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_253 potential_upper_254 field_lower_253

theorem cell_bound_254 : cellBound ((3456533023273/16000000000000 : ℚ) : ℝ) ((13860252210179/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_254 potential_upper_255 field_lower_254

theorem cell_bound_255 : cellBound ((13860252210179/64000000000000 : ℚ) : ℝ) ((6947186163633/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_255 potential_upper_256 field_lower_255

end Zeta5AppendixNumerics
