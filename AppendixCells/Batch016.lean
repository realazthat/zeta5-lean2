import CertificateTactics
import AppendixCellBase
import AppendixField.Batch031
import AppendixField.Batch032
import AppendixField.Batch033
import AppendixPotential.Batch032
import AppendixPotential.Batch033
import AppendixPotential.Batch034
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_256 : cellBound ((6947186163633/32000000000000 : ℚ) : ℝ) ((13928492444353/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_256 potential_upper_257 field_lower_256

theorem cell_bound_257 : cellBound ((13928492444353/64000000000000 : ℚ) : ℝ) ((87266328509/400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_257 potential_upper_258 field_lower_257

theorem cell_bound_258 : cellBound ((87266328509/400000000000 : ℚ) : ℝ) ((13996732678527/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_258 potential_upper_259 field_lower_258

theorem cell_bound_259 : cellBound ((13996732678527/64000000000000 : ℚ) : ℝ) ((7015426397807/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_259 potential_upper_260 field_lower_259

theorem cell_bound_260 : cellBound ((7015426397807/32000000000000 : ℚ) : ℝ) ((14064972912701/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_260 potential_upper_261 field_lower_260

theorem cell_bound_261 : cellBound ((14064972912701/64000000000000 : ℚ) : ℝ) ((3524773257447/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_261 potential_upper_262 field_lower_261

theorem cell_bound_262 : cellBound ((3524773257447/16000000000000 : ℚ) : ℝ) ((4522628207/20480000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_262 potential_upper_263 field_lower_262

theorem cell_bound_263 : cellBound ((4522628207/20480000000 : ℚ) : ℝ) ((7083666631981/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_263 potential_upper_264 field_lower_263

theorem cell_bound_264 : cellBound ((7083666631981/32000000000000 : ℚ) : ℝ) ((14201453381049/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_264 potential_upper_265 field_lower_264

theorem cell_bound_265 : cellBound ((14201453381049/64000000000000 : ℚ) : ℝ) ((1779446687267/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_265 potential_upper_266 field_lower_265

theorem cell_bound_266 : cellBound ((1779446687267/8000000000000 : ℚ) : ℝ) ((14269693615223/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_266 potential_upper_267 field_lower_266

theorem cell_bound_267 : cellBound ((14269693615223/64000000000000 : ℚ) : ℝ) ((1430381373231/6400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_267 potential_upper_268 field_lower_267

theorem cell_bound_268 : cellBound ((1430381373231/6400000000000 : ℚ) : ℝ) ((14337933849397/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_268 potential_upper_269 field_lower_268

theorem cell_bound_269 : cellBound ((14337933849397/64000000000000 : ℚ) : ℝ) ((3593013491621/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_269 potential_upper_270 field_lower_269

theorem cell_bound_270 : cellBound ((3593013491621/16000000000000 : ℚ) : ℝ) ((14406174083571/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_270 potential_upper_271 field_lower_270

theorem cell_bound_271 : cellBound ((14406174083571/64000000000000 : ℚ) : ℝ) ((7220147100329/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_271 potential_upper_272 field_lower_271

end Zeta5AppendixNumerics
