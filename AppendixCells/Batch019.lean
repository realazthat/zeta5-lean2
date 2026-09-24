import CertificateTactics
import AppendixCellBase
import AppendixField.Batch037
import AppendixField.Batch038
import AppendixField.Batch039
import AppendixPotential.Batch038
import AppendixPotential.Batch039
import AppendixPotential.Batch040
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_304 : cellBound ((36419876534909/128000000000000 : ℚ) : ℝ) ((18248810046081/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_304 potential_upper_305 field_lower_304

theorem cell_bound_305 : cellBound ((18248810046081/64000000000000 : ℚ) : ℝ) ((7315072729883/25600000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_305 potential_upper_306 field_lower_305

theorem cell_bound_306 : cellBound ((7315072729883/25600000000000 : ℚ) : ℝ) ((9163276801667/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_306 potential_upper_307 field_lower_306

theorem cell_bound_307 : cellBound ((9163276801667/32000000000000 : ℚ) : ℝ) ((36730850763921/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_307 potential_upper_308 field_lower_307

theorem cell_bound_308 : cellBound ((36730850763921/128000000000000 : ℚ) : ℝ) ((18404297160587/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_308 potential_upper_309 field_lower_308

theorem cell_bound_309 : cellBound ((18404297160587/64000000000000 : ℚ) : ℝ) ((36886337878427/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_309 potential_upper_310 field_lower_309

theorem cell_bound_310 : cellBound ((36886337878427/128000000000000 : ℚ) : ℝ) ((231025508973/800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_310 potential_upper_311 field_lower_310

theorem cell_bound_311 : cellBound ((231025508973/800000000000 : ℚ) : ℝ) ((37041824992933/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_311 potential_upper_312 field_lower_311

theorem cell_bound_312 : cellBound ((37041824992933/128000000000000 : ℚ) : ℝ) ((18559784275093/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_312 potential_upper_313 field_lower_312

theorem cell_bound_313 : cellBound ((18559784275093/64000000000000 : ℚ) : ℝ) ((37197312107439/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_313 potential_upper_314 field_lower_313

theorem cell_bound_314 : cellBound ((37197312107439/128000000000000 : ℚ) : ℝ) ((9318763916173/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_314 potential_upper_315 field_lower_314

theorem cell_bound_315 : cellBound ((9318763916173/32000000000000 : ℚ) : ℝ) ((7470559844389/25600000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_315 potential_upper_316 field_lower_315

theorem cell_bound_316 : cellBound ((7470559844389/25600000000000 : ℚ) : ℝ) ((18715271389599/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_316 potential_upper_317 field_lower_316

theorem cell_bound_317 : cellBound ((18715271389599/64000000000000 : ℚ) : ℝ) ((37508286336451/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_317 potential_upper_318 field_lower_317

theorem cell_bound_318 : cellBound ((37508286336451/128000000000000 : ℚ) : ℝ) ((4698253736713/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_318 potential_upper_319 field_lower_318

theorem cell_bound_319 : cellBound ((4698253736713/16000000000000 : ℚ) : ℝ) ((37663773450957/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_319 potential_upper_320 field_lower_319

end Zeta5AppendixNumerics
