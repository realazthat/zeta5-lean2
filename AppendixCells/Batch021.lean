import CertificateTactics
import AppendixCellBase
import AppendixField.Batch041
import AppendixField.Batch042
import AppendixField.Batch043
import AppendixPotential.Batch042
import AppendixPotential.Batch043
import AppendixPotential.Batch044
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_336 : cellBound ((3929638815327/12800000000000 : ℚ) : ℝ) ((616435551059/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_336 potential_upper_337 field_lower_336

theorem cell_bound_337 : cellBound ((616435551059/2000000000000 : ℚ) : ℝ) ((19803681191141/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_337 potential_upper_338 field_lower_337

theorem cell_bound_338 : cellBound ((19803681191141/64000000000000 : ℚ) : ℝ) ((9940712374197/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_338 potential_upper_339 field_lower_338

theorem cell_bound_339 : cellBound ((9940712374197/32000000000000 : ℚ) : ℝ) ((200369118629/640000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_339 potential_upper_340 field_lower_339

theorem cell_bound_340 : cellBound ((200369118629/640000000000 : ℚ) : ℝ) ((10096199488703/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_340 potential_upper_341 field_lower_340

theorem cell_bound_341 : cellBound ((10096199488703/32000000000000 : ℚ) : ℝ) ((2543485761489/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_341 potential_upper_342 field_lower_341

theorem cell_bound_342 : cellBound ((2543485761489/8000000000000 : ℚ) : ℝ) ((10251686603209/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_342 potential_upper_343 field_lower_342

theorem cell_bound_343 : cellBound ((10251686603209/32000000000000 : ℚ) : ℝ) ((5164715080231/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_343 potential_upper_344 field_lower_343

theorem cell_bound_344 : cellBound ((5164715080231/16000000000000 : ℚ) : ℝ) ((1310614659371/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_344 potential_upper_345 field_lower_344

theorem cell_bound_345 : cellBound ((1310614659371/4000000000000 : ℚ) : ℝ) ((5320202194737/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_345 potential_upper_346 field_lower_345

theorem cell_bound_346 : cellBound ((5320202194737/16000000000000 : ℚ) : ℝ) ((539794575199/1600000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_346 potential_upper_347 field_lower_346

theorem cell_bound_347 : cellBound ((539794575199/1600000000000 : ℚ) : ℝ) ((5475689309243/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_347 potential_upper_348 field_lower_347

theorem cell_bound_348 : cellBound ((5475689309243/16000000000000 : ℚ) : ℝ) ((86772388539/250000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_348 potential_upper_349 field_lower_348

theorem cell_bound_349 : cellBound ((86772388539/250000000000 : ℚ) : ℝ) ((11190582883251/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_349 potential_upper_350 field_lower_349

theorem cell_bound_350 : cellBound ((11190582883251/32000000000000 : ℚ) : ℝ) ((1127430003351/3200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_350 potential_upper_351 field_lower_350

theorem cell_bound_351 : cellBound ((1127430003351/3200000000000 : ℚ) : ℝ) ((11358017183769/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_351 potential_upper_352 field_lower_351

end Zeta5AppendixNumerics
