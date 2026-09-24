import CertificateTactics
import AppendixCellBase
import AppendixField.Batch043
import AppendixField.Batch044
import AppendixField.Batch045
import AppendixPotential.Batch044
import AppendixPotential.Batch045
import AppendixPotential.Batch046
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_352 : cellBound ((11358017183769/32000000000000 : ℚ) : ℝ) ((22799751517797/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_352 potential_upper_353 field_lower_352

theorem cell_bound_353 : cellBound ((22799751517797/64000000000000 : ℚ) : ℝ) ((2860433583507/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_353 potential_upper_354 field_lower_353

theorem cell_bound_354 : cellBound ((2860433583507/8000000000000 : ℚ) : ℝ) ((4593437163663/12800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_354 potential_upper_355 field_lower_354

theorem cell_bound_355 : cellBound ((4593437163663/12800000000000 : ℚ) : ℝ) ((11525451484287/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_355 potential_upper_356 field_lower_355

theorem cell_bound_356 : cellBound ((11525451484287/32000000000000 : ℚ) : ℝ) ((23134620118833/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_356 potential_upper_357 field_lower_356

theorem cell_bound_357 : cellBound ((23134620118833/64000000000000 : ℚ) : ℝ) ((5804584317273/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_357 potential_upper_358 field_lower_357

theorem cell_bound_358 : cellBound ((5804584317273/16000000000000 : ℚ) : ℝ) ((46520391688443/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_358 potential_upper_359 field_lower_358

theorem cell_bound_359 : cellBound ((46520391688443/128000000000000 : ℚ) : ℝ) ((23302054419351/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_359 potential_upper_360 field_lower_359

theorem cell_bound_360 : cellBound ((23302054419351/64000000000000 : ℚ) : ℝ) ((46687825988961/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_360 potential_upper_361 field_lower_360

theorem cell_bound_361 : cellBound ((46687825988961/128000000000000 : ℚ) : ℝ) ((2338577156961/6400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_361 potential_upper_362 field_lower_361

theorem cell_bound_362 : cellBound ((2338577156961/6400000000000 : ℚ) : ℝ) ((46855260289479/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_362 potential_upper_363 field_lower_362

theorem cell_bound_363 : cellBound ((46855260289479/128000000000000 : ℚ) : ℝ) ((23469488719869/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_363 potential_upper_364 field_lower_363

theorem cell_bound_364 : cellBound ((23469488719869/64000000000000 : ℚ) : ℝ) ((47022694589997/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_364 potential_upper_365 field_lower_364

theorem cell_bound_365 : cellBound ((47022694589997/128000000000000 : ℚ) : ℝ) ((1472075366883/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_365 potential_upper_366 field_lower_365

theorem cell_bound_366 : cellBound ((1472075366883/4000000000000 : ℚ) : ℝ) ((9438025778103/25600000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_366 potential_upper_367 field_lower_366

theorem cell_bound_367 : cellBound ((9438025778103/25600000000000 : ℚ) : ℝ) ((23636923020387/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_367 potential_upper_368 field_lower_367

end Zeta5AppendixNumerics
