import CertificateTactics
import AppendixCellBase
import AppendixField.Batch047
import AppendixField.Batch048
import AppendixField.Batch049
import AppendixPotential.Batch048
import AppendixPotential.Batch049
import AppendixPotential.Batch050
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_384 : cellBound ((24306660222459/64000000000000 : ℚ) : ℝ) ((48697037595177/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_384 potential_upper_385 field_lower_384

theorem cell_bound_385 : cellBound ((48697037595177/128000000000000 : ℚ) : ℝ) ((12195188686359/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_385 potential_upper_386 field_lower_385

theorem cell_bound_386 : cellBound ((12195188686359/32000000000000 : ℚ) : ℝ) ((9772894379139/25600000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_386 potential_upper_387 field_lower_386

theorem cell_bound_387 : cellBound ((9772894379139/25600000000000 : ℚ) : ℝ) ((24474094522977/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_387 potential_upper_388 field_lower_387

theorem cell_bound_388 : cellBound ((24474094522977/64000000000000 : ℚ) : ℝ) ((6139452918309/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_388 potential_upper_389 field_lower_388

theorem cell_bound_389 : cellBound ((6139452918309/16000000000000 : ℚ) : ℝ) ((4928305764699/12800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_389 potential_upper_390 field_lower_389

theorem cell_bound_390 : cellBound ((4928305764699/12800000000000 : ℚ) : ℝ) ((12362622986877/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_390 potential_upper_391 field_lower_390

theorem cell_bound_391 : cellBound ((12362622986877/32000000000000 : ℚ) : ℝ) ((24808963124013/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_391 potential_upper_392 field_lower_391

theorem cell_bound_392 : cellBound ((24808963124013/64000000000000 : ℚ) : ℝ) ((777896258571/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_392 potential_upper_393 field_lower_392

theorem cell_bound_393 : cellBound ((777896258571/2000000000000 : ℚ) : ℝ) ((24976397424531/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_393 potential_upper_394 field_lower_393

theorem cell_bound_394 : cellBound ((24976397424531/64000000000000 : ℚ) : ℝ) ((2506011457479/6400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_394 potential_upper_395 field_lower_394

theorem cell_bound_395 : cellBound ((2506011457479/6400000000000 : ℚ) : ℝ) ((25143831725049/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_395 potential_upper_396 field_lower_395

theorem cell_bound_396 : cellBound ((25143831725049/64000000000000 : ℚ) : ℝ) ((6306887218827/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_396 potential_upper_397 field_lower_396

theorem cell_bound_397 : cellBound ((6306887218827/16000000000000 : ℚ) : ℝ) ((12697491587913/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_397 potential_upper_398 field_lower_397

theorem cell_bound_398 : cellBound ((12697491587913/32000000000000 : ℚ) : ℝ) ((3195302184543/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_398 potential_upper_399 field_lower_398

theorem cell_bound_399 : cellBound ((3195302184543/8000000000000 : ℚ) : ℝ) ((12864925888431/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_399 potential_upper_400 field_lower_399

end Zeta5AppendixNumerics
