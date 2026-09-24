import CertificateTactics
import AppendixCellBase
import AppendixField.Batch051
import AppendixField.Batch052
import AppendixField.Batch053
import AppendixPotential.Batch052
import AppendixPotential.Batch053
import AppendixPotential.Batch054
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_416 : cellBound ((446698302933/1000000000000 : ℚ) : ℝ) ((896045205619/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_416 potential_upper_417 field_lower_416

theorem cell_bound_417 : cellBound ((896045205619/2000000000000 : ℚ) : ℝ) ((1794739010991/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_417 potential_upper_418 field_lower_417

theorem cell_bound_418 : cellBound ((1794739010991/4000000000000 : ℚ) : ℝ) ((224673451343/500000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_418 potential_upper_419 field_lower_418

theorem cell_bound_419 : cellBound ((224673451343/500000000000 : ℚ) : ℝ) ((1800036210497/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_419 potential_upper_420 field_lower_419

theorem cell_bound_420 : cellBound ((1800036210497/4000000000000 : ℚ) : ℝ) ((7210739241/16000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_420 potential_upper_421 field_lower_420

theorem cell_bound_421 : cellBound ((7210739241/16000000000 : ℚ) : ℝ) ((1805333410003/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_421 potential_upper_422 field_lower_421

theorem cell_bound_422 : cellBound ((1805333410003/4000000000000 : ℚ) : ℝ) ((451995502439/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_422 potential_upper_423 field_lower_422

theorem cell_bound_423 : cellBound ((451995502439/1000000000000 : ℚ) : ℝ) ((1810630609509/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_423 potential_upper_424 field_lower_423

theorem cell_bound_424 : cellBound ((1810630609509/4000000000000 : ℚ) : ℝ) ((906639604631/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_424 potential_upper_425 field_lower_424

theorem cell_bound_425 : cellBound ((906639604631/2000000000000 : ℚ) : ℝ) ((363185561803/800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_425 potential_upper_426 field_lower_425

theorem cell_bound_426 : cellBound ((363185561803/800000000000 : ℚ) : ℝ) ((28415256387/62500000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_426 potential_upper_427 field_lower_426

theorem cell_bound_427 : cellBound ((28415256387/62500000000 : ℚ) : ℝ) ((1821225008521/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_427 potential_upper_428 field_lower_427

theorem cell_bound_428 : cellBound ((1821225008521/4000000000000 : ℚ) : ℝ) ((911936804137/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_428 potential_upper_429 field_lower_428

theorem cell_bound_429 : cellBound ((911936804137/2000000000000 : ℚ) : ℝ) ((1826522208027/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_429 potential_upper_430 field_lower_429

theorem cell_bound_430 : cellBound ((1826522208027/4000000000000 : ℚ) : ℝ) ((91458540389/200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_430 potential_upper_431 field_lower_430

theorem cell_bound_431 : cellBound ((91458540389/200000000000 : ℚ) : ℝ) ((1831819407533/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_431 potential_upper_432 field_lower_431

end Zeta5AppendixNumerics
