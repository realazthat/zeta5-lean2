import CertificateTactics
import AppendixCellBase
import AppendixField.Batch059
import AppendixField.Batch060
import AppendixField.Batch061
import AppendixPotential.Batch060
import AppendixPotential.Batch061
import AppendixPotential.Batch062
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_480 : cellBound ((2142134468079/4000000000000 : ℚ) : ℝ) ((68628189860563/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_480 potential_upper_481 field_lower_480

theorem cell_bound_481 : cellBound ((68628189860563/128000000000000 : ℚ) : ℝ) ((34354038371299/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_481 potential_upper_482 field_lower_481

theorem cell_bound_482 : cellBound ((34354038371299/64000000000000 : ℚ) : ℝ) ((68787963624633/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_482 potential_upper_483 field_lower_482

theorem cell_bound_483 : cellBound ((68787963624633/128000000000000 : ℚ) : ℝ) ((17216962626667/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_483 potential_upper_484 field_lower_483

theorem cell_bound_484 : cellBound ((17216962626667/32000000000000 : ℚ) : ℝ) ((68947737388703/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_484 potential_upper_485 field_lower_484

theorem cell_bound_485 : cellBound ((68947737388703/128000000000000 : ℚ) : ℝ) ((34513812135369/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_485 potential_upper_486 field_lower_485

theorem cell_bound_486 : cellBound ((34513812135369/64000000000000 : ℚ) : ℝ) ((69107511152773/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_486 potential_upper_487 field_lower_486

theorem cell_bound_487 : cellBound ((69107511152773/128000000000000 : ℚ) : ℝ) ((8648424754351/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_487 potential_upper_488 field_lower_487

theorem cell_bound_488 : cellBound ((8648424754351/16000000000000 : ℚ) : ℝ) ((69267284916843/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_488 potential_upper_489 field_lower_488

theorem cell_bound_489 : cellBound ((69267284916843/128000000000000 : ℚ) : ℝ) ((34673585899439/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_489 potential_upper_490 field_lower_489

theorem cell_bound_490 : cellBound ((34673585899439/64000000000000 : ℚ) : ℝ) ((69427058680913/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_490 potential_upper_491 field_lower_490

theorem cell_bound_491 : cellBound ((69427058680913/128000000000000 : ℚ) : ℝ) ((17376736390737/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_491 potential_upper_492 field_lower_491

theorem cell_bound_492 : cellBound ((17376736390737/32000000000000 : ℚ) : ℝ) ((69586832444983/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_492 potential_upper_493 field_lower_492

theorem cell_bound_493 : cellBound ((69586832444983/128000000000000 : ℚ) : ℝ) ((34833359663509/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_493 potential_upper_494 field_lower_493

theorem cell_bound_494 : cellBound ((34833359663509/64000000000000 : ℚ) : ℝ) ((69746606209053/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_494 potential_upper_495 field_lower_494

theorem cell_bound_495 : cellBound ((69746606209053/128000000000000 : ℚ) : ℝ) ((4364155818193/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_495 potential_upper_496 field_lower_495

end Zeta5AppendixNumerics
