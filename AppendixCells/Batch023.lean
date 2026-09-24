import CertificateTactics
import AppendixCellBase
import AppendixField.Batch045
import AppendixField.Batch046
import AppendixField.Batch047
import AppendixPotential.Batch046
import AppendixPotential.Batch047
import AppendixPotential.Batch048
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_368 : cellBound ((23636923020387/64000000000000 : ℚ) : ℝ) ((47357563191033/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_368 potential_upper_369 field_lower_368

theorem cell_bound_369 : cellBound ((47357563191033/128000000000000 : ℚ) : ℝ) ((11860320085323/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_369 potential_upper_370 field_lower_369

theorem cell_bound_370 : cellBound ((11860320085323/32000000000000 : ℚ) : ℝ) ((47524997491551/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_370 potential_upper_371 field_lower_370

theorem cell_bound_371 : cellBound ((47524997491551/128000000000000 : ℚ) : ℝ) ((4760871464181/12800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_371 potential_upper_372 field_lower_371

theorem cell_bound_372 : cellBound ((4760871464181/12800000000000 : ℚ) : ℝ) ((47692431792069/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_372 potential_upper_373 field_lower_372

theorem cell_bound_373 : cellBound ((47692431792069/128000000000000 : ℚ) : ℝ) ((5972018617791/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_373 potential_upper_374 field_lower_373

theorem cell_bound_374 : cellBound ((5972018617791/16000000000000 : ℚ) : ℝ) ((47859866092587/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_374 potential_upper_375 field_lower_374

theorem cell_bound_375 : cellBound ((47859866092587/128000000000000 : ℚ) : ℝ) ((23971791621423/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_375 potential_upper_376 field_lower_375

theorem cell_bound_376 : cellBound ((23971791621423/64000000000000 : ℚ) : ℝ) ((9605460078621/25600000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_376 potential_upper_377 field_lower_376

theorem cell_bound_377 : cellBound ((9605460078621/25600000000000 : ℚ) : ℝ) ((12027754385841/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_377 potential_upper_378 field_lower_377

theorem cell_bound_378 : cellBound ((12027754385841/32000000000000 : ℚ) : ℝ) ((48194734693623/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_378 potential_upper_379 field_lower_378

theorem cell_bound_379 : cellBound ((48194734693623/128000000000000 : ℚ) : ℝ) ((24139225921941/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_379 potential_upper_380 field_lower_379

theorem cell_bound_380 : cellBound ((24139225921941/64000000000000 : ℚ) : ℝ) ((48362168994141/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_380 potential_upper_381 field_lower_380

theorem cell_bound_381 : cellBound ((48362168994141/128000000000000 : ℚ) : ℝ) ((121114715361/320000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_381 potential_upper_382 field_lower_381

theorem cell_bound_382 : cellBound ((121114715361/320000000000 : ℚ) : ℝ) ((48529603294659/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_382 potential_upper_383 field_lower_382

theorem cell_bound_383 : cellBound ((48529603294659/128000000000000 : ℚ) : ℝ) ((24306660222459/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_383 potential_upper_384 field_lower_383

end Zeta5AppendixNumerics
