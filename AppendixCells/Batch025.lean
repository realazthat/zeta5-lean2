import CertificateTactics
import AppendixCellBase
import AppendixField.Batch049
import AppendixField.Batch050
import AppendixField.Batch051
import AppendixPotential.Batch050
import AppendixPotential.Batch051
import AppendixPotential.Batch052
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_400 : cellBound ((12864925888431/32000000000000 : ℚ) : ℝ) ((1294864303869/3200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_400 potential_upper_401 field_lower_400

theorem cell_bound_401 : cellBound ((1294864303869/3200000000000 : ℚ) : ℝ) ((13032360188949/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_401 potential_upper_402 field_lower_401

theorem cell_bound_402 : cellBound ((13032360188949/32000000000000 : ℚ) : ℝ) ((1639509667401/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_402 potential_upper_403 field_lower_402

theorem cell_bound_403 : cellBound ((1639509667401/4000000000000 : ℚ) : ℝ) ((6641755819863/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_403 potential_upper_404 field_lower_403

theorem cell_bound_404 : cellBound ((6641755819863/16000000000000 : ℚ) : ℝ) ((3362736485061/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_404 potential_upper_405 field_lower_404

theorem cell_bound_405 : cellBound ((3362736485061/8000000000000 : ℚ) : ℝ) ((6809190120381/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_405 potential_upper_406 field_lower_405

theorem cell_bound_406 : cellBound ((6809190120381/16000000000000 : ℚ) : ℝ) ((86161340883/200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_406 potential_upper_407 field_lower_406

theorem cell_bound_407 : cellBound ((86161340883/200000000000 : ℚ) : ℝ) ((54181913021/125000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_407 potential_upper_408 field_lower_407

theorem cell_bound_408 : cellBound ((54181913021/125000000000 : ℚ) : ℝ) ((436103903921/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_408 potential_upper_409 field_lower_408

theorem cell_bound_409 : cellBound ((436103903921/1000000000000 : ℚ) : ℝ) ((219376251837/500000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_409 potential_upper_410 field_lower_409

theorem cell_bound_410 : cellBound ((219376251837/500000000000 : ℚ) : ℝ) ((880153607101/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_410 potential_upper_411 field_lower_410

theorem cell_bound_411 : cellBound ((880153607101/2000000000000 : ℚ) : ℝ) ((441401103427/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_411 potential_upper_412 field_lower_411

theorem cell_bound_412 : cellBound ((441401103427/1000000000000 : ℚ) : ℝ) ((885450806607/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_412 potential_upper_413 field_lower_412

theorem cell_bound_413 : cellBound ((885450806607/2000000000000 : ℚ) : ℝ) ((22202485159/50000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_413 potential_upper_414 field_lower_413

theorem cell_bound_414 : cellBound ((22202485159/50000000000 : ℚ) : ℝ) ((890748006113/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_414 potential_upper_415 field_lower_414

theorem cell_bound_415 : cellBound ((890748006113/2000000000000 : ℚ) : ℝ) ((446698302933/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_415 potential_upper_416 field_lower_415

end Zeta5AppendixNumerics
