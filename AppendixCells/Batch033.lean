import CertificateTactics
import AppendixCellBase
import AppendixField.Batch065
import AppendixField.Batch066
import AppendixField.Batch067
import AppendixPotential.Batch066
import AppendixPotential.Batch067
import AppendixPotential.Batch068
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_528 : cellBound ((966476566661/1600000000000 : ℚ) : ℝ) ((38727855271377/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_528 potential_upper_529 field_lower_528

theorem cell_bound_529 : cellBound ((38727855271377/64000000000000 : ℚ) : ℝ) ((19398323938157/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_529 potential_upper_530 field_lower_529

theorem cell_bound_530 : cellBound ((19398323938157/32000000000000 : ℚ) : ℝ) ((38865440481251/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_530 potential_upper_531 field_lower_530

theorem cell_bound_531 : cellBound ((38865440481251/64000000000000 : ℚ) : ℝ) ((9733558271547/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_531 potential_upper_532 field_lower_531

theorem cell_bound_532 : cellBound ((9733558271547/16000000000000 : ℚ) : ℝ) ((312024205529/512000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_532 potential_upper_533 field_lower_532

theorem cell_bound_533 : cellBound ((312024205529/512000000000 : ℚ) : ℝ) ((19535909148031/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_533 potential_upper_534 field_lower_533

theorem cell_bound_534 : cellBound ((19535909148031/32000000000000 : ℚ) : ℝ) ((39140610900999/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_534 potential_upper_535 field_lower_534

theorem cell_bound_535 : cellBound ((39140610900999/64000000000000 : ℚ) : ℝ) ((2450587719121/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_535 potential_upper_536 field_lower_535

theorem cell_bound_536 : cellBound ((2450587719121/4000000000000 : ℚ) : ℝ) ((39278196110873/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_536 potential_upper_537 field_lower_536

theorem cell_bound_537 : cellBound ((39278196110873/64000000000000 : ℚ) : ℝ) ((3934698871581/6400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_537 potential_upper_538 field_lower_537

theorem cell_bound_538 : cellBound ((3934698871581/6400000000000 : ℚ) : ℝ) ((39415781320747/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_538 potential_upper_539 field_lower_538

theorem cell_bound_539 : cellBound ((39415781320747/64000000000000 : ℚ) : ℝ) ((9871143481421/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_539 potential_upper_540 field_lower_539

theorem cell_bound_540 : cellBound ((9871143481421/16000000000000 : ℚ) : ℝ) ((39553366530621/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_540 potential_upper_541 field_lower_540

theorem cell_bound_541 : cellBound ((39553366530621/64000000000000 : ℚ) : ℝ) ((19811079567779/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_541 potential_upper_542 field_lower_541

theorem cell_bound_542 : cellBound ((19811079567779/32000000000000 : ℚ) : ℝ) ((7938190348099/12800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_542 potential_upper_543 field_lower_542

theorem cell_bound_543 : cellBound ((7938190348099/12800000000000 : ℚ) : ℝ) ((4969968043179/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_543 potential_upper_544 field_lower_543

end Zeta5AppendixNumerics
