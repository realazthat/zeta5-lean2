import CertificateTactics
import AppendixCellBase
import AppendixField.Batch063
import AppendixField.Batch064
import AppendixField.Batch065
import AppendixPotential.Batch064
import AppendixPotential.Batch065
import AppendixPotential.Batch066
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_512 : cellBound ((18015831447017/32000000000000 : ℚ) : ℝ) ((36111549776069/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_512 potential_upper_513 field_lower_512

theorem cell_bound_513 : cellBound ((36111549776069/64000000000000 : ℚ) : ℝ) ((4523929582263/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_513 potential_upper_514 field_lower_513

theorem cell_bound_514 : cellBound ((4523929582263/8000000000000 : ℚ) : ℝ) ((18175605211087/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_514 potential_upper_515 field_lower_514

theorem cell_bound_515 : cellBound ((18175605211087/32000000000000 : ℚ) : ℝ) ((9127746046561/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_515 potential_upper_516 field_lower_515

theorem cell_bound_516 : cellBound ((9127746046561/16000000000000 : ℚ) : ℝ) ((18335378975157/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_516 potential_upper_517 field_lower_516

theorem cell_bound_517 : cellBound ((18335378975157/32000000000000 : ℚ) : ℝ) ((2301908232149/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_517 potential_upper_518 field_lower_517

theorem cell_bound_518 : cellBound ((2301908232149/4000000000000 : ℚ) : ℝ) ((18495152739227/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_518 potential_upper_519 field_lower_518

theorem cell_bound_519 : cellBound ((18495152739227/32000000000000 : ℚ) : ℝ) ((9287519810631/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_519 potential_upper_520 field_lower_519

theorem cell_bound_520 : cellBound ((9287519810631/16000000000000 : ℚ) : ℝ) ((4683703346333/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_520 potential_upper_521 field_lower_520

theorem cell_bound_521 : cellBound ((4683703346333/8000000000000 : ℚ) : ℝ) ((9447293574701/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_521 potential_upper_522 field_lower_521

theorem cell_bound_522 : cellBound ((9447293574701/16000000000000 : ℚ) : ℝ) ((297724389273/500000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_522 potential_upper_523 field_lower_522

theorem cell_bound_523 : cellBound ((297724389273/500000000000 : ℚ) : ℝ) ((19123153518409/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_523 potential_upper_524 field_lower_523

theorem cell_bound_524 : cellBound ((19123153518409/32000000000000 : ℚ) : ℝ) ((9595973061673/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_524 potential_upper_525 field_lower_524

theorem cell_bound_525 : cellBound ((9595973061673/16000000000000 : ℚ) : ℝ) ((19260738728283/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_525 potential_upper_526 field_lower_525

theorem cell_bound_526 : cellBound ((19260738728283/32000000000000 : ℚ) : ℝ) ((38590270061503/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_526 potential_upper_527 field_lower_526

theorem cell_bound_527 : cellBound ((38590270061503/64000000000000 : ℚ) : ℝ) ((966476566661/1600000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_527 potential_upper_528 field_lower_527

end Zeta5AppendixNumerics
