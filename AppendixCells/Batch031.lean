import CertificateTactics
import AppendixCellBase
import AppendixField.Batch061
import AppendixField.Batch062
import AppendixField.Batch063
import AppendixPotential.Batch062
import AppendixPotential.Batch063
import AppendixPotential.Batch064
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_496 : cellBound ((4364155818193/8000000000000 : ℚ) : ℝ) ((69906379973123/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_496 potential_upper_497 field_lower_496

theorem cell_bound_497 : cellBound ((69906379973123/128000000000000 : ℚ) : ℝ) ((34993133427579/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_497 potential_upper_498 field_lower_497

theorem cell_bound_498 : cellBound ((34993133427579/64000000000000 : ℚ) : ℝ) ((70066153737193/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_498 potential_upper_499 field_lower_498

theorem cell_bound_499 : cellBound ((70066153737193/128000000000000 : ℚ) : ℝ) ((17536510154807/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_499 potential_upper_500 field_lower_499

theorem cell_bound_500 : cellBound ((17536510154807/32000000000000 : ℚ) : ℝ) ((35152907191649/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_500 potential_upper_501 field_lower_500

theorem cell_bound_501 : cellBound ((35152907191649/64000000000000 : ℚ) : ℝ) ((8808198518421/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_501 potential_upper_502 field_lower_501

theorem cell_bound_502 : cellBound ((8808198518421/16000000000000 : ℚ) : ℝ) ((35312680955719/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_502 potential_upper_503 field_lower_502

theorem cell_bound_503 : cellBound ((35312680955719/64000000000000 : ℚ) : ℝ) ((17696283918877/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_503 potential_upper_504 field_lower_503

theorem cell_bound_504 : cellBound ((17696283918877/32000000000000 : ℚ) : ℝ) ((35472454719789/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_504 potential_upper_505 field_lower_504

theorem cell_bound_505 : cellBound ((35472454719789/64000000000000 : ℚ) : ℝ) ((1111010675057/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_505 potential_upper_506 field_lower_505

theorem cell_bound_506 : cellBound ((1111010675057/2000000000000 : ℚ) : ℝ) ((35632228483859/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_506 potential_upper_507 field_lower_506

theorem cell_bound_507 : cellBound ((35632228483859/64000000000000 : ℚ) : ℝ) ((17856057682947/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_507 potential_upper_508 field_lower_507

theorem cell_bound_508 : cellBound ((17856057682947/32000000000000 : ℚ) : ℝ) ((35792002247929/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_508 potential_upper_509 field_lower_508

theorem cell_bound_509 : cellBound ((35792002247929/64000000000000 : ℚ) : ℝ) ((8967972282491/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_509 potential_upper_510 field_lower_509

theorem cell_bound_510 : cellBound ((8967972282491/16000000000000 : ℚ) : ℝ) ((35951776011999/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_510 potential_upper_511 field_lower_510

theorem cell_bound_511 : cellBound ((35951776011999/64000000000000 : ℚ) : ℝ) ((18015831447017/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_511 potential_upper_512 field_lower_511

end Zeta5AppendixNumerics
