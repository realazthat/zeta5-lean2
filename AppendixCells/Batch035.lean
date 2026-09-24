import CertificateTactics
import AppendixCellBase
import AppendixField.Batch069
import AppendixField.Batch070
import AppendixField.Batch071
import AppendixPotential.Batch070
import AppendixPotential.Batch071
import AppendixPotential.Batch072
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_560 : cellBound ((5107553253053/8000000000000 : ℚ) : ℝ) ((20499005617149/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_560 potential_upper_561 field_lower_560

theorem cell_bound_561 : cellBound ((20499005617149/32000000000000 : ℚ) : ℝ) ((10283899111043/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_561 potential_upper_562 field_lower_561

theorem cell_bound_562 : cellBound ((10283899111043/16000000000000 : ℚ) : ℝ) ((20636590827023/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_562 potential_upper_563 field_lower_562

theorem cell_bound_563 : cellBound ((20636590827023/32000000000000 : ℚ) : ℝ) ((517634585799/800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_563 potential_upper_564 field_lower_563

theorem cell_bound_564 : cellBound ((517634585799/800000000000 : ℚ) : ℝ) ((20774176036897/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_564 potential_upper_565 field_lower_564

theorem cell_bound_565 : cellBound ((20774176036897/32000000000000 : ℚ) : ℝ) ((10421484320917/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_565 potential_upper_566 field_lower_565

theorem cell_bound_566 : cellBound ((10421484320917/16000000000000 : ℚ) : ℝ) ((20911761246771/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_566 potential_upper_567 field_lower_566

theorem cell_bound_567 : cellBound ((20911761246771/32000000000000 : ℚ) : ℝ) ((5245138462927/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_567 potential_upper_568 field_lower_567

theorem cell_bound_568 : cellBound ((5245138462927/8000000000000 : ℚ) : ℝ) ((10559069530791/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_568 potential_upper_569 field_lower_568

theorem cell_bound_569 : cellBound ((10559069530791/16000000000000 : ℚ) : ℝ) ((664241383483/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_569 potential_upper_570 field_lower_569

theorem cell_bound_570 : cellBound ((664241383483/1000000000000 : ℚ) : ℝ) ((4261528693017/6400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_570 potential_upper_571 field_lower_570

theorem cell_bound_571 : cellBound ((4261528693017/6400000000000 : ℚ) : ℝ) ((10679781329357/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_571 potential_upper_572 field_lower_571

theorem cell_bound_572 : cellBound ((10679781329357/16000000000000 : ℚ) : ℝ) ((21411481852343/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_572 potential_upper_573 field_lower_572

theorem cell_bound_573 : cellBound ((21411481852343/32000000000000 : ℚ) : ℝ) ((5365850261493/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_573 potential_upper_574 field_lower_573

theorem cell_bound_574 : cellBound ((5365850261493/8000000000000 : ℚ) : ℝ) ((21515320239601/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_574 potential_upper_575 field_lower_574

theorem cell_bound_575 : cellBound ((21515320239601/32000000000000 : ℚ) : ℝ) ((43082559672831/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_575 potential_upper_576 field_lower_575

end Zeta5AppendixNumerics
