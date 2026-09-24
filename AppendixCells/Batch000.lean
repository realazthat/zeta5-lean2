import CertificateTactics
import AppendixCellBase
import AppendixField.Batch000
import AppendixField.Batch001
import AppendixPotential.Batch000
import AppendixPotential.Batch001
import AppendixPotential.Batch002
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_0 : cellBound ((0/1 : ℚ) : ℝ) ((7174131/200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_0 potential_upper_1 field_lower_1

theorem cell_bound_1 : cellBound ((7174131/200000000000 : ℚ) : ℝ) ((21522393/400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_1 potential_upper_2 field_lower_2

theorem cell_bound_2 : cellBound ((21522393/400000000000 : ℚ) : ℝ) ((7174131/100000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_2 potential_upper_3 field_lower_3

theorem cell_bound_3 : cellBound ((7174131/100000000000 : ℚ) : ℝ) ((14825913/200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_3 potential_upper_4 field_lower_4

theorem cell_bound_4 : cellBound ((14825913/200000000000 : ℚ) : ℝ) ((78667711/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_4 potential_upper_5 field_lower_5

theorem cell_bound_5 : cellBound ((78667711/1000000000000 : ℚ) : ℝ) ((85815639/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_5 potential_upper_6 field_lower_6

theorem cell_bound_6 : cellBound ((85815639/1000000000000 : ℚ) : ℝ) ((19269871/200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_6 potential_upper_7 field_lower_7

theorem cell_bound_7 : cellBound ((19269871/200000000000 : ℚ) : ℝ) ((55761057/500000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_7 potential_upper_8 field_lower_8

theorem cell_bound_8 : cellBound ((55761057/500000000000 : ℚ) : ℝ) ((33336783/250000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_8 potential_upper_9 field_lower_9

theorem cell_bound_9 : cellBound ((33336783/250000000000 : ℚ) : ℝ) ((82548843/500000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_9 potential_upper_10 field_lower_10

theorem cell_bound_10 : cellBound ((82548843/500000000000 : ℚ) : ℝ) ((53051547/250000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_10 potential_upper_11 field_lower_11

theorem cell_bound_11 : cellBound ((53051547/250000000000 : ℚ) : ℝ) ((496117379/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_11 potential_upper_12 field_lower_12

theorem cell_bound_12 : cellBound ((496117379/2000000000000 : ℚ) : ℝ) ((283911191/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_12 potential_upper_13 field_lower_13

theorem cell_bound_13 : cellBound ((283911191/1000000000000 : ℚ) : ℝ) ((170058951/500000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_13 potential_upper_14 field_lower_14

theorem cell_bound_14 : cellBound ((170058951/500000000000 : ℚ) : ℝ) ((396324613/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_14 potential_upper_15 field_lower_15

theorem cell_bound_15 : cellBound ((396324613/1000000000000 : ℚ) : ℝ) ((974522519/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_15 potential_upper_16 field_lower_16

end Zeta5AppendixNumerics
