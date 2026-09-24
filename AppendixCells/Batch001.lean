import CertificateTactics
import AppendixCellBase
import AppendixField.Batch002
import AppendixField.Batch003
import AppendixPotential.Batch002
import AppendixPotential.Batch003
import AppendixPotential.Batch004
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_16 : cellBound ((974522519/2000000000000 : ℚ) : ℝ) ((289098953/500000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_16 potential_upper_17 field_lower_17

theorem cell_bound_17 : cellBound ((289098953/500000000000 : ℚ) : ℝ) ((729961631/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_17 potential_upper_18 field_lower_18

theorem cell_bound_18 : cellBound ((729961631/1000000000000 : ℚ) : ℝ) ((1611686987/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_18 potential_upper_19 field_lower_19

theorem cell_bound_19 : cellBound ((1611686987/2000000000000 : ℚ) : ℝ) ((220431339/250000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_19 potential_upper_20 field_lower_20

theorem cell_bound_20 : cellBound ((220431339/250000000000 : ℚ) : ℝ) ((4047462733/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_20 potential_upper_21 field_lower_21

theorem cell_bound_21 : cellBound ((4047462733/4000000000000 : ℚ) : ℝ) ((2284012021/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_21 potential_upper_22 field_lower_22

theorem cell_bound_22 : cellBound ((2284012021/2000000000000 : ℚ) : ℝ) ((5088585351/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_22 potential_upper_23 field_lower_23

theorem cell_bound_23 : cellBound ((5088585351/4000000000000 : ℚ) : ℝ) ((280457333/200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_23 potential_upper_24 field_lower_24

theorem cell_bound_24 : cellBound ((280457333/200000000000 : ℚ) : ℝ) ((6519108259/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_24 potential_upper_25 field_lower_25

theorem cell_bound_25 : cellBound ((6519108259/4000000000000 : ℚ) : ℝ) ((3714534929/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_25 potential_upper_26 field_lower_26

theorem cell_bound_26 : cellBound ((3714534929/2000000000000 : ℚ) : ℝ) ((8339031457/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_26 potential_upper_27 field_lower_27

theorem cell_bound_27 : cellBound ((8339031457/4000000000000 : ℚ) : ℝ) ((289031033/125000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_27 potential_upper_28 field_lower_28

theorem cell_bound_28 : cellBound ((289031033/125000000000 : ℚ) : ℝ) ((124379927/40000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_28 potential_upper_29 field_lower_29

theorem cell_bound_29 : cellBound ((124379927/40000000000 : ℚ) : ℝ) ((7016246261/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_29 potential_upper_30 field_lower_30

theorem cell_bound_30 : cellBound ((7016246261/2000000000000 : ℚ) : ℝ) ((1953374043/500000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_30 potential_upper_31 field_lower_31

theorem cell_bound_31 : cellBound ((1953374043/500000000000 : ℚ) : ℝ) ((59205077/10000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_31 potential_upper_32 field_lower_32

end Zeta5AppendixNumerics
