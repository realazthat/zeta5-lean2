import CertificateTactics
import AppendixCellBase
import AppendixField.Batch004
import AppendixField.Batch005
import AppendixNumericSpecial
import AppendixPotential.Batch004
import AppendixPotential.Batch005
import AppendixPotential.Batch006
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_32 : cellBound ((59205077/10000000000 : ℚ) : ℝ) ((59205079/10000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_32 potential_upper_33 vstar_lower

theorem cell_bound_33 : cellBound ((59205079/10000000000 : ℚ) : ℝ) ((8992695531/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_33 potential_upper_34 field_lower_33

theorem cell_bound_34 : cellBound ((8992695531/1000000000000 : ℚ) : ℝ) ((19572466643/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_34 potential_upper_35 field_lower_34

theorem cell_bound_35 : cellBound ((19572466643/2000000000000 : ℚ) : ℝ) ((40732008867/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_35 potential_upper_36 field_lower_35

theorem cell_bound_36 : cellBound ((40732008867/4000000000000 : ℚ) : ℝ) ((1322471389/125000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_36 potential_upper_37 field_lower_36

theorem cell_bound_37 : cellBound ((1322471389/125000000000 : ℚ) : ℝ) ((4549323561/400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_37 potential_upper_38 field_lower_37

theorem cell_bound_38 : cellBound ((4549323561/400000000000 : ℚ) : ℝ) ((12166846693/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_38 potential_upper_39 field_lower_38

theorem cell_bound_39 : cellBound ((12166846693/1000000000000 : ℚ) : ℝ) ((3068199571/200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_39 potential_upper_40 field_lower_39

theorem cell_bound_40 : cellBound ((3068199571/200000000000 : ℚ) : ℝ) ((255845148549/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_40 potential_upper_41 field_lower_40

theorem cell_bound_41 : cellBound ((255845148549/16000000000000 : ℚ) : ℝ) ((133117165709/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_41 potential_upper_42 field_lower_41

theorem cell_bound_42 : cellBound ((133117165709/8000000000000 : ℚ) : ℝ) ((108571569141/6400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_42 potential_upper_43 field_lower_42

theorem cell_bound_43 : cellBound ((108571569141/6400000000000 : ℚ) : ℝ) ((276623514287/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_43 potential_upper_44 field_lower_43

theorem cell_bound_44 : cellBound ((276623514287/16000000000000 : ℚ) : ℝ) ((563636211443/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_44 potential_upper_45 field_lower_44

theorem cell_bound_45 : cellBound ((563636211443/32000000000000 : ℚ) : ℝ) ((71753174289/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_45 potential_upper_46 field_lower_45

theorem cell_bound_46 : cellBound ((71753174289/4000000000000 : ℚ) : ℝ) ((584414577181/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_46 potential_upper_47 field_lower_46

theorem cell_bound_47 : cellBound ((584414577181/32000000000000 : ℚ) : ℝ) ((11896075201/640000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_47 potential_upper_48 field_lower_47

end Zeta5AppendixNumerics
