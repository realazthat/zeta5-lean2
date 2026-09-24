import CertificateTactics
import AppendixCellBase
import AppendixField.Batch011
import AppendixField.Batch012
import AppendixField.Batch013
import AppendixPotential.Batch012
import AppendixPotential.Batch013
import AppendixPotential.Batch014
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_96 : cellBound ((646573553607/12800000000000 : ℚ) : ℝ) ((407101159919/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_96 potential_upper_97 field_lower_96

theorem cell_bound_97 : cellBound ((407101159919/8000000000000 : ℚ) : ℝ) ((1652346150993/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_97 potential_upper_98 field_lower_97

theorem cell_bound_98 : cellBound ((1652346150993/32000000000000 : ℚ) : ℝ) ((167628766231/3200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_98 potential_upper_99 field_lower_98

theorem cell_bound_99 : cellBound ((167628766231/3200000000000 : ℚ) : ℝ) ((1700229173627/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_99 potential_upper_100 field_lower_99

theorem cell_bound_100 : cellBound ((1700229173627/32000000000000 : ℚ) : ℝ) ((107760667809/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_100 potential_upper_101 field_lower_100

theorem cell_bound_101 : cellBound ((107760667809/2000000000000 : ℚ) : ℝ) ((886026853789/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_101 potential_upper_102 field_lower_101

theorem cell_bound_102 : cellBound ((886026853789/16000000000000 : ℚ) : ℝ) ((454984182553/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_102 potential_upper_103 field_lower_102

theorem cell_bound_103 : cellBound ((454984182553/8000000000000 : ℚ) : ℝ) ((47892569387/800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_103 potential_upper_104 field_lower_103

theorem cell_bound_104 : cellBound ((47892569387/800000000000 : ℚ) : ℝ) ((502867205187/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_104 potential_upper_105 field_lower_104

theorem cell_bound_105 : cellBound ((502867205187/8000000000000 : ℚ) : ℝ) ((65851089563/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_105 potential_upper_106 field_lower_105

theorem cell_bound_106 : cellBound ((65851089563/1000000000000 : ℚ) : ℝ) ((2140864814337/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_106 potential_upper_107 field_lower_106

theorem cell_bound_107 : cellBound ((2140864814337/32000000000000 : ℚ) : ℝ) ((1087247381329/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_107 potential_upper_108 field_lower_107

theorem cell_bound_108 : cellBound ((1087247381329/16000000000000 : ℚ) : ℝ) ((2208124710979/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_108 potential_upper_109 field_lower_108

theorem cell_bound_109 : cellBound ((2208124710979/32000000000000 : ℚ) : ℝ) ((4449879370279/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_109 potential_upper_110 field_lower_109

theorem cell_bound_110 : cellBound ((4449879370279/64000000000000 : ℚ) : ℝ) ((22417546593/320000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_110 potential_upper_111 field_lower_110

theorem cell_bound_111 : cellBound ((22417546593/320000000000 : ℚ) : ℝ) ((4517139266921/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_111 potential_upper_112 field_lower_111

end Zeta5AppendixNumerics
