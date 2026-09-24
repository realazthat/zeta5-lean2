import CertificateTactics
import AppendixCellBase
import AppendixField.Batch013
import AppendixField.Batch014
import AppendixField.Batch015
import AppendixPotential.Batch014
import AppendixPotential.Batch015
import AppendixPotential.Batch016
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_112 : cellBound ((4517139266921/64000000000000 : ℚ) : ℝ) ((2275384607621/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_112 potential_upper_113 field_lower_112

theorem cell_bound_113 : cellBound ((2275384607621/32000000000000 : ℚ) : ℝ) ((4584399163563/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_113 potential_upper_114 field_lower_113

theorem cell_bound_114 : cellBound ((4584399163563/64000000000000 : ℚ) : ℝ) ((1154507277971/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_114 potential_upper_115 field_lower_114

theorem cell_bound_115 : cellBound ((1154507277971/16000000000000 : ℚ) : ℝ) ((930331812041/12800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_115 potential_upper_116 field_lower_115

theorem cell_bound_116 : cellBound ((930331812041/12800000000000 : ℚ) : ℝ) ((2342644504263/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_116 potential_upper_117 field_lower_116

theorem cell_bound_117 : cellBound ((2342644504263/32000000000000 : ℚ) : ℝ) ((9404207965373/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_117 potential_upper_118 field_lower_117

theorem cell_bound_118 : cellBound ((9404207965373/128000000000000 : ℚ) : ℝ) ((4718918956847/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_118 potential_upper_119 field_lower_118

theorem cell_bound_119 : cellBound ((4718918956847/64000000000000 : ℚ) : ℝ) ((1894293572403/25600000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_119 potential_upper_120 field_lower_119

theorem cell_bound_120 : cellBound ((1894293572403/25600000000000 : ℚ) : ℝ) ((297034306573/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_120 potential_upper_121 field_lower_120

theorem cell_bound_121 : cellBound ((297034306573/4000000000000 : ℚ) : ℝ) ((9538727758657/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_121 potential_upper_122 field_lower_121

theorem cell_bound_122 : cellBound ((9538727758657/128000000000000 : ℚ) : ℝ) ((4786178853489/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_122 potential_upper_123 field_lower_122

theorem cell_bound_123 : cellBound ((4786178853489/64000000000000 : ℚ) : ℝ) ((9605987655299/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_123 potential_upper_124 field_lower_123

theorem cell_bound_124 : cellBound ((9605987655299/128000000000000 : ℚ) : ℝ) ((481980880181/6400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_124 potential_upper_125 field_lower_124

theorem cell_bound_125 : cellBound ((481980880181/6400000000000 : ℚ) : ℝ) ((9673247551941/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_125 potential_upper_126 field_lower_125

theorem cell_bound_126 : cellBound ((9673247551941/128000000000000 : ℚ) : ℝ) ((4853438750131/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_126 potential_upper_127 field_lower_126

theorem cell_bound_127 : cellBound ((4853438750131/64000000000000 : ℚ) : ℝ) ((1221767174613/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_127 potential_upper_128 field_lower_127

end Zeta5AppendixNumerics
