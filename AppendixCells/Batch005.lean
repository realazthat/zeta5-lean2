import CertificateTactics
import AppendixCellBase
import AppendixField.Batch009
import AppendixField.Batch010
import AppendixField.Batch011
import AppendixPotential.Batch010
import AppendixPotential.Batch011
import AppendixPotential.Batch012
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_80 : cellBound ((1412931037823/32000000000000 : ℚ) : ℝ) ((71843627457/1600000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_80 potential_upper_81 field_lower_80

theorem cell_bound_81 : cellBound ((71843627457/1600000000000 : ℚ) : ℝ) ((2897686609597/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_81 potential_upper_82 field_lower_81

theorem cell_bound_82 : cellBound ((2897686609597/64000000000000 : ℚ) : ℝ) ((1460814060457/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_82 potential_upper_83 field_lower_82

theorem cell_bound_83 : cellBound ((1460814060457/32000000000000 : ℚ) : ℝ) ((2945569632231/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_83 potential_upper_84 field_lower_83

theorem cell_bound_84 : cellBound ((2945569632231/64000000000000 : ℚ) : ℝ) ((742377785887/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_84 potential_upper_85 field_lower_84

theorem cell_bound_85 : cellBound ((742377785887/16000000000000 : ℚ) : ℝ) ((598690530973/12800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_85 potential_upper_86 field_lower_85

theorem cell_bound_86 : cellBound ((598690530973/12800000000000 : ℚ) : ℝ) ((1508697083091/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_86 potential_upper_87 field_lower_86

theorem cell_bound_87 : cellBound ((1508697083091/32000000000000 : ℚ) : ℝ) ((3041335677499/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_87 potential_upper_88 field_lower_87

theorem cell_bound_88 : cellBound ((3041335677499/64000000000000 : ℚ) : ℝ) ((191579824301/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_88 potential_upper_89 field_lower_88

theorem cell_bound_89 : cellBound ((191579824301/4000000000000 : ℚ) : ℝ) ((3089218700133/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_89 potential_upper_90 field_lower_89

theorem cell_bound_90 : cellBound ((3089218700133/64000000000000 : ℚ) : ℝ) ((62263204229/1280000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_90 potential_upper_91 field_lower_90

theorem cell_bound_91 : cellBound ((62263204229/1280000000000 : ℚ) : ℝ) ((3137101722767/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_91 potential_upper_92 field_lower_91

theorem cell_bound_92 : cellBound ((3137101722767/64000000000000 : ℚ) : ℝ) ((790260808521/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_92 potential_upper_93 field_lower_92

theorem cell_bound_93 : cellBound ((790260808521/16000000000000 : ℚ) : ℝ) ((3184984745401/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_93 potential_upper_94 field_lower_93

theorem cell_bound_94 : cellBound ((3184984745401/64000000000000 : ℚ) : ℝ) ((1604463128359/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_94 potential_upper_95 field_lower_94

theorem cell_bound_95 : cellBound ((1604463128359/32000000000000 : ℚ) : ℝ) ((646573553607/12800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_95 potential_upper_96 field_lower_95

end Zeta5AppendixNumerics
