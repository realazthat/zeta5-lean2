import CertificateTactics
import AppendixCellBase
import AppendixField.Batch025
import AppendixField.Batch026
import AppendixField.Batch027
import AppendixPotential.Batch026
import AppendixPotential.Batch027
import AppendixPotential.Batch028
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_208 : cellBound ((634082945103/4000000000000 : ℚ) : ℝ) ((20347434278567/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_208 potential_upper_209 field_lower_208

theorem cell_bound_209 : cellBound ((20347434278567/128000000000000 : ℚ) : ℝ) ((10202107156919/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_209 potential_upper_210 field_lower_209

theorem cell_bound_210 : cellBound ((10202107156919/64000000000000 : ℚ) : ℝ) ((20460994349109/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_210 potential_upper_211 field_lower_210

theorem cell_bound_211 : cellBound ((20460994349109/128000000000000 : ℚ) : ℝ) ((1025888719219/6400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_211 potential_upper_212 field_lower_211

theorem cell_bound_212 : cellBound ((1025888719219/6400000000000 : ℚ) : ℝ) ((20574554419651/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_212 potential_upper_213 field_lower_212

theorem cell_bound_213 : cellBound ((20574554419651/128000000000000 : ℚ) : ℝ) ((10315667227461/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_213 potential_upper_214 field_lower_213

theorem cell_bound_214 : cellBound ((10315667227461/64000000000000 : ℚ) : ℝ) ((20688114490193/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_214 potential_upper_215 field_lower_214

theorem cell_bound_215 : cellBound ((20688114490193/128000000000000 : ℚ) : ℝ) ((2593111815683/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_215 potential_upper_216 field_lower_215

theorem cell_bound_216 : cellBound ((2593111815683/16000000000000 : ℚ) : ℝ) ((4160334912147/25600000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_216 potential_upper_217 field_lower_216

theorem cell_bound_217 : cellBound ((4160334912147/25600000000000 : ℚ) : ℝ) ((10429227298003/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_217 potential_upper_218 field_lower_217

theorem cell_bound_218 : cellBound ((10429227298003/64000000000000 : ℚ) : ℝ) ((20915234631277/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_218 potential_upper_219 field_lower_218

theorem cell_bound_219 : cellBound ((20915234631277/128000000000000 : ℚ) : ℝ) ((5243003666637/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_219 potential_upper_220 field_lower_219

theorem cell_bound_220 : cellBound ((5243003666637/32000000000000 : ℚ) : ℝ) ((21028794701819/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_220 potential_upper_221 field_lower_220

theorem cell_bound_221 : cellBound ((21028794701819/128000000000000 : ℚ) : ℝ) ((2108557473709/12800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_221 potential_upper_222 field_lower_221

theorem cell_bound_222 : cellBound ((2108557473709/12800000000000 : ℚ) : ℝ) ((21142354772361/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_222 potential_upper_223 field_lower_222

theorem cell_bound_223 : cellBound ((21142354772361/128000000000000 : ℚ) : ℝ) ((1324945925477/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_223 potential_upper_224 field_lower_223

end Zeta5AppendixNumerics
