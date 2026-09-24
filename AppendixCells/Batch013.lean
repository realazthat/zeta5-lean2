import AppendixCellBase
import AppendixField.Batch025
import AppendixField.Batch026
import AppendixField.Batch027
import AppendixPotential.Batch026
import AppendixPotential.Batch027
import AppendixPotential.Batch028
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_208 : cellBound ((634082945103/4000000000000 : ℚ) : ℝ) ((20347434278567/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (634082945103/4000000000000 : ℝ) ≤ (-528160376139786817/250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_208 (by norm_num)
  have hUr : potential (20347434278567/128000000000000 : ℝ) ≤ (-528160376139786817/250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_209 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_208
  linarith only [hU, hF]

theorem cell_bound_209 : cellBound ((20347434278567/128000000000000 : ℚ) : ℝ) ((10202107156919/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (20347434278567/128000000000000 : ℝ) ≤ (-211081751249754636909/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_209 (by norm_num)
  have hUr : potential (10202107156919/64000000000000 : ℝ) ≤ (-211081751249754636909/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_210 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_209
  linarith only [hU, hF]

theorem cell_bound_210 : cellBound ((10202107156919/64000000000000 : ℚ) : ℝ) ((20460994349109/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (10202107156919/64000000000000 : ℝ) ≤ (-42180200671827160997/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_210 (by norm_num)
  have hUr : potential (20460994349109/128000000000000 : ℝ) ≤ (-42180200671827160997/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_211 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_210
  linarith only [hU, hF]

theorem cell_bound_211 : cellBound ((20460994349109/128000000000000 : ℚ) : ℝ) ((1025888719219/6400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (20460994349109/128000000000000 : ℝ) ≤ (-210721851871214857779/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_211 (by norm_num)
  have hUr : potential (1025888719219/6400000000000 : ℝ) ≤ (-210721851871214857779/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_212 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_211
  linarith only [hU, hF]

theorem cell_bound_212 : cellBound ((1025888719219/6400000000000 : ℚ) : ℝ) ((20574554419651/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1025888719219/6400000000000 : ℝ) ≤ (-210544244992212636331/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_212 (by norm_num)
  have hUr : potential (20574554419651/128000000000000 : ℝ) ≤ (-210544244992212636331/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_213 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_212
  linarith only [hU, hF]

theorem cell_bound_213 : cellBound ((20574554419651/128000000000000 : ℚ) : ℝ) ((10315667227461/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (20574554419651/128000000000000 : ℝ) ≤ (-105184067103180285177/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_213 (by norm_num)
  have hUr : potential (10315667227461/64000000000000 : ℝ) ≤ (-105184067103180285177/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_214 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_213
  linarith only [hU, hF]

theorem cell_bound_214 : cellBound ((10315667227461/64000000000000 : ℚ) : ℝ) ((20688114490193/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (10315667227461/64000000000000 : ℝ) ≤ (-1642136518769507009/781250000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_214 (by norm_num)
  have hUr : potential (20688114490193/128000000000000 : ℝ) ≤ (-1642136518769507009/781250000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_215 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_214
  linarith only [hU, hF]

theorem cell_bound_215 : cellBound ((20688114490193/128000000000000 : ℚ) : ℝ) ((2593111815683/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (20688114490193/128000000000000 : ℝ) ≤ (-105010111308641157877/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_215 (by norm_num)
  have hUr : potential (2593111815683/16000000000000 : ℝ) ≤ (-105010111308641157877/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_216 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_215
  linarith only [hU, hF]

theorem cell_bound_216 : cellBound ((2593111815683/16000000000000 : ℚ) : ℝ) ((4160334912147/25600000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2593111815683/16000000000000 : ℝ) ≤ (-104924169297770462487/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_216 (by norm_num)
  have hUr : potential (4160334912147/25600000000000 : ℝ) ≤ (-104924169297770462487/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_217 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_216
  linarith only [hU, hF]

theorem cell_bound_217 : cellBound ((4160334912147/25600000000000 : ℚ) : ℝ) ((10429227298003/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (4160334912147/25600000000000 : ℝ) ≤ (-20967778446064251519/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_217 (by norm_num)
  have hUr : potential (10429227298003/64000000000000 : ℝ) ≤ (-20967778446064251519/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_218 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_217
  linarith only [hU, hF]

theorem cell_bound_218 : cellBound ((10429227298003/64000000000000 : ℚ) : ℝ) ((20915234631277/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (10429227298003/64000000000000 : ℝ) ≤ (-130942827656663141/62500000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_218 (by norm_num)
  have hUr : potential (20915234631277/128000000000000 : ℝ) ≤ (-130942827656663141/62500000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_219 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_218
  linarith only [hU, hF]

theorem cell_bound_219 : cellBound ((20915234631277/128000000000000 : ℚ) : ℝ) ((5243003666637/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (20915234631277/128000000000000 : ℝ) ≤ (-26167565486856381209/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_219 (by norm_num)
  have hUr : potential (5243003666637/32000000000000 : ℝ) ≤ (-26167565486856381209/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_220 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_219
  linarith only [hU, hF]

theorem cell_bound_220 : cellBound ((5243003666637/32000000000000 : ℚ) : ℝ) ((21028794701819/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (5243003666637/32000000000000 : ℝ) ≤ (-104586875578037883609/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_220 (by norm_num)
  have hUr : potential (21028794701819/128000000000000 : ℝ) ≤ (-104586875578037883609/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_221 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_220
  linarith only [hU, hF]

theorem cell_bound_221 : cellBound ((21028794701819/128000000000000 : ℚ) : ℝ) ((2108557473709/12800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (21028794701819/128000000000000 : ℝ) ≤ (-209008175426332732263/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_221 (by norm_num)
  have hUr : potential (2108557473709/12800000000000 : ℝ) ≤ (-209008175426332732263/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_222 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_221
  linarith only [hU, hF]

theorem cell_bound_222 : cellBound ((2108557473709/12800000000000 : ℚ) : ℝ) ((21142354772361/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2108557473709/12800000000000 : ℝ) ≤ (-104421883893214285969/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_222 (by norm_num)
  have hUr : potential (21142354772361/128000000000000 : ℝ) ≤ (-104421883893214285969/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_223 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_222
  linarith only [hU, hF]

theorem cell_bound_223 : cellBound ((21142354772361/128000000000000 : ℚ) : ℝ) ((1324945925477/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (21142354772361/128000000000000 : ℝ) ≤ (-208680500278398218591/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_223 (by norm_num)
  have hUr : potential (1324945925477/8000000000000 : ℝ) ≤ (-208680500278398218591/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_224 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_223
  linarith only [hU, hF]

#print axioms cell_bound_223
end Zeta5AppendixNumerics
