import AppendixCellBase
import AppendixField.Batch033
import AppendixField.Batch034
import AppendixField.Batch035
import AppendixPotential.Batch034
import AppendixPotential.Batch035
import AppendixPotential.Batch036
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_272 : cellBound ((7220147100329/32000000000000 : ℚ) : ℝ) ((2894882863549/12800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (7220147100329/32000000000000 : ℝ) ≤ (-186113945427644814117/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_272 (by norm_num)
  have hUr : potential (2894882863549/12800000000000 : ℝ) ≤ (-186113945427644814117/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_273 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_272
  linarith only [hU, hF]

theorem cell_bound_273 : cellBound ((2894882863549/12800000000000 : ℚ) : ℝ) ((906783402177/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2894882863549/12800000000000 : ℝ) ≤ (-5810580504229130217/3125000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_273 (by norm_num)
  have hUr : potential (906783402177/4000000000000 : ℝ) ≤ (-5810580504229130217/3125000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_274 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_273
  linarith only [hU, hF]

theorem cell_bound_274 : cellBound ((906783402177/4000000000000 : ℚ) : ℝ) ((14542654551919/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (906783402177/4000000000000 : ℝ) ≤ (-23220537152623993767/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_274 (by norm_num)
  have hUr : potential (14542654551919/64000000000000 : ℝ) ≤ (-23220537152623993767/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_275 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_274
  linarith only [hU, hF]

theorem cell_bound_275 : cellBound ((14542654551919/64000000000000 : ℚ) : ℝ) ((7288387334503/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (14542654551919/64000000000000 : ℝ) ≤ (-18559108474131503481/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_275 (by norm_num)
  have hUr : potential (7288387334503/32000000000000 : ℝ) ≤ (-18559108474131503481/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_276 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_275
  linarith only [hU, hF]

theorem cell_bound_276 : cellBound ((7288387334503/32000000000000 : ℚ) : ℝ) ((732250745159/3200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (7288387334503/32000000000000 : ℝ) ≤ (-46311941988866656143/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_276 (by norm_num)
  have hUr : potential (732250745159/3200000000000 : ℝ) ≤ (-46311941988866656143/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_277 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_276
  linarith only [hU, hF]

theorem cell_bound_277 : cellBound ((732250745159/3200000000000 : ℚ) : ℝ) ((7356627568677/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (732250745159/3200000000000 : ℝ) ≤ (-18490845303908329583/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_277 (by norm_num)
  have hUr : potential (7356627568677/32000000000000 : ℝ) ≤ (-18490845303908329583/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_278 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_277
  linarith only [hU, hF]

theorem cell_bound_278 : cellBound ((7356627568677/32000000000000 : ℚ) : ℝ) ((1847686921441/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (7356627568677/32000000000000 : ℝ) ≤ (-92286490857538819207/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_278 (by norm_num)
  have hUr : potential (1847686921441/8000000000000 : ℝ) ≤ (-92286490857538819207/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_279 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_278
  linarith only [hU, hF]

theorem cell_bound_279 : cellBound ((1847686921441/8000000000000 : ℚ) : ℝ) ((7424867802851/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1847686921441/8000000000000 : ℝ) ≤ (-92120604189016822229/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_279 (by norm_num)
  have hUr : potential (7424867802851/32000000000000 : ℝ) ≤ (-92120604189016822229/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_280 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_279
  linarith only [hU, hF]

theorem cell_bound_280 : cellBound ((7424867802851/32000000000000 : ℚ) : ℝ) ((3729493959969/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (7424867802851/32000000000000 : ℝ) ≤ (-183912998396626094773/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_280 (by norm_num)
  have hUr : potential (3729493959969/16000000000000 : ℝ) ≤ (-183912998396626094773/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_281 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_280
  linarith only [hU, hF]

theorem cell_bound_281 : cellBound ((3729493959969/16000000000000 : ℚ) : ℝ) ((299724321481/1280000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (3729493959969/16000000000000 : ℝ) ≤ (-36717645403161046703/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_281 (by norm_num)
  have hUr : potential (299724321481/1280000000000 : ℝ) ≤ (-36717645403161046703/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_282 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_281
  linarith only [hU, hF]

theorem cell_bound_282 : cellBound ((299724321481/1280000000000 : ℚ) : ℝ) ((29403234977/125000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (299724321481/1280000000000 : ℝ) ≤ (-36653355638763647603/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_282 (by norm_num)
  have hUr : potential (29403234977/125000000000 : ℝ) ≤ (-36653355638763647603/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_283 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_282
  linarith only [hU, hF]

theorem cell_bound_283 : cellBound ((29403234977/125000000000 : ℚ) : ℝ) ((7561348271199/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (29403234977/125000000000 : ℝ) ≤ (-11434283987726164777/6250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_283 (by norm_num)
  have hUr : potential (7561348271199/32000000000000 : ℝ) ≤ (-11434283987726164777/6250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_284 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_283
  linarith only [hU, hF]

theorem cell_bound_284 : cellBound ((7561348271199/32000000000000 : ℚ) : ℝ) ((3797734194143/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (7561348271199/32000000000000 : ℝ) ≤ (-182633422947392822657/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_284 (by norm_num)
  have hUr : potential (3797734194143/16000000000000 : ℝ) ≤ (-182633422947392822657/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_285 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_284
  linarith only [hU, hF]

theorem cell_bound_285 : cellBound ((3797734194143/16000000000000 : ℚ) : ℝ) ((383185431123/1600000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (3797734194143/16000000000000 : ℝ) ≤ (-182012148357618061059/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_285 (by norm_num)
  have hUr : potential (383185431123/1600000000000 : ℝ) ≤ (-182012148357618061059/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_286 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_285
  linarith only [hU, hF]

theorem cell_bound_286 : cellBound ((383185431123/1600000000000 : ℚ) : ℝ) ((3865974428317/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (383185431123/1600000000000 : ℝ) ≤ (-18140226381545642993/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_286 (by norm_num)
  have hUr : potential (3865974428317/16000000000000 : ℝ) ≤ (-18140226381545642993/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_287 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_286
  linarith only [hU, hF]

theorem cell_bound_287 : cellBound ((3865974428317/16000000000000 : ℚ) : ℝ) ((975023636351/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (3865974428317/16000000000000 : ℝ) ≤ (-180803155097160694559/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_287 (by norm_num)
  have hUr : potential (975023636351/4000000000000 : ℝ) ≤ (-180803155097160694559/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_288 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_287
  linarith only [hU, hF]

#print axioms cell_bound_287
end Zeta5AppendixNumerics
