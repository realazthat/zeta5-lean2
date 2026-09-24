import AppendixCellBase
import AppendixField.Batch037
import AppendixField.Batch038
import AppendixField.Batch039
import AppendixPotential.Batch038
import AppendixPotential.Batch039
import AppendixPotential.Batch040
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_304 : cellBound ((36419876534909/128000000000000 : ℚ) : ℝ) ((18248810046081/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (36419876534909/128000000000000 : ℝ) ≤ (-166532277593890056827/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_304 (by norm_num)
  have hUr : potential (18248810046081/64000000000000 : ℝ) ≤ (-166532277593890056827/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_305 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_304
  linarith only [hU, hF]

theorem cell_bound_305 : cellBound ((18248810046081/64000000000000 : ℚ) : ℝ) ((7315072729883/25600000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (18248810046081/64000000000000 : ℝ) ≤ (-83161724685576548963/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_305 (by norm_num)
  have hUr : potential (7315072729883/25600000000000 : ℝ) ≤ (-83161724685576548963/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_306 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_305
  linarith only [hU, hF]

theorem cell_bound_306 : cellBound ((7315072729883/25600000000000 : ℚ) : ℝ) ((9163276801667/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (7315072729883/25600000000000 : ℝ) ≤ (-20764571034027740247/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_306 (by norm_num)
  have hUr : potential (9163276801667/32000000000000 : ℝ) ≤ (-20764571034027740247/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_307 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_306
  linarith only [hU, hF]

theorem cell_bound_307 : cellBound ((9163276801667/32000000000000 : ℚ) : ℝ) ((36730850763921/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (9163276801667/32000000000000 : ℝ) ≤ (-82955775303945918521/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_307 (by norm_num)
  have hUr : potential (36730850763921/128000000000000 : ℝ) ≤ (-82955775303945918521/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_308 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_307
  linarith only [hU, hF]

theorem cell_bound_308 : cellBound ((36730850763921/128000000000000 : ℚ) : ℝ) ((18404297160587/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (36730850763921/128000000000000 : ℝ) ≤ (-41427079967677993691/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_308 (by norm_num)
  have hUr : potential (18404297160587/64000000000000 : ℝ) ≤ (-41427079967677993691/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_309 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_308
  linarith only [hU, hF]

theorem cell_bound_309 : cellBound ((18404297160587/64000000000000 : ℚ) : ℝ) ((36886337878427/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (18404297160587/64000000000000 : ℝ) ≤ (-165506805577533831751/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_309 (by norm_num)
  have hUr : potential (36886337878427/128000000000000 : ℝ) ≤ (-165506805577533831751/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_310 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_309
  linarith only [hU, hF]

theorem cell_bound_310 : cellBound ((36886337878427/128000000000000 : ℚ) : ℝ) ((231025508973/800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (36886337878427/128000000000000 : ℝ) ≤ (-165306942578965844447/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_310 (by norm_num)
  have hUr : potential (231025508973/800000000000 : ℝ) ≤ (-165306942578965844447/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_311 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_310
  linarith only [hU, hF]

theorem cell_bound_311 : cellBound ((231025508973/800000000000 : ℚ) : ℝ) ((37041824992933/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (231025508973/800000000000 : ℝ) ≤ (-16510867079679922651/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_311 (by norm_num)
  have hUr : potential (37041824992933/128000000000000 : ℝ) ≤ (-16510867079679922651/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_312 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_311
  linarith only [hU, hF]

theorem cell_bound_312 : cellBound ((37041824992933/128000000000000 : ℚ) : ℝ) ((18559784275093/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (37041824992933/128000000000000 : ℝ) ≤ (-8245596715995157707/5000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_312 (by norm_num)
  have hUr : potential (18559784275093/64000000000000 : ℝ) ≤ (-8245596715995157707/5000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_313 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_312
  linarith only [hU, hF]

theorem cell_bound_313 : cellBound ((18559784275093/64000000000000 : ℚ) : ℝ) ((37197312107439/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (18559784275093/64000000000000 : ℝ) ≤ (-82358340513622699001/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_313 (by norm_num)
  have hUr : potential (37197312107439/128000000000000 : ℝ) ≤ (-82358340513622699001/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_314 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_313
  linarith only [hU, hF]

theorem cell_bound_314 : cellBound ((37197312107439/128000000000000 : ℚ) : ℝ) ((9318763916173/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (37197312107439/128000000000000 : ℝ) ≤ (-41130715623023479817/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_314 (by norm_num)
  have hUr : potential (9318763916173/32000000000000 : ℝ) ≤ (-41130715623023479817/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_315 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_314
  linarith only [hU, hF]

theorem cell_bound_315 : cellBound ((9318763916173/32000000000000 : ℚ) : ℝ) ((7470559844389/25600000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (9318763916173/32000000000000 : ℝ) ≤ (-164330433288297716611/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_315 (by norm_num)
  have hUr : potential (7470559844389/25600000000000 : ℝ) ≤ (-164330433288297716611/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_316 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_315
  linarith only [hU, hF]

theorem cell_bound_316 : cellBound ((7470559844389/25600000000000 : ℚ) : ℝ) ((18715271389599/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (7470559844389/25600000000000 : ℝ) ≤ (-82069675554895162871/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_316 (by norm_num)
  have hUr : potential (18715271389599/64000000000000 : ℝ) ≤ (-82069675554895162871/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_317 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_316
  linarith only [hU, hF]

theorem cell_bound_317 : cellBound ((18715271389599/64000000000000 : ℚ) : ℝ) ((37508286336451/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (18715271389599/64000000000000 : ℝ) ≤ (-163949575834389431557/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_317 (by norm_num)
  have hUr : potential (37508286336451/128000000000000 : ℝ) ≤ (-163949575834389431557/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_318 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_317
  linarith only [hU, hF]

theorem cell_bound_318 : cellBound ((37508286336451/128000000000000 : ℚ) : ℝ) ((4698253736713/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (37508286336451/128000000000000 : ℝ) ≤ (-163761070384018479043/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_318 (by norm_num)
  have hUr : potential (4698253736713/16000000000000 : ℝ) ≤ (-163761070384018479043/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_319 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_318
  linarith only [hU, hF]

theorem cell_bound_319 : cellBound ((4698253736713/16000000000000 : ℚ) : ℝ) ((37663773450957/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (4698253736713/16000000000000 : ℝ) ≤ (-4089344974467055977/2500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_319 (by norm_num)
  have hUr : potential (37663773450957/128000000000000 : ℝ) ≤ (-4089344974467055977/2500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_320 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_319
  linarith only [hU, hF]

#print axioms cell_bound_319
end Zeta5AppendixNumerics
