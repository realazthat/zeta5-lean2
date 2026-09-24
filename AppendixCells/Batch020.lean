import AppendixCellBase
import AppendixField.Batch039
import AppendixField.Batch040
import AppendixField.Batch041
import AppendixPotential.Batch040
import AppendixPotential.Batch041
import AppendixPotential.Batch042
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_320 : cellBound ((37663773450957/128000000000000 : ℚ) : ℝ) ((3774151700821/12800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (37663773450957/128000000000000 : ℝ) ≤ (-163387728661180338007/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_320 (by norm_num)
  have hUr : potential (3774151700821/12800000000000 : ℝ) ≤ (-163387728661180338007/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_321 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_320
  linarith only [hU, hF]

theorem cell_bound_321 : cellBound ((3774151700821/12800000000000 : ℚ) : ℝ) ((37819260565463/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (3774151700821/12800000000000 : ℝ) ≤ (-163202828064614953701/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_321 (by norm_num)
  have hUr : potential (37819260565463/128000000000000 : ℝ) ≤ (-163202828064614953701/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_322 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_321
  linarith only [hU, hF]

theorem cell_bound_322 : cellBound ((37819260565463/128000000000000 : ℚ) : ℝ) ((9474251030679/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (37819260565463/128000000000000 : ℝ) ≤ (-20377383393988333059/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_322 (by norm_num)
  have hUr : potential (9474251030679/32000000000000 : ℝ) ≤ (-20377383393988333059/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_323 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_322
  linarith only [hU, hF]

theorem cell_bound_323 : cellBound ((9474251030679/32000000000000 : ℚ) : ℝ) ((37974747679969/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (9474251030679/32000000000000 : ℝ) ≤ (-162836417863462820797/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_323 (by norm_num)
  have hUr : potential (37974747679969/128000000000000 : ℝ) ≤ (-162836417863462820797/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_324 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_323
  linarith only [hU, hF]

theorem cell_bound_324 : cellBound ((37974747679969/128000000000000 : ℚ) : ℝ) ((19026245618611/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (37974747679969/128000000000000 : ℝ) ≤ (-40663713339161750091/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_324 (by norm_num)
  have hUr : potential (19026245618611/64000000000000 : ℝ) ≤ (-40663713339161750091/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_325 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_324
  linarith only [hU, hF]

theorem cell_bound_325 : cellBound ((19026245618611/64000000000000 : ℚ) : ℝ) ((1525209391779/5120000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (19026245618611/64000000000000 : ℝ) ≤ (-40618587091407705481/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_325 (by norm_num)
  have hUr : potential (1525209391779/5120000000000 : ℝ) ≤ (-40618587091407705481/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_326 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_325
  linarith only [hU, hF]

theorem cell_bound_326 : cellBound ((1525209391779/5120000000000 : ℚ) : ℝ) ((2387998646983/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1525209391779/5120000000000 : ℝ) ≤ (-32458975688842180869/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_326 (by norm_num)
  have hUr : potential (2387998646983/8000000000000 : ℝ) ≤ (-32458975688842180869/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_327 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_326
  linarith only [hU, hF]

theorem cell_bound_327 : cellBound ((2387998646983/8000000000000 : ℚ) : ℝ) ((38285721908981/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2387998646983/8000000000000 : ℝ) ≤ (-162116420786060988361/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_327 (by norm_num)
  have hUr : potential (38285721908981/128000000000000 : ℝ) ≤ (-162116420786060988361/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_328 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_327
  linarith only [hU, hF]

theorem cell_bound_328 : cellBound ((38285721908981/128000000000000 : ℚ) : ℝ) ((19181732733117/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (38285721908981/128000000000000 : ℝ) ≤ (-80969476552917535611/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_328 (by norm_num)
  have hUr : potential (19181732733117/64000000000000 : ℝ) ≤ (-80969476552917535611/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_329 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_328
  linarith only [hU, hF]

theorem cell_bound_329 : cellBound ((19181732733117/64000000000000 : ℚ) : ℝ) ((38441209023487/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (19181732733117/64000000000000 : ℝ) ≤ (-3235249093669627121/2000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_329 (by norm_num)
  have hUr : potential (38441209023487/128000000000000 : ℝ) ≤ (-3235249093669627121/2000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_330 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_329
  linarith only [hU, hF]

theorem cell_bound_330 : cellBound ((38441209023487/128000000000000 : ℚ) : ℝ) ((1925947629037/6400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (38441209023487/128000000000000 : ℝ) ≤ (-1615869053220548093/1000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_330 (by norm_num)
  have hUr : potential (1925947629037/6400000000000 : ℝ) ≤ (-1615869053220548093/1000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_331 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_330
  linarith only [hU, hF]

theorem cell_bound_331 : cellBound ((1925947629037/6400000000000 : ℚ) : ℝ) ((19337219847623/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1925947629037/6400000000000 : ℝ) ≤ (-161238577914911467589/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_331 (by norm_num)
  have hUr : potential (19337219847623/64000000000000 : ℝ) ≤ (-161238577914911467589/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_332 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_331
  linarith only [hU, hF]

theorem cell_bound_332 : cellBound ((19337219847623/64000000000000 : ℚ) : ℝ) ((4853740851219/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (19337219847623/64000000000000 : ℝ) ≤ (-160893826765526623207/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_332 (by norm_num)
  have hUr : potential (4853740851219/16000000000000 : ℝ) ≤ (-160893826765526623207/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_333 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_332
  linarith only [hU, hF]

theorem cell_bound_333 : cellBound ((4853740851219/16000000000000 : ℚ) : ℝ) ((19492706962129/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (4853740851219/16000000000000 : ℝ) ≤ (-160552519378482045837/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_333 (by norm_num)
  have hUr : potential (19492706962129/64000000000000 : ℝ) ≤ (-160552519378482045837/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_334 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_333
  linarith only [hU, hF]

theorem cell_bound_334 : cellBound ((19492706962129/64000000000000 : ℚ) : ℝ) ((9785225259691/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (19492706962129/64000000000000 : ℝ) ≤ (-20026816651274885957/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_334 (by norm_num)
  have hUr : potential (9785225259691/32000000000000 : ℝ) ≤ (-20026816651274885957/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_335 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_334
  linarith only [hU, hF]

theorem cell_bound_335 : cellBound ((9785225259691/32000000000000 : ℚ) : ℝ) ((3929638815327/12800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (9785225259691/32000000000000 : ℝ) ≤ (-15987975463786665517/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_335 (by norm_num)
  have hUr : potential (3929638815327/12800000000000 : ℝ) ≤ (-15987975463786665517/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_336 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_335
  linarith only [hU, hF]

#print axioms cell_bound_335
end Zeta5AppendixNumerics
