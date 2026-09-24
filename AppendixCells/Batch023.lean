import AppendixCellBase
import AppendixField.Batch045
import AppendixField.Batch046
import AppendixField.Batch047
import AppendixPotential.Batch046
import AppendixPotential.Batch047
import AppendixPotential.Batch048
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_368 : cellBound ((23636923020387/64000000000000 : ℚ) : ℝ) ((47357563191033/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (23636923020387/64000000000000 : ℝ) ≤ (-70558957417104972109/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_368 (by norm_num)
  have hUr : potential (47357563191033/128000000000000 : ℝ) ≤ (-70558957417104972109/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_369 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_368
  linarith only [hU, hF]

theorem cell_bound_369 : cellBound ((47357563191033/128000000000000 : ℚ) : ℝ) ((11860320085323/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (47357563191033/128000000000000 : ℝ) ≤ (-70464828616040116741/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_369 (by norm_num)
  have hUr : potential (11860320085323/32000000000000 : ℝ) ≤ (-70464828616040116741/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_370 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_369
  linarith only [hU, hF]

theorem cell_bound_370 : cellBound ((11860320085323/32000000000000 : ℚ) : ℝ) ((47524997491551/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (11860320085323/32000000000000 : ℝ) ≤ (-140742623991664731991/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_370 (by norm_num)
  have hUr : potential (47524997491551/128000000000000 : ℝ) ≤ (-140742623991664731991/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_371 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_370
  linarith only [hU, hF]

theorem cell_bound_371 : cellBound ((47524997491551/128000000000000 : ℚ) : ℝ) ((4760871464181/12800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (47524997491551/128000000000000 : ℝ) ≤ (-14055677848464481079/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_371 (by norm_num)
  have hUr : potential (4760871464181/12800000000000 : ℝ) ≤ (-14055677848464481079/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_372 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_371
  linarith only [hU, hF]

theorem cell_bound_372 : cellBound ((4760871464181/12800000000000 : ℚ) : ℝ) ((47692431792069/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (4760871464181/12800000000000 : ℝ) ≤ (-35093021368729331809/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_372 (by norm_num)
  have hUr : potential (47692431792069/128000000000000 : ℝ) ≤ (-35093021368729331809/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_373 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_372
  linarith only [hU, hF]

theorem cell_bound_373 : cellBound ((47692431792069/128000000000000 : ℚ) : ℝ) ((5972018617791/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (47692431792069/128000000000000 : ℝ) ≤ (-35047127998455204537/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_373 (by norm_num)
  have hUr : potential (5972018617791/16000000000000 : ℝ) ≤ (-35047127998455204537/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_374 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_373
  linarith only [hU, hF]

theorem cell_bound_374 : cellBound ((5972018617791/16000000000000 : ℚ) : ℝ) ((47859866092587/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (5972018617791/16000000000000 : ℝ) ≤ (-140006027419402036131/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_374 (by norm_num)
  have hUr : potential (47859866092587/128000000000000 : ℝ) ≤ (-140006027419402036131/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_375 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_374
  linarith only [hU, hF]

theorem cell_bound_375 : cellBound ((47859866092587/128000000000000 : ℚ) : ℝ) ((23971791621423/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (47859866092587/128000000000000 : ℝ) ≤ (-139824602567900418113/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_375 (by norm_num)
  have hUr : potential (23971791621423/64000000000000 : ℝ) ≤ (-139824602567900418113/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_376 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_375
  linarith only [hU, hF]

theorem cell_bound_376 : cellBound ((23971791621423/64000000000000 : ℚ) : ℝ) ((9605460078621/25600000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (23971791621423/64000000000000 : ℝ) ≤ (-139644209618752263581/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_376 (by norm_num)
  have hUr : potential (9605460078621/25600000000000 : ℝ) ≤ (-139644209618752263581/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_377 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_376
  linarith only [hU, hF]

theorem cell_bound_377 : cellBound ((9605460078621/25600000000000 : ℚ) : ℝ) ((12027754385841/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (9605460078621/25600000000000 : ℝ) ≤ (-34866205722393099011/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_377 (by norm_num)
  have hUr : potential (12027754385841/32000000000000 : ℝ) ≤ (-34866205722393099011/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_378 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_377
  linarith only [hU, hF]

theorem cell_bound_378 : cellBound ((12027754385841/32000000000000 : ℚ) : ℝ) ((48194734693623/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (12027754385841/32000000000000 : ℝ) ≤ (-27857283504957110077/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_378 (by norm_num)
  have hUr : potential (48194734693623/128000000000000 : ℝ) ≤ (-27857283504957110077/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_379 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_378
  linarith only [hU, hF]

theorem cell_bound_379 : cellBound ((48194734693623/128000000000000 : ℚ) : ℝ) ((24139225921941/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (48194734693623/128000000000000 : ℝ) ≤ (-3477724251511800877/2500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_379 (by norm_num)
  have hUr : potential (24139225921941/64000000000000 : ℝ) ≤ (-3477724251511800877/2500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_380 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_379
  linarith only [hU, hF]

theorem cell_bound_380 : cellBound ((24139225921941/64000000000000 : ℚ) : ℝ) ((48362168994141/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (24139225921941/64000000000000 : ℝ) ≤ (-138932458315207450147/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_380 (by norm_num)
  have hUr : potential (48362168994141/128000000000000 : ℝ) ≤ (-138932458315207450147/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_381 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_380
  linarith only [hU, hF]

theorem cell_bound_381 : cellBound ((48362168994141/128000000000000 : ℚ) : ℝ) ((121114715361/320000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (48362168994141/128000000000000 : ℝ) ≤ (-138756861192547763287/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_381 (by norm_num)
  have hUr : potential (121114715361/320000000000 : ℝ) ≤ (-138756861192547763287/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_382 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_381
  linarith only [hU, hF]

theorem cell_bound_382 : cellBound ((121114715361/320000000000 : ℚ) : ℝ) ((48529603294659/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (121114715361/320000000000 : ℝ) ≤ (-138582158513021803241/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_382 (by norm_num)
  have hUr : potential (48529603294659/128000000000000 : ℝ) ≤ (-138582158513021803241/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_383 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_382
  linarith only [hU, hF]

theorem cell_bound_383 : cellBound ((48529603294659/128000000000000 : ℚ) : ℝ) ((24306660222459/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (48529603294659/128000000000000 : ℝ) ≤ (-138408331109500407987/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_383 (by norm_num)
  have hUr : potential (24306660222459/64000000000000 : ℝ) ≤ (-138408331109500407987/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_384 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_383
  linarith only [hU, hF]

#print axioms cell_bound_383
end Zeta5AppendixNumerics
