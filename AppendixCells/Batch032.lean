import AppendixCellBase
import AppendixField.Batch063
import AppendixField.Batch064
import AppendixField.Batch065
import AppendixPotential.Batch064
import AppendixPotential.Batch065
import AppendixPotential.Batch066
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_512 : cellBound ((18015831447017/32000000000000 : ℚ) : ℝ) ((36111549776069/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (18015831447017/32000000000000 : ℝ) ≤ (-92033932439599937443/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_512 (by norm_num)
  have hUr : potential (36111549776069/64000000000000 : ℝ) ≤ (-92033932439599937443/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_513 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_512
  linarith only [hU, hF]

theorem cell_bound_513 : cellBound ((36111549776069/64000000000000 : ℚ) : ℝ) ((4523929582263/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (36111549776069/64000000000000 : ℝ) ≤ (-11471813633513130221/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_513 (by norm_num)
  have hUr : potential (4523929582263/8000000000000 : ℝ) ≤ (-11471813633513130221/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_514 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_513
  linarith only [hU, hF]

theorem cell_bound_514 : cellBound ((4523929582263/8000000000000 : ℚ) : ℝ) ((18175605211087/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (4523929582263/8000000000000 : ℝ) ≤ (-91259847183845533843/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_514 (by norm_num)
  have hUr : potential (18175605211087/32000000000000 : ℝ) ≤ (-91259847183845533843/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_515 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_514
  linarith only [hU, hF]

theorem cell_bound_515 : cellBound ((18175605211087/32000000000000 : ℚ) : ℝ) ((9127746046561/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (18175605211087/32000000000000 : ℝ) ≤ (-45375281976093444773/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_515 (by norm_num)
  have hUr : potential (9127746046561/16000000000000 : ℝ) ≤ (-45375281976093444773/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_516 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_515
  linarith only [hU, hF]

theorem cell_bound_516 : cellBound ((9127746046561/16000000000000 : ℚ) : ℝ) ((18335378975157/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (9127746046561/16000000000000 : ℝ) ≤ (-90246440655432909699/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_516 (by norm_num)
  have hUr : potential (18335378975157/32000000000000 : ℝ) ≤ (-90246440655432909699/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_517 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_516
  linarith only [hU, hF]

theorem cell_bound_517 : cellBound ((18335378975157/32000000000000 : ℚ) : ℝ) ((2301908232149/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (18335378975157/32000000000000 : ℝ) ≤ (-89747276655682430799/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_517 (by norm_num)
  have hUr : potential (2301908232149/4000000000000 : ℝ) ≤ (-89747276655682430799/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_518 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_517
  linarith only [hU, hF]

theorem cell_bound_518 : cellBound ((2301908232149/4000000000000 : ℚ) : ℝ) ((18495152739227/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2301908232149/4000000000000 : ℝ) ≤ (-44626445075165889219/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_518 (by norm_num)
  have hUr : potential (18495152739227/32000000000000 : ℝ) ≤ (-44626445075165889219/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_519 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_518
  linarith only [hU, hF]

theorem cell_bound_519 : cellBound ((18495152739227/32000000000000 : ℚ) : ℝ) ((9287519810631/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (18495152739227/32000000000000 : ℝ) ≤ (-44381556786078831479/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_519 (by norm_num)
  have hUr : potential (9287519810631/16000000000000 : ℝ) ≤ (-44381556786078831479/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_520 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_519
  linarith only [hU, hF]

theorem cell_bound_520 : cellBound ((9287519810631/16000000000000 : ℚ) : ℝ) ((4683703346333/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (9287519810631/16000000000000 : ℝ) ≤ (-87796784725249641959/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_520 (by norm_num)
  have hUr : potential (4683703346333/8000000000000 : ℝ) ≤ (-87796784725249641959/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_521 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_520
  linarith only [hU, hF]

theorem cell_bound_521 : cellBound ((4683703346333/8000000000000 : ℚ) : ℝ) ((9447293574701/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (4683703346333/8000000000000 : ℝ) ≤ (-86847187123540338051/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_521 (by norm_num)
  have hUr : potential (9447293574701/16000000000000 : ℝ) ≤ (-86847187123540338051/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_522 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_521
  linarith only [hU, hF]

theorem cell_bound_522 : cellBound ((9447293574701/16000000000000 : ℚ) : ℝ) ((297724389273/500000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (9447293574701/16000000000000 : ℝ) ≤ (-42956682364006285137/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_522 (by norm_num)
  have hUr : potential (297724389273/500000000000 : ℝ) ≤ (-42956682364006285137/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_523 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_522
  linarith only [hU, hF]

theorem cell_bound_523 : cellBound ((297724389273/500000000000 : ℚ) : ℝ) ((19123153518409/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (297724389273/500000000000 : ℝ) ≤ (-42404617396713601079/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_523 (by norm_num)
  have hUr : potential (19123153518409/32000000000000 : ℝ) ≤ (-42404617396713601079/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_524 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_523
  linarith only [hU, hF]

theorem cell_bound_524 : cellBound ((19123153518409/32000000000000 : ℚ) : ℝ) ((9595973061673/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (19123153518409/32000000000000 : ℝ) ≤ (-84122389166286358983/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_524 (by norm_num)
  have hUr : potential (9595973061673/16000000000000 : ℝ) ≤ (-84122389166286358983/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_525 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_524
  linarith only [hU, hF]

theorem cell_bound_525 : cellBound ((9595973061673/16000000000000 : ℚ) : ℝ) ((19260738728283/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (9595973061673/16000000000000 : ℝ) ≤ (-83506568434804298041/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_525 (by norm_num)
  have hUr : potential (19260738728283/32000000000000 : ℝ) ≤ (-83506568434804298041/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_526 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_525
  linarith only [hU, hF]

theorem cell_bound_526 : cellBound ((19260738728283/32000000000000 : ℚ) : ℝ) ((38590270061503/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (19260738728283/32000000000000 : ℝ) ≤ (-83213945670493695887/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_526 (by norm_num)
  have hUr : potential (38590270061503/64000000000000 : ℝ) ≤ (-83213945670493695887/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_527 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_526
  linarith only [hU, hF]

theorem cell_bound_527 : cellBound ((38590270061503/64000000000000 : ℚ) : ℝ) ((966476566661/1600000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (38590270061503/64000000000000 : ℝ) ≤ (-82928799077825373951/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_527 (by norm_num)
  have hUr : potential (966476566661/1600000000000 : ℝ) ≤ (-82928799077825373951/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_528 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_527
  linarith only [hU, hF]

#print axioms cell_bound_527
end Zeta5AppendixNumerics
