import AppendixCellBase
import AppendixField.Batch059
import AppendixField.Batch060
import AppendixField.Batch061
import AppendixPotential.Batch060
import AppendixPotential.Batch061
import AppendixPotential.Batch062
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_480 : cellBound ((2142134468079/4000000000000 : ℚ) : ℝ) ((68628189860563/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2142134468079/4000000000000 : ℝ) ≤ (-24587236673677633161/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_480 (by norm_num)
  have hUr : potential (68628189860563/128000000000000 : ℝ) ≤ (-24587236673677633161/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_481 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_480
  linarith only [hU, hF]

theorem cell_bound_481 : cellBound ((68628189860563/128000000000000 : ℚ) : ℝ) ((34354038371299/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (68628189860563/128000000000000 : ℝ) ≤ (-24548820260991955379/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_481 (by norm_num)
  have hUr : potential (34354038371299/64000000000000 : ℝ) ≤ (-24548820260991955379/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_482 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_481
  linarith only [hU, hF]

theorem cell_bound_482 : cellBound ((34354038371299/64000000000000 : ℚ) : ℝ) ((68787963624633/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (34354038371299/64000000000000 : ℝ) ≤ (-98042459533125730533/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_482 (by norm_num)
  have hUr : potential (68787963624633/128000000000000 : ℝ) ≤ (-98042459533125730533/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_483 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_482
  linarith only [hU, hF]

theorem cell_bound_483 : cellBound ((68787963624633/128000000000000 : ℚ) : ℝ) ((17216962626667/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (68787963624633/128000000000000 : ℝ) ≤ (-12236306830746116917/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_483 (by norm_num)
  have hUr : potential (17216962626667/32000000000000 : ℝ) ≤ (-12236306830746116917/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_484 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_483
  linarith only [hU, hF]

theorem cell_bound_484 : cellBound ((17216962626667/32000000000000 : ℚ) : ℝ) ((68947737388703/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (17216962626667/32000000000000 : ℝ) ≤ (-3054351273072396751/3125000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_484 (by norm_num)
  have hUr : potential (68947737388703/128000000000000 : ℝ) ≤ (-3054351273072396751/3125000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_485 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_484
  linarith only [hU, hF]

theorem cell_bound_485 : cellBound ((68947737388703/128000000000000 : ℚ) : ℝ) ((34513812135369/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (68947737388703/128000000000000 : ℝ) ≤ (-12198599194051793283/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_485 (by norm_num)
  have hUr : potential (34513812135369/64000000000000 : ℝ) ≤ (-12198599194051793283/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_486 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_485
  linarith only [hU, hF]

theorem cell_bound_486 : cellBound ((34513812135369/64000000000000 : ℚ) : ℝ) ((69107511152773/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (34513812135369/64000000000000 : ℝ) ≤ (-97439090670029387077/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_486 (by norm_num)
  have hUr : potential (69107511152773/128000000000000 : ℝ) ≤ (-97439090670029387077/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_487 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_486
  linarith only [hU, hF]

theorem cell_bound_487 : cellBound ((69107511152773/128000000000000 : ℚ) : ℝ) ((8648424754351/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (69107511152773/128000000000000 : ℝ) ≤ (-24322527624993160473/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_487 (by norm_num)
  have hUr : potential (8648424754351/16000000000000 : ℝ) ≤ (-24322527624993160473/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_488 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_487
  linarith only [hU, hF]

theorem cell_bound_488 : cellBound ((8648424754351/16000000000000 : ℚ) : ℝ) ((69267284916843/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (8648424754351/16000000000000 : ℝ) ≤ (-97141833523273769969/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_488 (by norm_num)
  have hUr : potential (69267284916843/128000000000000 : ℝ) ≤ (-97141833523273769969/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_489 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_488
  linarith only [hU, hF]

theorem cell_bound_489 : cellBound ((69267284916843/128000000000000 : ℚ) : ℝ) ((34673585899439/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (69267284916843/128000000000000 : ℝ) ≤ (-96994240961333104411/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_489 (by norm_num)
  have hUr : potential (34673585899439/64000000000000 : ℝ) ≤ (-96994240961333104411/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_490 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_489
  linarith only [hU, hF]

theorem cell_bound_490 : cellBound ((34673585899439/64000000000000 : ℚ) : ℝ) ((69427058680913/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (34673585899439/64000000000000 : ℝ) ≤ (-48423657241973736363/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_490 (by norm_num)
  have hUr : potential (69427058680913/128000000000000 : ℝ) ≤ (-48423657241973736363/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_491 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_490
  linarith only [hU, hF]

theorem cell_bound_491 : cellBound ((69427058680913/128000000000000 : ℚ) : ℝ) ((17376736390737/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (69427058680913/128000000000000 : ℝ) ≤ (-96701037889514845163/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_491 (by norm_num)
  have hUr : potential (17376736390737/32000000000000 : ℝ) ≤ (-96701037889514845163/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_492 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_491
  linarith only [hU, hF]

theorem cell_bound_492 : cellBound ((17376736390737/32000000000000 : ℚ) : ℝ) ((69586832444983/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (17376736390737/32000000000000 : ℝ) ≤ (-19311079025518841111/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_492 (by norm_num)
  have hUr : potential (69586832444983/128000000000000 : ℝ) ≤ (-19311079025518841111/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_493 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_492
  linarith only [hU, hF]

theorem cell_bound_493 : cellBound ((69586832444983/128000000000000 : ℚ) : ℝ) ((34833359663509/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (69586832444983/128000000000000 : ℝ) ≤ (-96410371222695167079/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_493 (by norm_num)
  have hUr : potential (34833359663509/64000000000000 : ℝ) ≤ (-96410371222695167079/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_494 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_493
  linarith only [hU, hF]

theorem cell_bound_494 : cellBound ((34833359663509/64000000000000 : ℚ) : ℝ) ((69746606209053/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (34833359663509/64000000000000 : ℝ) ≤ (-96265951620744489659/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_494 (by norm_num)
  have hUr : potential (69746606209053/128000000000000 : ℝ) ≤ (-96265951620744489659/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_495 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_494
  linarith only [hU, hF]

theorem cell_bound_495 : cellBound ((69746606209053/128000000000000 : ℚ) : ℝ) ((4364155818193/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (69746606209053/128000000000000 : ℝ) ≤ (-24030530698386588731/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_495 (by norm_num)
  have hUr : potential (4364155818193/8000000000000 : ℝ) ≤ (-24030530698386588731/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_496 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_495
  linarith only [hU, hF]

#print axioms cell_bound_495
end Zeta5AppendixNumerics
