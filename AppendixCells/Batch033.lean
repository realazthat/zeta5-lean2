import AppendixCellBase
import AppendixField.Batch065
import AppendixField.Batch066
import AppendixField.Batch067
import AppendixPotential.Batch066
import AppendixPotential.Batch067
import AppendixPotential.Batch068
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_528 : cellBound ((966476566661/1600000000000 : ℚ) : ℝ) ((38727855271377/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (966476566661/1600000000000 : ℝ) ≤ (-10331234707884210153/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_528 (by norm_num)
  have hUr : potential (38727855271377/64000000000000 : ℝ) ≤ (-10331234707884210153/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_529 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_528
  linarith only [hU, hF]

theorem cell_bound_529 : cellBound ((38727855271377/64000000000000 : ℚ) : ℝ) ((19398323938157/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (38727855271377/64000000000000 : ℝ) ≤ (-82376268907482863457/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_529 (by norm_num)
  have hUr : potential (19398323938157/32000000000000 : ℝ) ≤ (-82376268907482863457/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_530 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_529
  linarith only [hU, hF]

theorem cell_bound_530 : cellBound ((19398323938157/32000000000000 : ℚ) : ℝ) ((38865440481251/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (19398323938157/32000000000000 : ℝ) ≤ (-41053641110601576159/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_530 (by norm_num)
  have hUr : potential (38865440481251/64000000000000 : ℝ) ≤ (-41053641110601576159/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_531 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_530
  linarith only [hU, hF]

theorem cell_bound_531 : cellBound ((38865440481251/64000000000000 : ℚ) : ℝ) ((9733558271547/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (38865440481251/64000000000000 : ℝ) ≤ (-40921189712479850481/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_531 (by norm_num)
  have hUr : potential (9733558271547/16000000000000 : ℝ) ≤ (-40921189712479850481/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_532 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_531
  linarith only [hU, hF]

theorem cell_bound_532 : cellBound ((9733558271547/16000000000000 : ℚ) : ℝ) ((312024205529/512000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (9733558271547/16000000000000 : ℝ) ≤ (-81581131608963447989/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_532 (by norm_num)
  have hUr : potential (312024205529/512000000000 : ℝ) ≤ (-81581131608963447989/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_533 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_532
  linarith only [hU, hF]

theorem cell_bound_533 : cellBound ((312024205529/512000000000 : ℚ) : ℝ) ((19535909148031/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (312024205529/512000000000 : ℝ) ≤ (-20330797410917533877/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_533 (by norm_num)
  have hUr : potential (19535909148031/32000000000000 : ℝ) ≤ (-20330797410917533877/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_534 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_533
  linarith only [hU, hF]

theorem cell_bound_534 : cellBound ((19535909148031/32000000000000 : ℚ) : ℝ) ((39140610900999/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (19535909148031/32000000000000 : ℝ) ≤ (-81068264970646602541/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_534 (by norm_num)
  have hUr : potential (39140610900999/64000000000000 : ℝ) ≤ (-81068264970646602541/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_535 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_534
  linarith only [hU, hF]

theorem cell_bound_535 : cellBound ((39140610900999/64000000000000 : ℚ) : ℝ) ((2450587719121/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (39140610900999/64000000000000 : ℝ) ≤ (-404080577291935137/500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_535 (by norm_num)
  have hUr : potential (2450587719121/4000000000000 : ℝ) ≤ (-404080577291935137/500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_536 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_535
  linarith only [hU, hF]

theorem cell_bound_536 : cellBound ((2450587719121/4000000000000 : ℚ) : ℝ) ((39278196110873/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2450587719121/4000000000000 : ℝ) ≤ (-4028326771882712497/5000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_536 (by norm_num)
  have hUr : potential (39278196110873/64000000000000 : ℝ) ≤ (-4028326771882712497/5000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_537 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_536
  linarith only [hU, hF]

theorem cell_bound_537 : cellBound ((39278196110873/64000000000000 : ℚ) : ℝ) ((3934698871581/6400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (39278196110873/64000000000000 : ℝ) ≤ (-80319348331397895017/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_537 (by norm_num)
  have hUr : potential (3934698871581/6400000000000 : ℝ) ≤ (-80319348331397895017/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_538 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_537
  linarith only [hU, hF]

theorem cell_bound_538 : cellBound ((3934698871581/6400000000000 : ℚ) : ℝ) ((39415781320747/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (3934698871581/6400000000000 : ℝ) ≤ (-80074401456547989547/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_538 (by norm_num)
  have hUr : potential (39415781320747/64000000000000 : ℝ) ≤ (-80074401456547989547/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_539 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_538
  linarith only [hU, hF]

theorem cell_bound_539 : cellBound ((39415781320747/64000000000000 : ℚ) : ℝ) ((9871143481421/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (39415781320747/64000000000000 : ℝ) ≤ (-19957890240149399967/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_539 (by norm_num)
  have hUr : potential (9871143481421/16000000000000 : ℝ) ≤ (-19957890240149399967/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_540 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_539
  linarith only [hU, hF]

theorem cell_bound_540 : cellBound ((9871143481421/16000000000000 : ℚ) : ℝ) ((39553366530621/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (9871143481421/16000000000000 : ℝ) ≤ (-4974419301005444911/6250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_540 (by norm_num)
  have hUr : potential (39553366530621/64000000000000 : ℝ) ≤ (-4974419301005444911/6250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_541 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_540
  linarith only [hU, hF]

theorem cell_bound_541 : cellBound ((39553366530621/64000000000000 : ℚ) : ℝ) ((19811079567779/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (39553366530621/64000000000000 : ℝ) ≤ (-79351740853000047143/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_541 (by norm_num)
  have hUr : potential (19811079567779/32000000000000 : ℝ) ≤ (-79351740853000047143/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_542 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_541
  linarith only [hU, hF]

theorem cell_bound_542 : cellBound ((19811079567779/32000000000000 : ℚ) : ℝ) ((7938190348099/12800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (19811079567779/32000000000000 : ℝ) ≤ (-79114563739592534201/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_542 (by norm_num)
  have hUr : potential (7938190348099/12800000000000 : ℝ) ≤ (-79114563739592534201/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_543 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_542
  linarith only [hU, hF]

theorem cell_bound_543 : cellBound ((7938190348099/12800000000000 : ℚ) : ℝ) ((4969968043179/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (7938190348099/12800000000000 : ℝ) ≤ (-78879094061745025619/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_543 (by norm_num)
  have hUr : potential (4969968043179/8000000000000 : ℝ) ≤ (-78879094061745025619/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_544 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_543
  linarith only [hU, hF]

#print axioms cell_bound_543
end Zeta5AppendixNumerics
