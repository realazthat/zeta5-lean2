import AppendixCellBase
import AppendixField.Batch075
import AppendixField.Batch076
import AppendixField.Batch077
import AppendixPotential.Batch076
import AppendixPotential.Batch077
import AppendixPotential.Batch078
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_608 : cellBound ((2812723114819/4000000000000 : ℚ) : ℝ) ((22553704112181/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2812723114819/4000000000000 : ℝ) ≤ (-1531466594830306839/2500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_608 (by norm_num)
  have hUr : potential (22553704112181/32000000000000 : ℝ) ≤ (-1531466594830306839/2500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_609 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_608
  linarith only [hU, hF]

theorem cell_bound_609 : cellBound ((22553704112181/32000000000000 : ℚ) : ℝ) ((2260562330581/3200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (22553704112181/32000000000000 : ℝ) ≤ (-12190647535914160769/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_609 (by norm_num)
  have hUr : potential (2260562330581/3200000000000 : ℝ) ≤ (-12190647535914160769/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_610 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_609
  linarith only [hU, hF]

theorem cell_bound_610 : cellBound ((2260562330581/3200000000000 : ℚ) : ℝ) ((22657542499439/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2260562330581/3200000000000 : ℝ) ≤ (-30324849208126602973/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_610 (by norm_num)
  have hUr : potential (22657542499439/32000000000000 : ℝ) ≤ (-30324849208126602973/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_611 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_610
  linarith only [hU, hF]

theorem cell_bound_611 : cellBound ((22657542499439/32000000000000 : ℚ) : ℝ) ((5677365423267/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (22657542499439/32000000000000 : ℝ) ≤ (-60347987888249117859/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_611 (by norm_num)
  have hUr : potential (5677365423267/8000000000000 : ℝ) ≤ (-60347987888249117859/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_612 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_611
  linarith only [hU, hF]

theorem cell_bound_612 : cellBound ((5677365423267/8000000000000 : ℚ) : ℝ) ((22761380886697/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (5677365423267/8000000000000 : ℝ) ≤ (-15012013269161152933/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_612 (by norm_num)
  have hUr : potential (22761380886697/32000000000000 : ℝ) ≤ (-15012013269161152933/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_613 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_612
  linarith only [hU, hF]

theorem cell_bound_613 : cellBound ((22761380886697/32000000000000 : ℚ) : ℝ) ((11406650040163/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (22761380886697/32000000000000 : ℝ) ≤ (-59749843499815820451/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_613 (by norm_num)
  have hUr : potential (11406650040163/16000000000000 : ℝ) ≤ (-59749843499815820451/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_614 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_613
  linarith only [hU, hF]

theorem cell_bound_614 : cellBound ((11406650040163/16000000000000 : ℚ) : ℝ) ((89520072139/125000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (11406650040163/16000000000000 : ℝ) ≤ (-5915841944724284687/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_614 (by norm_num)
  have hUr : potential (89520072139/125000000000 : ℝ) ≤ (-5915841944724284687/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_615 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_614
  linarith only [hU, hF]

theorem cell_bound_615 : cellBound ((89520072139/125000000000 : ℚ) : ℝ) ((11489045952349/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (89520072139/125000000000 : ℝ) ≤ (-11700031669280935441/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_615 (by norm_num)
  have hUr : potential (11489045952349/16000000000000 : ℝ) ≤ (-11700031669280935441/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_616 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_615
  linarith only [hU, hF]

theorem cell_bound_616 : cellBound ((11489045952349/16000000000000 : ℚ) : ℝ) ((4601713724651/6400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (11489045952349/16000000000000 : ℝ) ≤ (-29129186199518752069/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_616 (by norm_num)
  have hUr : potential (4601713724651/6400000000000 : ℝ) ≤ (-29129186199518752069/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_617 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_616
  linarith only [hU, hF]

theorem cell_bound_617 : cellBound ((4601713724651/6400000000000 : ℚ) : ℝ) ((5759761335453/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (4601713724651/6400000000000 : ℝ) ≤ (-7253527405911989229/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_617 (by norm_num)
  have hUr : potential (5759761335453/8000000000000 : ℝ) ≤ (-7253527405911989229/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_618 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_617
  linarith only [hU, hF]

theorem cell_bound_618 : cellBound ((5759761335453/8000000000000 : ℚ) : ℝ) ((23069522060369/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (5759761335453/8000000000000 : ℝ) ≤ (-57805688603894872353/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_618 (by norm_num)
  have hUr : potential (23069522060369/32000000000000 : ℝ) ≤ (-57805688603894872353/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_619 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_618
  linarith only [hU, hF]

theorem cell_bound_619 : cellBound ((23069522060369/32000000000000 : ℚ) : ℝ) ((11549999389463/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (23069522060369/32000000000000 : ℝ) ≤ (-28794359747870428333/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_619 (by norm_num)
  have hUr : potential (11549999389463/16000000000000 : ℝ) ≤ (-28794359747870428333/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_620 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_619
  linarith only [hU, hF]

theorem cell_bound_620 : cellBound ((11549999389463/16000000000000 : ℚ) : ℝ) ((23130475497483/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (11549999389463/16000000000000 : ℝ) ≤ (-28688042499997077471/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_620 (by norm_num)
  have hUr : potential (23130475497483/32000000000000 : ℝ) ≤ (-28688042499997077471/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_621 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_620
  linarith only [hU, hF]

theorem cell_bound_621 : cellBound ((23130475497483/32000000000000 : ℚ) : ℝ) ((579023805401/800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (23130475497483/32000000000000 : ℝ) ≤ (-7145872873661092453/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_621 (by norm_num)
  have hUr : potential (579023805401/800000000000 : ℝ) ≤ (-7145872873661092453/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_622 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_621
  linarith only [hU, hF]

theorem cell_bound_622 : cellBound ((579023805401/800000000000 : ℚ) : ℝ) ((23191428934597/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (579023805401/800000000000 : ℝ) ≤ (-14240213889124053219/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_622 (by norm_num)
  have hUr : potential (23191428934597/32000000000000 : ℝ) ≤ (-14240213889124053219/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_623 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_622
  linarith only [hU, hF]

theorem cell_bound_623 : cellBound ((23191428934597/32000000000000 : ℚ) : ℝ) ((11610952826577/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (23191428934597/32000000000000 : ℝ) ≤ (-28378646896288422183/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_623 (by norm_num)
  have hUr : potential (11610952826577/16000000000000 : ℝ) ≤ (-28378646896288422183/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_624 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_623
  linarith only [hU, hF]

#print axioms cell_bound_623
end Zeta5AppendixNumerics
