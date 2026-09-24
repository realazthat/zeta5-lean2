import AppendixCellBase
import AppendixField.Batch069
import AppendixField.Batch070
import AppendixField.Batch071
import AppendixPotential.Batch070
import AppendixPotential.Batch071
import AppendixPotential.Batch072
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_560 : cellBound ((5107553253053/8000000000000 : ℚ) : ℝ) ((20499005617149/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (5107553253053/8000000000000 : ℝ) ≤ (-74870658890194170311/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_560 (by norm_num)
  have hUr : potential (20499005617149/32000000000000 : ℝ) ≤ (-74870658890194170311/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_561 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_560
  linarith only [hU, hF]

theorem cell_bound_561 : cellBound ((20499005617149/32000000000000 : ℚ) : ℝ) ((10283899111043/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (20499005617149/32000000000000 : ℝ) ≤ (-14889423952169544453/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_561 (by norm_num)
  have hUr : potential (10283899111043/16000000000000 : ℝ) ≤ (-14889423952169544453/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_562 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_561
  linarith only [hU, hF]

theorem cell_bound_562 : cellBound ((10283899111043/16000000000000 : ℚ) : ℝ) ((20636590827023/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (10283899111043/16000000000000 : ℝ) ≤ (-74027224600566548569/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_562 (by norm_num)
  have hUr : potential (20636590827023/32000000000000 : ℝ) ≤ (-74027224600566548569/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_563 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_562
  linarith only [hU, hF]

theorem cell_bound_563 : cellBound ((20636590827023/32000000000000 : ℚ) : ℝ) ((517634585799/800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (20636590827023/32000000000000 : ℝ) ≤ (-9201354322340763351/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_563 (by norm_num)
  have hUr : potential (517634585799/800000000000 : ℝ) ≤ (-9201354322340763351/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_564 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_563
  linarith only [hU, hF]

theorem cell_bound_564 : cellBound ((517634585799/800000000000 : ℚ) : ℝ) ((20774176036897/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (517634585799/800000000000 : ℝ) ≤ (-36598911620376694477/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_564 (by norm_num)
  have hUr : potential (20774176036897/32000000000000 : ℝ) ≤ (-36598911620376694477/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_565 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_564
  linarith only [hU, hF]

theorem cell_bound_565 : cellBound ((20774176036897/32000000000000 : ℚ) : ℝ) ((10421484320917/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (20774176036897/32000000000000 : ℝ) ≤ (-18197018617707388177/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_565 (by norm_num)
  have hUr : potential (10421484320917/16000000000000 : ℝ) ≤ (-18197018617707388177/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_566 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_565
  linarith only [hU, hF]

theorem cell_bound_566 : cellBound ((10421484320917/16000000000000 : ℚ) : ℝ) ((20911761246771/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (10421484320917/16000000000000 : ℝ) ≤ (-72381482011101804883/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_566 (by norm_num)
  have hUr : potential (20911761246771/32000000000000 : ℝ) ≤ (-72381482011101804883/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_567 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_566
  linarith only [hU, hF]

theorem cell_bound_567 : cellBound ((20911761246771/32000000000000 : ℚ) : ℝ) ((5245138462927/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (20911761246771/32000000000000 : ℝ) ≤ (-71977946952642506861/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_567 (by norm_num)
  have hUr : potential (5245138462927/8000000000000 : ℝ) ≤ (-71977946952642506861/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_568 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_567
  linarith only [hU, hF]

theorem cell_bound_568 : cellBound ((5245138462927/8000000000000 : ℚ) : ℝ) ((10559069530791/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (5245138462927/8000000000000 : ℝ) ≤ (-35589845581693857837/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_568 (by norm_num)
  have hUr : potential (10559069530791/16000000000000 : ℝ) ≤ (-35589845581693857837/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_569 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_568
  linarith only [hU, hF]

theorem cell_bound_569 : cellBound ((10559069530791/16000000000000 : ℚ) : ℝ) ((664241383483/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (10559069530791/16000000000000 : ℝ) ≤ (-1099885141595061171/1562500000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_569 (by norm_num)
  have hUr : potential (664241383483/1000000000000 : ℝ) ≤ (-1099885141595061171/1562500000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_570 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_569
  linarith only [hU, hF]

theorem cell_bound_570 : cellBound ((664241383483/1000000000000 : ℚ) : ℝ) ((4261528693017/6400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (664241383483/1000000000000 : ℝ) ≤ (-69659512755745651131/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_570 (by norm_num)
  have hUr : potential (4261528693017/6400000000000 : ℝ) ≤ (-69659512755745651131/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_571 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_570
  linarith only [hU, hF]

theorem cell_bound_571 : cellBound ((4261528693017/6400000000000 : ℚ) : ℝ) ((10679781329357/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (4261528693017/6400000000000 : ℝ) ≤ (-69185234319830891299/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_571 (by norm_num)
  have hUr : potential (10679781329357/16000000000000 : ℝ) ≤ (-69185234319830891299/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_572 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_571
  linarith only [hU, hF]

theorem cell_bound_572 : cellBound ((10679781329357/16000000000000 : ℚ) : ℝ) ((21411481852343/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (10679781329357/16000000000000 : ℝ) ≤ (-2750193207402177861/4000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_572 (by norm_num)
  have hUr : potential (21411481852343/32000000000000 : ℝ) ≤ (-2750193207402177861/4000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_573 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_572
  linarith only [hU, hF]

theorem cell_bound_573 : cellBound ((21411481852343/32000000000000 : ℚ) : ℝ) ((5365850261493/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (21411481852343/32000000000000 : ℝ) ≤ (-17086960431115462033/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_573 (by norm_num)
  have hUr : potential (5365850261493/8000000000000 : ℝ) ≤ (-17086960431115462033/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_574 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_573
  linarith only [hU, hF]

theorem cell_bound_574 : cellBound ((5365850261493/8000000000000 : ℚ) : ℝ) ((21515320239601/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (5365850261493/8000000000000 : ℝ) ≤ (-67956326990882133683/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_574 (by norm_num)
  have hUr : potential (21515320239601/32000000000000 : ℝ) ≤ (-67956326990882133683/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_575 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_574
  linarith only [hU, hF]

theorem cell_bound_575 : cellBound ((21515320239601/32000000000000 : ℚ) : ℝ) ((43082559672831/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (21515320239601/32000000000000 : ℝ) ≤ (-13553003558241239469/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_575 (by norm_num)
  have hUr : potential (43082559672831/64000000000000 : ℝ) ≤ (-13553003558241239469/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_576 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_575
  linarith only [hU, hF]

#print axioms cell_bound_575
end Zeta5AppendixNumerics
