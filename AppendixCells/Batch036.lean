import AppendixCellBase
import AppendixField.Batch071
import AppendixField.Batch072
import AppendixField.Batch073
import AppendixPotential.Batch072
import AppendixPotential.Batch073
import AppendixPotential.Batch074
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_576 : cellBound ((43082559672831/64000000000000 : ℚ) : ℝ) ((2156723943323/3200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (43082559672831/64000000000000 : ℝ) ≤ (-4223512439967377483/6250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_576 (by norm_num)
  have hUr : potential (2156723943323/3200000000000 : ℝ) ≤ (-4223512439967377483/6250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_577 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_576
  linarith only [hU, hF]

theorem cell_bound_577 : cellBound ((2156723943323/3200000000000 : ℚ) : ℝ) ((43186398060089/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2156723943323/3200000000000 : ℝ) ≤ (-67389605295385540103/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_577 (by norm_num)
  have hUr : potential (43186398060089/64000000000000 : ℝ) ≤ (-67389605295385540103/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_578 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_577
  linarith only [hU, hF]

theorem cell_bound_578 : cellBound ((43186398060089/64000000000000 : ℚ) : ℝ) ((21619158626859/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (43186398060089/64000000000000 : ℝ) ≤ (-67205020826528111373/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_578 (by norm_num)
  have hUr : potential (21619158626859/32000000000000 : ℝ) ≤ (-67205020826528111373/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_579 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_578
  linarith only [hU, hF]

theorem cell_bound_579 : cellBound ((21619158626859/32000000000000 : ℚ) : ℝ) ((43290236447347/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (21619158626859/32000000000000 : ℝ) ≤ (-67022267687100709929/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_579 (by norm_num)
  have hUr : potential (43290236447347/64000000000000 : ℝ) ≤ (-67022267687100709929/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_580 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_579
  linarith only [hU, hF]

theorem cell_bound_580 : cellBound ((43290236447347/64000000000000 : ℚ) : ℝ) ((2708884727561/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (43290236447347/64000000000000 : ℝ) ≤ (-66841196514200796027/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_580 (by norm_num)
  have hUr : potential (2708884727561/4000000000000 : ℝ) ≤ (-66841196514200796027/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_581 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_580
  linarith only [hU, hF]

theorem cell_bound_581 : cellBound ((2708884727561/4000000000000 : ℚ) : ℝ) ((8678814966921/12800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2708884727561/4000000000000 : ℝ) ≤ (-16665420120127010157/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_581 (by norm_num)
  have hUr : potential (8678814966921/12800000000000 : ℝ) ≤ (-16665420120127010157/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_582 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_581
  linarith only [hU, hF]

theorem cell_bound_582 : cellBound ((8678814966921/12800000000000 : ℚ) : ℝ) ((21722997014117/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (8678814966921/12800000000000 : ℝ) ≤ (-33241805581937398897/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_582 (by norm_num)
  have hUr : potential (21722997014117/32000000000000 : ℝ) ≤ (-33241805581937398897/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_583 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_582
  linarith only [hU, hF]

theorem cell_bound_583 : cellBound ((21722997014117/32000000000000 : ℚ) : ℝ) ((43497913221863/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (21722997014117/32000000000000 : ℝ) ≤ (-33153447215505925961/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_583 (by norm_num)
  have hUr : potential (43497913221863/64000000000000 : ℝ) ≤ (-33153447215505925961/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_584 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_583
  linarith only [hU, hF]

theorem cell_bound_584 : cellBound ((43497913221863/64000000000000 : ℚ) : ℝ) ((10887458103873/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (43497913221863/64000000000000 : ℝ) ≤ (-33065724068753096917/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_584 (by norm_num)
  have hUr : potential (10887458103873/16000000000000 : ℝ) ≤ (-33065724068753096917/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_585 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_584
  linarith only [hU, hF]

theorem cell_bound_585 : cellBound ((10887458103873/16000000000000 : ℚ) : ℝ) ((43601751609121/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (10887458103873/16000000000000 : ℝ) ≤ (-32978599872055984071/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_585 (by norm_num)
  have hUr : potential (43601751609121/64000000000000 : ℝ) ≤ (-32978599872055984071/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_586 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_585
  linarith only [hU, hF]

theorem cell_bound_586 : cellBound ((43601751609121/64000000000000 : ℚ) : ℝ) ((174614683211/256000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (43601751609121/64000000000000 : ℝ) ≤ (-32892042862411041043/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_586 (by norm_num)
  have hUr : potential (174614683211/256000000000 : ℝ) ≤ (-32892042862411041043/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_587 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_586
  linarith only [hU, hF]

theorem cell_bound_587 : cellBound ((174614683211/256000000000 : ℚ) : ℝ) ((43705589996379/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (174614683211/256000000000 : ℝ) ≤ (-65612048498319750523/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_587 (by norm_num)
  have hUr : potential (43705589996379/64000000000000 : ℝ) ≤ (-65612048498319750523/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_588 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_587
  linarith only [hU, hF]

theorem cell_bound_588 : cellBound ((43705589996379/64000000000000 : ℚ) : ℝ) ((5469688648751/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (43705589996379/64000000000000 : ℝ) ≤ (-13088207458864473349/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_588 (by norm_num)
  have hUr : potential (5469688648751/8000000000000 : ℝ) ≤ (-13088207458864473349/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_589 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_588
  linarith only [hU, hF]

theorem cell_bound_589 : cellBound ((5469688648751/8000000000000 : ℚ) : ℝ) ((43809428383637/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (5469688648751/8000000000000 : ℝ) ≤ (-4079437867271146083/6250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_589 (by norm_num)
  have hUr : potential (43809428383637/64000000000000 : ℝ) ≤ (-4079437867271146083/6250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_590 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_589
  linarith only [hU, hF]

theorem cell_bound_590 : cellBound ((43809428383637/64000000000000 : ℚ) : ℝ) ((21930673788633/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (43809428383637/64000000000000 : ℝ) ≤ (-8137739081522642707/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_590 (by norm_num)
  have hUr : potential (21930673788633/32000000000000 : ℝ) ≤ (-8137739081522642707/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_591 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_590
  linarith only [hU, hF]

theorem cell_bound_591 : cellBound ((21930673788633/32000000000000 : ℚ) : ℝ) ((8782653354179/12800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (21930673788633/32000000000000 : ℝ) ≤ (-202917873326148151/312500000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_591 (by norm_num)
  have hUr : potential (8782653354179/12800000000000 : ℝ) ≤ (-202917873326148151/312500000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_592 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_591
  linarith only [hU, hF]

#print axioms cell_bound_591
end Zeta5AppendixNumerics
