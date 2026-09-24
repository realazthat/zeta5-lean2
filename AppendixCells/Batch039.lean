import AppendixCellBase
import AppendixField.Batch077
import AppendixField.Batch078
import AppendixField.Batch079
import AppendixPotential.Batch078
import AppendixPotential.Batch079
import AppendixPotential.Batch080
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_624 : cellBound ((11610952826577/16000000000000 : ℚ) : ℝ) ((23252382371711/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (11610952826577/16000000000000 : ℝ) ≤ (-3534749249882440997/6250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_624 (by norm_num)
  have hUr : potential (23252382371711/32000000000000 : ℝ) ≤ (-3534749249882440997/6250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_625 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_624
  linarith only [hU, hF]

theorem cell_bound_625 : cellBound ((23252382371711/32000000000000 : ℚ) : ℝ) ((5820714772567/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (23252382371711/32000000000000 : ℝ) ≤ (-28178348335041671693/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_625 (by norm_num)
  have hUr : potential (5820714772567/8000000000000 : ℝ) ≤ (-28178348335041671693/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_626 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_625
  linarith only [hU, hF]

theorem cell_bound_626 : cellBound ((5820714772567/8000000000000 : ℚ) : ℝ) ((932533432353/1280000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (5820714772567/8000000000000 : ℝ) ≤ (-7019903302303289307/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_626 (by norm_num)
  have hUr : potential (932533432353/1280000000000 : ℝ) ≤ (-7019903302303289307/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_627 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_626
  linarith only [hU, hF]

theorem cell_bound_627 : cellBound ((932533432353/1280000000000 : ℚ) : ℝ) ((11671906263691/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (932533432353/1280000000000 : ℝ) ≤ (-13990854986803186851/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_627 (by norm_num)
  have hUr : potential (11671906263691/16000000000000 : ℝ) ≤ (-13990854986803186851/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_628 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_627
  linarith only [hU, hF]

theorem cell_bound_628 : cellBound ((11671906263691/16000000000000 : ℚ) : ℝ) ((23374289245939/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (11671906263691/16000000000000 : ℝ) ≤ (-55769146137831122147/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_628 (by norm_num)
  have hUr : potential (23374289245939/32000000000000 : ℝ) ≤ (-55769146137831122147/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_629 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_628
  linarith only [hU, hF]

theorem cell_bound_629 : cellBound ((23374289245939/32000000000000 : ℚ) : ℝ) ((1462797872781/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (23374289245939/32000000000000 : ℝ) ≤ (-11115259010030387367/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_629 (by norm_num)
  have hUr : potential (1462797872781/2000000000000 : ℝ) ≤ (-11115259010030387367/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_630 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_629
  linarith only [hU, hF]

theorem cell_bound_630 : cellBound ((1462797872781/2000000000000 : ℚ) : ℝ) ((23435242683053/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1462797872781/2000000000000 : ℝ) ≤ (-1107695469626033563/2000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_630 (by norm_num)
  have hUr : potential (23435242683053/32000000000000 : ℝ) ≤ (-1107695469626033563/2000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_631 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_630
  linarith only [hU, hF]

theorem cell_bound_631 : cellBound ((23435242683053/32000000000000 : ℚ) : ℝ) ((2346571940161/3200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (23435242683053/32000000000000 : ℝ) ≤ (-27597250102341527769/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_631 (by norm_num)
  have hUr : potential (2346571940161/3200000000000 : ℝ) ≤ (-27597250102341527769/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_632 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_631
  linarith only [hU, hF]

theorem cell_bound_632 : cellBound ((2346571940161/3200000000000 : ℚ) : ℝ) ((23496196120167/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2346571940161/3200000000000 : ℝ) ≤ (-27502702680967799273/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_632 (by norm_num)
  have hUr : potential (23496196120167/32000000000000 : ℝ) ≤ (-27502702680967799273/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_633 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_632
  linarith only [hU, hF]

theorem cell_bound_633 : cellBound ((23496196120167/32000000000000 : ℚ) : ℝ) ((5881668209681/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (23496196120167/32000000000000 : ℝ) ≤ (-54817427472305806517/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_633 (by norm_num)
  have hUr : potential (5881668209681/8000000000000 : ℝ) ≤ (-54817427472305806517/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_634 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_633
  linarith only [hU, hF]

theorem cell_bound_634 : cellBound ((5881668209681/8000000000000 : ℚ) : ℝ) ((23557149557281/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (5881668209681/8000000000000 : ℝ) ≤ (-27315256009532026573/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_634 (by norm_num)
  have hUr : potential (23557149557281/32000000000000 : ℝ) ≤ (-27315256009532026573/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_635 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_634
  linarith only [hU, hF]

theorem cell_bound_635 : cellBound ((23557149557281/32000000000000 : ℚ) : ℝ) ((11793813137919/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (23557149557281/32000000000000 : ℝ) ≤ (-13611152650851766713/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_635 (by norm_num)
  have hUr : potential (11793813137919/16000000000000 : ℝ) ≤ (-13611152650851766713/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_636 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_635
  linarith only [hU, hF]

theorem cell_bound_636 : cellBound ((11793813137919/16000000000000 : ℚ) : ℝ) ((4723620598879/6400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (11793813137919/16000000000000 : ℝ) ≤ (-54259680061294184397/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_636 (by norm_num)
  have hUr : potential (4723620598879/6400000000000 : ℝ) ≤ (-54259680061294184397/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_637 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_636
  linarith only [hU, hF]

theorem cell_bound_637 : cellBound ((4723620598879/6400000000000 : ℚ) : ℝ) ((2956072464119/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (4723620598879/6400000000000 : ℝ) ≤ (-10815136292436314293/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_637 (by norm_num)
  have hUr : potential (2956072464119/4000000000000 : ℝ) ≤ (-10815136292436314293/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_638 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_637
  linarith only [hU, hF]

theorem cell_bound_638 : cellBound ((2956072464119/4000000000000 : ℚ) : ℝ) ((23679056431509/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2956072464119/4000000000000 : ℝ) ≤ (-1684143097301533577/3125000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_638 (by norm_num)
  have hUr : potential (23679056431509/32000000000000 : ℝ) ≤ (-1684143097301533577/3125000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_639 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_638
  linarith only [hU, hF]

theorem cell_bound_639 : cellBound ((23679056431509/32000000000000 : ℚ) : ℝ) ((11854766575033/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (23679056431509/32000000000000 : ℝ) ≤ (-13427585274650468999/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_639 (by norm_num)
  have hUr : potential (11854766575033/16000000000000 : ℝ) ≤ (-13427585274650468999/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_640 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_639
  linarith only [hU, hF]

#print axioms cell_bound_639
end Zeta5AppendixNumerics
