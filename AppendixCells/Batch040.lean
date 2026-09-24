import AppendixCellBase
import AppendixField.Batch079
import AppendixField.Batch080
import AppendixField.Batch081
import AppendixPotential.Batch080
import AppendixPotential.Batch081
import AppendixPotential.Batch082
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_640 : cellBound ((11854766575033/16000000000000 : ℚ) : ℝ) ((23740009868623/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (11854766575033/16000000000000 : ℝ) ≤ (-5352893814373307841/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_640 (by norm_num)
  have hUr : potential (23740009868623/32000000000000 : ℝ) ≤ (-5352893814373307841/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_641 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_640
  linarith only [hU, hF]

theorem cell_bound_641 : cellBound ((23740009868623/32000000000000 : ℚ) : ℝ) ((1188524329359/1600000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (23740009868623/32000000000000 : ℝ) ≤ (-53348343228819660511/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_641 (by norm_num)
  have hUr : potential (1188524329359/1600000000000 : ℝ) ≤ (-53348343228819660511/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_642 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_641
  linarith only [hU, hF]

theorem cell_bound_642 : cellBound ((1188524329359/1600000000000 : ℚ) : ℝ) ((23800963305737/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1188524329359/1600000000000 : ℝ) ≤ (-13292132861950774221/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_642 (by norm_num)
  have hUr : potential (23800963305737/32000000000000 : ℝ) ≤ (-13292132861950774221/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_643 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_642
  linarith only [hU, hF]

theorem cell_bound_643 : cellBound ((23800963305737/32000000000000 : ℚ) : ℝ) ((11915720012147/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (23800963305737/32000000000000 : ℝ) ≤ (-52989479987600840229/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_643 (by norm_num)
  have hUr : potential (11915720012147/16000000000000 : ℝ) ≤ (-52989479987600840229/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_644 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_643
  linarith only [hU, hF]

theorem cell_bound_644 : cellBound ((11915720012147/16000000000000 : ℚ) : ℝ) ((746637295669/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (11915720012147/16000000000000 : ℝ) ≤ (-52633574580563285053/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_644 (by norm_num)
  have hUr : potential (746637295669/1000000000000 : ℝ) ≤ (-52633574580563285053/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_645 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_644
  linarith only [hU, hF]

theorem cell_bound_645 : cellBound ((746637295669/1000000000000 : ℚ) : ℝ) ((765809953469387/1024000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (746637295669/1000000000000 : ℝ) ≤ (-52358116544885725381/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_645 (by norm_num)
  have hUr : potential (765809953469387/1024000000000000 : ℝ) ≤ (-52358116544885725381/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_646 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_645
  linarith only [hU, hF]

theorem cell_bound_646 : cellBound ((765809953469387/1024000000000000 : ℚ) : ℝ) ((383531658086859/512000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (765809953469387/1024000000000000 : ℝ) ≤ (-52112062004109321751/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_646 (by norm_num)
  have hUr : potential (383531658086859/512000000000000 : ℝ) ≤ (-52112062004109321751/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_647 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_646
  linarith only [hU, hF]

theorem cell_bound_647 : cellBound ((383531658086859/512000000000000 : ℚ) : ℝ) ((768316678878049/1024000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (383531658086859/512000000000000 : ℝ) ≤ (-12967938511193613827/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_647 (by norm_num)
  have hUr : potential (768316678878049/1024000000000000 : ℝ) ≤ (-12967938511193613827/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_648 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_647
  linarith only [hU, hF]

theorem cell_bound_648 : cellBound ((768316678878049/1024000000000000 : ℚ) : ℝ) ((38478502079119/51200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (768316678878049/1024000000000000 : ℝ) ≤ (-51634916772547811731/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_648 (by norm_num)
  have hUr : potential (38478502079119/51200000000000 : ℝ) ≤ (-51634916772547811731/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_649 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_648
  linarith only [hU, hF]

theorem cell_bound_649 : cellBound ((38478502079119/51200000000000 : ℚ) : ℝ) ((770823404286711/1024000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (38478502079119/51200000000000 : ℝ) ≤ (-25700325912828724207/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_649 (by norm_num)
  have hUr : potential (770823404286711/1024000000000000 : ℝ) ≤ (-25700325912828724207/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_650 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_649
  linarith only [hU, hF]

theorem cell_bound_650 : cellBound ((770823404286711/1024000000000000 : ℚ) : ℝ) ((386038383495521/512000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (770823404286711/1024000000000000 : ℝ) ≤ (-2558424319182558037/5000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_650 (by norm_num)
  have hUr : potential (386038383495521/512000000000000 : ℝ) ≤ (-2558424319182558037/5000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_651 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_650
  linarith only [hU, hF]

theorem cell_bound_651 : cellBound ((386038383495521/512000000000000 : ℚ) : ℝ) ((773330129695373/1024000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (386038383495521/512000000000000 : ℝ) ≤ (-25469065177602493747/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_651 (by norm_num)
  have hUr : potential (773330129695373/1024000000000000 : ℝ) ≤ (-25469065177602493747/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_652 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_651
  linarith only [hU, hF]

theorem cell_bound_652 : cellBound ((773330129695373/1024000000000000 : ℚ) : ℝ) ((96822936549963/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (773330129695373/1024000000000000 : ℝ) ≤ (-25354693983726568587/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_652 (by norm_num)
  have hUr : potential (96822936549963/128000000000000 : ℝ) ≤ (-25354693983726568587/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_653 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_652
  linarith only [hU, hF]

theorem cell_bound_653 : cellBound ((96822936549963/128000000000000 : ℚ) : ℝ) ((155167371020807/204800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (96822936549963/128000000000000 : ℝ) ≤ (-10096423401619219691/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_653 (by norm_num)
  have hUr : potential (155167371020807/204800000000000 : ℝ) ≤ (-10096423401619219691/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_654 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_653
  linarith only [hU, hF]

theorem cell_bound_654 : cellBound ((155167371020807/204800000000000 : ℚ) : ℝ) ((388545108904183/512000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (155167371020807/204800000000000 : ℝ) ≤ (-50256209743504016111/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_654 (by norm_num)
  have hUr : potential (388545108904183/512000000000000 : ℝ) ≤ (-50256209743504016111/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_655 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_654
  linarith only [hU, hF]

theorem cell_bound_655 : cellBound ((388545108904183/512000000000000 : ℚ) : ℝ) ((194899235804257/256000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (388545108904183/512000000000000 : ℝ) ≤ (-49808160683778410639/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_655 (by norm_num)
  have hUr : potential (194899235804257/256000000000000 : ℝ) ≤ (-49808160683778410639/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_656 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_655
  linarith only [hU, hF]

#print axioms cell_bound_655
end Zeta5AppendixNumerics
