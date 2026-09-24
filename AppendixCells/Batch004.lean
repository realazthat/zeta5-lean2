import AppendixCellBase
import AppendixField.Batch007
import AppendixField.Batch008
import AppendixField.Batch009
import AppendixPotential.Batch008
import AppendixPotential.Batch009
import AppendixPotential.Batch010
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_64 : cellBound ((944711264583/32000000000000 : ℚ) : ℝ) ((59550060209/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (944711264583/32000000000000 : ℝ) ≤ (-549905291003694661/200000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_64 (by norm_num)
  have hUr : potential (59550060209/2000000000000 : ℝ) ≤ (-549905291003694661/200000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_65 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_64
  linarith only [hU, hF]

theorem cell_bound_65 : cellBound ((59550060209/2000000000000 : ℚ) : ℝ) ((192178132421/6400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (59550060209/2000000000000 : ℝ) ≤ (-54960901315747869837/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_65 (by norm_num)
  have hUr : potential (192178132421/6400000000000 : ℝ) ≤ (-54960901315747869837/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_66 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_65
  linarith only [hU, hF]

theorem cell_bound_66 : cellBound ((192178132421/6400000000000 : ℚ) : ℝ) ((484490180433/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (192178132421/6400000000000 : ℝ) ≤ (-137330145364500149131/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_66 (by norm_num)
  have hUr : potential (484490180433/16000000000000 : ℝ) ≤ (-137330145364500149131/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_67 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_66
  linarith only [hU, hF]

theorem cell_bound_67 : cellBound ((484490180433/16000000000000 : ℚ) : ℝ) ((977070059627/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (484490180433/16000000000000 : ℝ) ≤ (-274519715796450841623/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_67 (by norm_num)
  have hUr : potential (977070059627/32000000000000 : ℝ) ≤ (-274519715796450841623/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_68 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_67
  linarith only [hU, hF]

theorem cell_bound_68 : cellBound ((977070059627/32000000000000 : ℚ) : ℝ) ((246289939597/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (977070059627/32000000000000 : ℝ) ≤ (-3429781680211960181/1250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_68 (by norm_num)
  have hUr : potential (246289939597/8000000000000 : ℝ) ≤ (-3429781680211960181/1250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_69 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_68
  linarith only [hU, hF]

theorem cell_bound_69 : cellBound ((246289939597/8000000000000 : ℚ) : ℝ) ((100133915591/3200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (246289939597/8000000000000 : ℝ) ≤ (-34264687835749443321/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_69 (by norm_num)
  have hUr : potential (100133915591/3200000000000 : ℝ) ≤ (-34264687835749443321/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_70 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_69
  linarith only [hU, hF]

theorem cell_bound_70 : cellBound ((100133915591/3200000000000 : ℚ) : ℝ) ((127189819179/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (100133915591/3200000000000 : ℝ) ≤ (-27386371691237568801/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_70 (by norm_num)
  have hUr : potential (127189819179/4000000000000 : ℝ) ≤ (-27386371691237568801/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_71 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_70
  linarith only [hU, hF]

theorem cell_bound_71 : cellBound ((127189819179/4000000000000 : ℚ) : ℝ) ((516848975477/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (127189819179/4000000000000 : ℝ) ≤ (-273619982419613731079/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_71 (by norm_num)
  have hUr : potential (516848975477/16000000000000 : ℝ) ≤ (-273619982419613731079/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_72 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_71
  linarith only [hU, hF]

theorem cell_bound_72 : cellBound ((516848975477/16000000000000 : ℚ) : ℝ) ((262469337119/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (516848975477/16000000000000 : ℝ) ≤ (-68346328837550090901/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_72 (by norm_num)
  have hUr : potential (262469337119/8000000000000 : ℝ) ≤ (-68346328837550090901/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_73 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_72
  linarith only [hU, hF]

theorem cell_bound_73 : cellBound ((262469337119/8000000000000 : ℚ) : ℝ) ((6763975897/200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (262469337119/8000000000000 : ℝ) ≤ (-68235003498902866827/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_73 (by norm_num)
  have hUr : potential (6763975897/200000000000 : ℝ) ≤ (-68235003498902866827/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_74 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_73
  linarith only [hU, hF]

theorem cell_bound_74 : cellBound ((6763975897/200000000000 : ℚ) : ℝ) ((278648734641/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (6763975897/200000000000 : ℝ) ≤ (-136261285682690732173/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_74 (by norm_num)
  have hUr : potential (278648734641/8000000000000 : ℝ) ≤ (-136261285682690732173/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_75 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_74
  linarith only [hU, hF]

theorem cell_bound_75 : cellBound ((278648734641/8000000000000 : ℚ) : ℝ) ((143369216701/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (278648734641/8000000000000 : ℝ) ≤ (-272129056005142496517/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_75 (by norm_num)
  have hUr : potential (143369216701/4000000000000 : ℝ) ≤ (-272129056005142496517/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_76 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_75
  linarith only [hU, hF]

theorem cell_bound_76 : cellBound ((143369216701/4000000000000 : ℚ) : ℝ) ((75729457731/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (143369216701/4000000000000 : ℝ) ≤ (-271402211973984812039/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_76 (by norm_num)
  have hUr : potential (75729457731/2000000000000 : ℝ) ≤ (-271402211973984812039/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_77 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_76
  linarith only [hU, hF]

theorem cell_bound_77 : cellBound ((75729457731/2000000000000 : ℚ) : ℝ) ((20954789123/500000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (75729457731/2000000000000 : ℝ) ≤ (-135067340962496292497/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_77 (by norm_num)
  have hUr : potential (20954789123/500000000000 : ℝ) ≤ (-135067340962496292497/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_78 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_77
  linarith only [hU, hF]

theorem cell_bound_78 : cellBound ((20954789123/500000000000 : ℚ) : ℝ) ((694494763253/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (20954789123/500000000000 : ℝ) ≤ (-267505241230109801683/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_78 (by norm_num)
  have hUr : potential (694494763253/16000000000000 : ℝ) ≤ (-267505241230109801683/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_79 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_78
  linarith only [hU, hF]

theorem cell_bound_79 : cellBound ((694494763253/16000000000000 : ℚ) : ℝ) ((1412931037823/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (694494763253/16000000000000 : ℝ) ≤ (-53363011017125020303/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_79 (by norm_num)
  have hUr : potential (1412931037823/32000000000000 : ℝ) ≤ (-53363011017125020303/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_80 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_79
  linarith only [hU, hF]

#print axioms cell_bound_79
end Zeta5AppendixNumerics
