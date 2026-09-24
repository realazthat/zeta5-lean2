import AppendixCellBase
import AppendixField.Batch083
import AppendixField.Batch084
import AppendixField.Batch085
import AppendixPotential.Batch084
import AppendixPotential.Batch085
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_672 : cellBound ((106849838184611/128000000000000 : ℚ) : ℝ) ((54051600444471/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (106849838184611/128000000000000 : ℝ) ≤ (-36349671252260808593/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_672 (by norm_num)
  have hUr : potential (54051600444471/64000000000000 : ℝ) ≤ (-36349671252260808593/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_673 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_672
  linarith only [hU, hF]

theorem cell_bound_673 : cellBound ((54051600444471/64000000000000 : ℚ) : ℝ) ((27652481574401/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (54051600444471/64000000000000 : ℝ) ≤ (-16766254316996283939/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_673 (by norm_num)
  have hUr : potential (27652481574401/32000000000000 : ℝ) ≤ (-16766254316996283939/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_674 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_673
  linarith only [hU, hF]

theorem cell_bound_674 : cellBound ((27652481574401/32000000000000 : ℚ) : ℝ) ((56558325853133/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (27652481574401/32000000000000 : ℝ) ≤ (-30815903920681131479/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_674 (by norm_num)
  have hUr : potential (56558325853133/64000000000000 : ℝ) ≤ (-30815903920681131479/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_675 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_674
  linarith only [hU, hF]

theorem cell_bound_675 : cellBound ((56558325853133/64000000000000 : ℚ) : ℝ) ((7226461069683/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (56558325853133/64000000000000 : ℝ) ≤ (-1761919606880665003/6250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_675 (by norm_num)
  have hUr : potential (7226461069683/8000000000000 : ℝ) ≤ (-1761919606880665003/6250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_676 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_675
  linarith only [hU, hF]

theorem cell_bound_676 : cellBound ((7226461069683/8000000000000 : ℚ) : ℝ) ((30159206983063/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (7226461069683/8000000000000 : ℝ) ≤ (-23185476827357388669/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_676 (by norm_num)
  have hUr : potential (30159206983063/32000000000000 : ℝ) ≤ (-23185476827357388669/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_677 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_676
  linarith only [hU, hF]

theorem cell_bound_677 : cellBound ((30159206983063/32000000000000 : ℚ) : ℝ) ((15706284843697/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (30159206983063/32000000000000 : ℝ) ≤ (-18468653397334900241/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_677 (by norm_num)
  have hUr : potential (15706284843697/16000000000000 : ℝ) ≤ (-18468653397334900241/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_678 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_677
  linarith only [hU, hF]

theorem cell_bound_678 : cellBound ((15706284843697/16000000000000 : ℚ) : ℝ) ((4239911887007/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (15706284843697/16000000000000 : ℝ) ≤ (-976182029600696261/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_678 (by norm_num)
  have hUr : potential (4239911887007/4000000000000 : ℝ) ≤ (-976182029600696261/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_679 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_678
  linarith only [hU, hF]

theorem cell_bound_679 : cellBound ((4239911887007/4000000000000 : ℚ) : ℝ) ((18213010252359/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (4239911887007/4000000000000 : ℝ) ≤ (-371382903737138001/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_679 (by norm_num)
  have hUr : potential (18213010252359/16000000000000 : ℝ) ≤ (-371382903737138001/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_680 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_679
  linarith only [hU, hF]

theorem cell_bound_680 : cellBound ((18213010252359/16000000000000 : ℚ) : ℝ) ((1946637295669/1600000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (18213010252359/16000000000000 : ℝ) ≤ (5392069717486622537/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_680 (by norm_num)
  have hUr : potential (1946637295669/1600000000000 : ℝ) ≤ (5392069717486622537/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_681 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_680
  linarith only [hU, hF]

theorem cell_bound_681 : cellBound ((1946637295669/1600000000000 : ℚ) : ℝ) ((2746637295669/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1946637295669/1600000000000 : ℝ) ≤ (9161506331765032541/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_681 (by norm_num)
  have hUr : potential (2746637295669/2000000000000 : ℝ) ≤ (9161506331765032541/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_682 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_681
  linarith only [hU, hF]

theorem cell_bound_682 : cellBound ((2746637295669/2000000000000 : ℚ) : ℝ) ((6746637295669/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2746637295669/2000000000000 : ℝ) ≤ (9916412084762805207/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_682 (by norm_num)
  have hUr : potential (6746637295669/4000000000000 : ℝ) ≤ (9916412084762805207/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_683 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_682
  linarith only [hU, hF]

theorem cell_bound_683 : cellBound ((6746637295669/4000000000000 : ℚ) : ℝ) ((2/1 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (6746637295669/4000000000000 : ℝ) ≤ (28468603721507761461/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_683 (by norm_num)
  have hUr : potential (2/1 : ℝ) ≤ (28468603721507761461/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_684 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_683
  linarith only [hU, hF]

#print axioms cell_bound_683
end Zeta5AppendixNumerics
