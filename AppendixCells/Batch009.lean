import AppendixCellBase
import AppendixField.Batch017
import AppendixField.Batch018
import AppendixField.Batch019
import AppendixPotential.Batch018
import AppendixPotential.Batch019
import AppendixPotential.Batch020
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_144 : cellBound ((762218354751/8000000000000 : ℚ) : ℝ) ((24870259471/250000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (762218354751/8000000000000 : ℝ) ≤ (-24024717210889072499/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_144 (by norm_num)
  have hUr : potential (24870259471/250000000000 : ℝ) ≤ (-24024717210889072499/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_145 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_144
  linarith only [hU, hF]

theorem cell_bound_145 : cellBound ((24870259471/250000000000 : ℚ) : ℝ) ((1614118950931/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (24870259471/250000000000 : ℝ) ≤ (-118985820633313905779/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_145 (by norm_num)
  have hUr : potential (1614118950931/16000000000000 : ℝ) ≤ (-118985820633313905779/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_146 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_145
  linarith only [hU, hF]

theorem cell_bound_146 : cellBound ((1614118950931/16000000000000 : ℚ) : ℝ) ((818270647859/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1614118950931/16000000000000 : ℝ) ≤ (-5920177238864442021/2500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_146 (by norm_num)
  have hUr : potential (818270647859/8000000000000 : ℝ) ≤ (-5920177238864442021/2500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_147 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_146
  linarith only [hU, hF]

theorem cell_bound_147 : cellBound ((818270647859/8000000000000 : ℚ) : ℝ) ((331792728101/3200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (818270647859/8000000000000 : ℝ) ≤ (-58958415685439432709/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_147 (by norm_num)
  have hUr : potential (331792728101/3200000000000 : ℝ) ≤ (-58958415685439432709/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_148 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_147
  linarith only [hU, hF]

theorem cell_bound_148 : cellBound ((331792728101/3200000000000 : ℚ) : ℝ) ((3340349625797/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (331792728101/3200000000000 : ℝ) ≤ (-47077665650959990773/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_148 (by norm_num)
  have hUr : potential (3340349625797/32000000000000 : ℝ) ≤ (-47077665650959990773/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_149 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_148
  linarith only [hU, hF]

theorem cell_bound_149 : cellBound ((3340349625797/32000000000000 : ℚ) : ℝ) ((420346496323/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (3340349625797/32000000000000 : ℝ) ≤ (-234963299274532081629/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_149 (by norm_num)
  have hUr : potential (420346496323/4000000000000 : ℝ) ≤ (-234963299274532081629/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_150 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_149
  linarith only [hU, hF]

theorem cell_bound_150 : cellBound ((420346496323/4000000000000 : ℚ) : ℝ) ((3385194315371/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (420346496323/4000000000000 : ℝ) ≤ (-23455520940860516903/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_150 (by norm_num)
  have hUr : potential (3385194315371/32000000000000 : ℝ) ≤ (-23455520940860516903/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_151 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_150
  linarith only [hU, hF]

theorem cell_bound_151 : cellBound ((3385194315371/32000000000000 : ℚ) : ℝ) ((1703808330079/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (3385194315371/32000000000000 : ℝ) ≤ (-11708079734769455079/5000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_151 (by norm_num)
  have hUr : potential (1703808330079/16000000000000 : ℝ) ≤ (-11708079734769455079/5000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_152 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_151
  linarith only [hU, hF]

theorem cell_bound_152 : cellBound ((1703808330079/16000000000000 : ℚ) : ℝ) ((686007800989/6400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1703808330079/16000000000000 : ℝ) ≤ (-29222572993696939227/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_152 (by norm_num)
  have hUr : potential (686007800989/6400000000000 : ℝ) ≤ (-29222572993696939227/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_153 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_152
  linarith only [hU, hF]

theorem cell_bound_153 : cellBound ((686007800989/6400000000000 : ℚ) : ℝ) ((863115337433/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (686007800989/6400000000000 : ℝ) ≤ (-116705357189389828087/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_153 (by norm_num)
  have hUr : potential (863115337433/8000000000000 : ℝ) ≤ (-116705357189389828087/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_154 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_153
  linarith only [hU, hF]

theorem cell_bound_154 : cellBound ((863115337433/8000000000000 : ℚ) : ℝ) ((6927345044251/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (863115337433/8000000000000 : ℝ) ≤ (-233229582454522279881/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_154 (by norm_num)
  have hUr : potential (6927345044251/64000000000000 : ℝ) ≤ (-233229582454522279881/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_155 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_154
  linarith only [hU, hF]

theorem cell_bound_155 : cellBound ((6927345044251/64000000000000 : ℚ) : ℝ) ((3474883694519/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (6927345044251/64000000000000 : ℝ) ≤ (-116525407393694874479/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_155 (by norm_num)
  have hUr : potential (3474883694519/32000000000000 : ℝ) ≤ (-116525407393694874479/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_156 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_155
  linarith only [hU, hF]

theorem cell_bound_156 : cellBound ((3474883694519/32000000000000 : ℚ) : ℝ) ((278887589353/2560000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (3474883694519/32000000000000 : ℝ) ≤ (-232874298003777541817/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_156 (by norm_num)
  have hUr : potential (278887589353/2560000000000 : ℝ) ≤ (-232874298003777541817/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_157 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_156
  linarith only [hU, hF]

theorem cell_bound_157 : cellBound ((278887589353/2560000000000 : ℚ) : ℝ) ((1748653019653/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (278887589353/2560000000000 : ℝ) ≤ (-58174982154531192859/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_157 (by norm_num)
  have hUr : potential (1748653019653/16000000000000 : ℝ) ≤ (-58174982154531192859/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_158 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_157
  linarith only [hU, hF]

theorem cell_bound_158 : cellBound ((1748653019653/16000000000000 : ℚ) : ℝ) ((7017034423399/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1748653019653/16000000000000 : ℝ) ≤ (-232527612170563309307/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_158 (by norm_num)
  have hUr : potential (7017034423399/64000000000000 : ℝ) ≤ (-232527612170563309307/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_159 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_158
  linarith only [hU, hF]

theorem cell_bound_159 : cellBound ((7017034423399/64000000000000 : ℚ) : ℝ) ((3519728384093/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (7017034423399/64000000000000 : ℝ) ≤ (-46471452324267673913/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_159 (by norm_num)
  have hUr : potential (3519728384093/32000000000000 : ℝ) ≤ (-46471452324267673913/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_160 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_159
  linarith only [hU, hF]

#print axioms cell_bound_159
end Zeta5AppendixNumerics
