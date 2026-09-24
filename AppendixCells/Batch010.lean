import AppendixCellBase
import AppendixField.Batch019
import AppendixField.Batch020
import AppendixField.Batch021
import AppendixPotential.Batch020
import AppendixPotential.Batch021
import AppendixPotential.Batch022
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_160 : cellBound ((3519728384093/32000000000000 : ℚ) : ℝ) ((7061879112973/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (3519728384093/32000000000000 : ℝ) ≤ (-232188797243744913431/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_160 (by norm_num)
  have hUr : potential (7061879112973/64000000000000 : ℝ) ≤ (-232188797243744913431/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_161 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_160
  linarith only [hU, hF]

theorem cell_bound_161 : cellBound ((7061879112973/64000000000000 : ℚ) : ℝ) ((44276884111/400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (7061879112973/64000000000000 : ℝ) ≤ (-116011072430182735933/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_161 (by norm_num)
  have hUr : potential (44276884111/400000000000 : ℝ) ≤ (-116011072430182735933/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_162 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_161
  linarith only [hU, hF]

theorem cell_bound_162 : cellBound ((44276884111/400000000000 : ℚ) : ℝ) ((7106723802547/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (44276884111/400000000000 : ℝ) ≤ (-57964309019003593951/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_162 (by norm_num)
  have hUr : potential (7106723802547/64000000000000 : ℝ) ≤ (-57964309019003593951/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_163 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_162
  linarith only [hU, hF]

theorem cell_bound_163 : cellBound ((7106723802547/64000000000000 : ℚ) : ℝ) ((3564573073667/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (7106723802547/64000000000000 : ℝ) ≤ (-115847003713410761289/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_163 (by norm_num)
  have hUr : potential (3564573073667/32000000000000 : ℝ) ≤ (-115847003713410761289/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_164 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_163
  linarith only [hU, hF]

theorem cell_bound_164 : cellBound ((3564573073667/32000000000000 : ℚ) : ℝ) ((7151568492121/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (3564573073667/32000000000000 : ℝ) ≤ (-57883099916292005859/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_164 (by norm_num)
  have hUr : potential (7151568492121/64000000000000 : ℝ) ≤ (-57883099916292005859/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_165 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_164
  linarith only [hU, hF]

theorem cell_bound_165 : cellBound ((7151568492121/64000000000000 : ℚ) : ℝ) ((1793497709227/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (7151568492121/64000000000000 : ℝ) ≤ (-46274471519307270963/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_165 (by norm_num)
  have hUr : potential (1793497709227/16000000000000 : ℝ) ≤ (-46274471519307270963/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_166 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_165
  linarith only [hU, hF]

theorem cell_bound_166 : cellBound ((1793497709227/16000000000000 : ℚ) : ℝ) ((1439282636339/12800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1793497709227/16000000000000 : ℝ) ≤ (-57803457333927669377/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_166 (by norm_num)
  have hUr : potential (1439282636339/12800000000000 : ℝ) ≤ (-57803457333927669377/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_167 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_166
  linarith only [hU, hF]

theorem cell_bound_167 : cellBound ((1439282636339/12800000000000 : ℚ) : ℝ) ((3609417763241/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1439282636339/12800000000000 : ℝ) ≤ (-115528383410102231989/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_167 (by norm_num)
  have hUr : potential (3609417763241/32000000000000 : ℝ) ≤ (-115528383410102231989/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_168 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_167
  linarith only [hU, hF]

theorem cell_bound_168 : cellBound ((3609417763241/32000000000000 : ℚ) : ℝ) ((7241257871269/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (3609417763241/32000000000000 : ℝ) ≤ (-230901124322243486797/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_168 (by norm_num)
  have hUr : potential (7241257871269/64000000000000 : ℝ) ≤ (-230901124322243486797/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_169 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_168
  linarith only [hU, hF]

theorem cell_bound_169 : cellBound ((7241257871269/64000000000000 : ℚ) : ℝ) ((907960027007/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (7241257871269/64000000000000 : ℝ) ≤ (-230746859214437947871/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_169 (by norm_num)
  have hUr : potential (907960027007/8000000000000 : ℝ) ≤ (-230746859214437947871/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_170 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_169
  linarith only [hU, hF]

theorem cell_bound_170 : cellBound ((907960027007/8000000000000 : ℚ) : ℝ) ((7286102560843/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (907960027007/8000000000000 : ℝ) ≤ (-46118786250561346519/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_170 (by norm_num)
  have hUr : potential (7286102560843/64000000000000 : ℝ) ≤ (-46118786250561346519/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_171 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_170
  linarith only [hU, hF]

theorem cell_bound_171 : cellBound ((7286102560843/64000000000000 : ℚ) : ℝ) ((730852490563/6400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (7286102560843/64000000000000 : ℝ) ≤ (-230442302211735214181/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_171 (by norm_num)
  have hUr : potential (730852490563/6400000000000 : ℝ) ≤ (-230442302211735214181/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_172 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_171
  linarith only [hU, hF]

theorem cell_bound_172 : cellBound ((730852490563/6400000000000 : ℚ) : ℝ) ((7330947250417/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (730852490563/6400000000000 : ℝ) ≤ (-7196623013275908191/3125000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_172 (by norm_num)
  have hUr : potential (7330947250417/64000000000000 : ℝ) ≤ (-7196623013275908191/3125000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_173 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_172
  linarith only [hU, hF]

theorem cell_bound_173 : cellBound ((7330947250417/64000000000000 : ℚ) : ℝ) ((1838342398801/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (7330947250417/64000000000000 : ℝ) ≤ (-230142799689883524747/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_173 (by norm_num)
  have hUr : potential (1838342398801/16000000000000 : ℝ) ≤ (-230142799689883524747/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_174 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_173
  linarith only [hU, hF]

theorem cell_bound_174 : cellBound ((1838342398801/16000000000000 : ℚ) : ℝ) ((3699107142389/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1838342398801/16000000000000 : ℝ) ≤ (-11492404299303256889/5000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_174 (by norm_num)
  have hUr : potential (3699107142389/32000000000000 : ℝ) ≤ (-11492404299303256889/5000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_175 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_174
  linarith only [hU, hF]

theorem cell_bound_175 : cellBound ((3699107142389/32000000000000 : ℚ) : ℝ) ((465191185897/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (3699107142389/32000000000000 : ℝ) ≤ (-57389480542587558187/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_175 (by norm_num)
  have hUr : potential (465191185897/4000000000000 : ℝ) ≤ (-57389480542587558187/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_176 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_175
  linarith only [hU, hF]

#print axioms cell_bound_175
end Zeta5AppendixNumerics
