import AppendixCellBase
import AppendixField.Batch031
import AppendixField.Batch032
import AppendixField.Batch033
import AppendixPotential.Batch032
import AppendixPotential.Batch033
import AppendixPotential.Batch034
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_256 : cellBound ((6947186163633/32000000000000 : ℚ) : ℝ) ((13928492444353/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (6947186163633/32000000000000 : ℝ) ≤ (-94546842745503946737/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_256 (by norm_num)
  have hUr : potential (13928492444353/64000000000000 : ℝ) ≤ (-94546842745503946737/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_257 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_256
  linarith only [hU, hF]

theorem cell_bound_257 : cellBound ((13928492444353/64000000000000 : ℚ) : ℝ) ((87266328509/400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (13928492444353/64000000000000 : ℝ) ≤ (-188896268383526043553/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_257 (by norm_num)
  have hUr : potential (87266328509/400000000000 : ℝ) ≤ (-188896268383526043553/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_258 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_257
  linarith only [hU, hF]

theorem cell_bound_258 : cellBound ((87266328509/400000000000 : ℚ) : ℝ) ((13996732678527/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (87266328509/400000000000 : ℝ) ≤ (-188700575451474114181/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_258 (by norm_num)
  have hUr : potential (13996732678527/64000000000000 : ℝ) ≤ (-188700575451474114181/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_259 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_258
  linarith only [hU, hF]

theorem cell_bound_259 : cellBound ((13996732678527/64000000000000 : ℚ) : ℝ) ((7015426397807/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (13996732678527/64000000000000 : ℝ) ≤ (-94253272992795003859/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_259 (by norm_num)
  have hUr : potential (7015426397807/32000000000000 : ℝ) ≤ (-94253272992795003859/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_260 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_259
  linarith only [hU, hF]

theorem cell_bound_260 : cellBound ((7015426397807/32000000000000 : ℚ) : ℝ) ((14064972912701/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (7015426397807/32000000000000 : ℝ) ≤ (-188314122811140388007/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_260 (by norm_num)
  have hUr : potential (14064972912701/64000000000000 : ℝ) ≤ (-188314122811140388007/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_261 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_260
  linarith only [hU, hF]

theorem cell_bound_261 : cellBound ((14064972912701/64000000000000 : ℚ) : ℝ) ((3524773257447/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (14064972912701/64000000000000 : ℝ) ≤ (-188123252942681885239/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_261 (by norm_num)
  have hUr : potential (3524773257447/16000000000000 : ℝ) ≤ (-188123252942681885239/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_262 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_261
  linarith only [hU, hF]

theorem cell_bound_262 : cellBound ((3524773257447/16000000000000 : ℚ) : ℝ) ((4522628207/20480000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (3524773257447/16000000000000 : ℝ) ≤ (-11745867924299822277/6250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_262 (by norm_num)
  have hUr : potential (4522628207/20480000000 : ℝ) ≤ (-11745867924299822277/6250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_263 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_262
  linarith only [hU, hF]

theorem cell_bound_263 : cellBound ((4522628207/20480000000 : ℚ) : ℝ) ((7083666631981/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (4522628207/20480000000 : ℝ) ≤ (-46936494498823667577/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_263 (by norm_num)
  have hUr : potential (7083666631981/32000000000000 : ℝ) ≤ (-46936494498823667577/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_264 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_263
  linarith only [hU, hF]

theorem cell_bound_264 : cellBound ((7083666631981/32000000000000 : ℚ) : ℝ) ((14201453381049/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (7083666631981/32000000000000 : ℝ) ≤ (-187559482832739172021/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_264 (by norm_num)
  have hUr : potential (14201453381049/64000000000000 : ℝ) ≤ (-187559482832739172021/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_265 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_264
  linarith only [hU, hF]

theorem cell_bound_265 : cellBound ((14201453381049/64000000000000 : ℚ) : ℝ) ((1779446687267/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (14201453381049/64000000000000 : ℝ) ≤ (-93687180170474236439/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_265 (by norm_num)
  have hUr : potential (1779446687267/8000000000000 : ℝ) ≤ (-93687180170474236439/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_266 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_265
  linarith only [hU, hF]

theorem cell_bound_266 : cellBound ((1779446687267/8000000000000 : ℚ) : ℝ) ((14269693615223/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1779446687267/8000000000000 : ℝ) ≤ (-93595285960624827367/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_266 (by norm_num)
  have hUr : potential (14269693615223/64000000000000 : ℝ) ≤ (-93595285960624827367/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_267 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_266
  linarith only [hU, hF]

theorem cell_bound_267 : cellBound ((14269693615223/64000000000000 : ℚ) : ℝ) ((1430381373231/6400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (14269693615223/64000000000000 : ℝ) ≤ (-46752020223868186601/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_267 (by norm_num)
  have hUr : potential (1430381373231/6400000000000 : ℝ) ≤ (-46752020223868186601/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_268 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_267
  linarith only [hU, hF]

theorem cell_bound_268 : cellBound ((1430381373231/6400000000000 : ℚ) : ℝ) ((14337933849397/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1430381373231/6400000000000 : ℝ) ≤ (-93413426552623161741/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_268 (by norm_num)
  have hUr : potential (14337933849397/64000000000000 : ℝ) ≤ (-93413426552623161741/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_269 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_268
  linarith only [hU, hF]

theorem cell_bound_269 : cellBound ((14337933849397/64000000000000 : ℚ) : ℝ) ((3593013491621/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (14337933849397/64000000000000 : ℝ) ≤ (-37329371162903749957/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_269 (by norm_num)
  have hUr : potential (3593013491621/16000000000000 : ℝ) ≤ (-37329371162903749957/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_270 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_269
  linarith only [hU, hF]

theorem cell_bound_270 : cellBound ((3593013491621/16000000000000 : ℚ) : ℝ) ((14406174083571/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (3593013491621/16000000000000 : ℝ) ≤ (-186468058116364128371/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_270 (by norm_num)
  have hUr : potential (14406174083571/64000000000000 : ℝ) ≤ (-186468058116364128371/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_271 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_270
  linarith only [hU, hF]

theorem cell_bound_271 : cellBound ((14406174083571/64000000000000 : ℚ) : ℝ) ((7220147100329/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (14406174083571/64000000000000 : ℝ) ≤ (-37258086118517577303/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_271 (by norm_num)
  have hUr : potential (7220147100329/32000000000000 : ℝ) ≤ (-37258086118517577303/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_272 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_271
  linarith only [hU, hF]

#print axioms cell_bound_271
end Zeta5AppendixNumerics
