import AppendixCellBase
import AppendixField.Batch035
import AppendixField.Batch036
import AppendixField.Batch037
import AppendixPotential.Batch036
import AppendixPotential.Batch037
import AppendixPotential.Batch038
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_288 : cellBound ((975023636351/4000000000000 : ℚ) : ℝ) ((3934214662491/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (975023636351/4000000000000 : ℝ) ≤ (-18021427283274520669/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_288 (by norm_num)
  have hUr : potential (3934214662491/16000000000000 : ℝ) ≤ (-18021427283274520669/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_289 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_288
  linarith only [hU, hF]

theorem cell_bound_289 : cellBound ((3934214662491/16000000000000 : ℚ) : ℝ) ((1984167389789/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (3934214662491/16000000000000 : ℝ) ≤ (-44908780394725925329/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_289 (by norm_num)
  have hUr : potential (1984167389789/8000000000000 : ℝ) ≤ (-44908780394725925329/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_290 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_289
  linarith only [hU, hF]

theorem cell_bound_290 : cellBound ((1984167389789/8000000000000 : ℚ) : ℝ) ((504571876719/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1984167389789/8000000000000 : ℝ) ≤ (-22313032241915975817/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_290 (by norm_num)
  have hUr : potential (504571876719/2000000000000 : ℝ) ≤ (-22313032241915975817/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_291 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_290
  linarith only [hU, hF]

theorem cell_bound_291 : cellBound ((504571876719/2000000000000 : ℚ) : ℝ) ((2052407623963/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (504571876719/2000000000000 : ℝ) ≤ (-177407421816639482307/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_291 (by norm_num)
  have hUr : potential (2052407623963/8000000000000 : ℝ) ≤ (-177407421816639482307/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_292 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_291
  linarith only [hU, hF]

theorem cell_bound_292 : cellBound ((2052407623963/8000000000000 : ℚ) : ℝ) ((41730554821/160000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2052407623963/8000000000000 : ℝ) ≤ (-35268392060985615513/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_292 (by norm_num)
  have hUr : potential (41730554821/160000000000 : ℝ) ≤ (-35268392060985615513/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_293 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_292
  linarith only [hU, hF]

theorem cell_bound_293 : cellBound ((41730554821/160000000000 : ℚ) : ℝ) ((269345996903/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (41730554821/160000000000 : ℝ) ≤ (-87148181079114062703/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_293 (by norm_num)
  have hUr : potential (269345996903/1000000000000 : ℝ) ≤ (-87148181079114062703/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_294 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_293
  linarith only [hU, hF]

theorem cell_bound_294 : cellBound ((269345996903/1000000000000 : ℚ) : ℝ) ((8696815458149/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (269345996903/1000000000000 : ℝ) ≤ (-21507203547513098929/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_294 (by norm_num)
  have hUr : potential (8696815458149/32000000000000 : ℝ) ≤ (-21507203547513098929/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_295 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_294
  linarith only [hU, hF]

theorem cell_bound_295 : cellBound ((8696815458149/32000000000000 : ℚ) : ℝ) ((4387279507701/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (8696815458149/32000000000000 : ℝ) ≤ (-10675733169798467137/6250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_295 (by norm_num)
  have hUr : potential (4387279507701/16000000000000 : ℝ) ≤ (-10675733169798467137/6250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_296 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_295
  linarith only [hU, hF]

theorem cell_bound_296 : cellBound ((4387279507701/16000000000000 : ℚ) : ℝ) ((1770460514531/6400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (4387279507701/16000000000000 : ℝ) ≤ (-169736515367997538363/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_296 (by norm_num)
  have hUr : potential (1770460514531/6400000000000 : ℝ) ≤ (-169736515367997538363/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_297 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_296
  linarith only [hU, hF]

theorem cell_bound_297 : cellBound ((1770460514531/6400000000000 : ℚ) : ℝ) ((17782348702563/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1770460514531/6400000000000 : ℝ) ≤ (-169235897319915991167/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_297 (by norm_num)
  have hUr : potential (17782348702563/64000000000000 : ℝ) ≤ (-169235897319915991167/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_298 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_297
  linarith only [hU, hF]

theorem cell_bound_298 : cellBound ((17782348702563/64000000000000 : ℚ) : ℝ) ((2232511532477/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (17782348702563/64000000000000 : ℝ) ≤ (-5273545540722947923/3125000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_298 (by norm_num)
  have hUr : potential (2232511532477/8000000000000 : ℝ) ≤ (-5273545540722947923/3125000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_299 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_298
  linarith only [hU, hF]

theorem cell_bound_299 : cellBound ((2232511532477/8000000000000 : ℚ) : ℝ) ((17937835817069/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2232511532477/8000000000000 : ℝ) ≤ (-84143101116526662383/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_299 (by norm_num)
  have hUr : potential (17937835817069/64000000000000 : ℝ) ≤ (-84143101116526662383/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_300 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_299
  linarith only [hU, hF]

theorem cell_bound_300 : cellBound ((17937835817069/64000000000000 : ℚ) : ℝ) ((9007789687161/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (17937835817069/64000000000000 : ℝ) ≤ (-33566388929251868879/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_300 (by norm_num)
  have hUr : potential (9007789687161/32000000000000 : ℝ) ≤ (-33566388929251868879/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_301 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_300
  linarith only [hU, hF]

theorem cell_bound_301 : cellBound ((9007789687161/32000000000000 : ℚ) : ℝ) ((723732917263/2560000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (9007789687161/32000000000000 : ℝ) ≤ (-41847256269373282343/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_301 (by norm_num)
  have hUr : potential (723732917263/2560000000000 : ℝ) ≤ (-41847256269373282343/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_302 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_301
  linarith only [hU, hF]

theorem cell_bound_302 : cellBound ((723732917263/2560000000000 : ℚ) : ℝ) ((4542766622207/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (723732917263/2560000000000 : ℝ) ≤ (-166956147971380541163/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_302 (by norm_num)
  have hUr : potential (4542766622207/16000000000000 : ℝ) ≤ (-166956147971380541163/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_303 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_302
  linarith only [hU, hF]

theorem cell_bound_303 : cellBound ((4542766622207/16000000000000 : ℚ) : ℝ) ((36419876534909/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (4542766622207/16000000000000 : ℝ) ≤ (-8337157178109253049/5000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_303 (by norm_num)
  have hUr : potential (36419876534909/128000000000000 : ℝ) ≤ (-8337157178109253049/5000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_304 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_303
  linarith only [hU, hF]

#print axioms cell_bound_303
end Zeta5AppendixNumerics
