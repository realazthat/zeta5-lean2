import AppendixCellBase
import AppendixField.Batch057
import AppendixField.Batch058
import AppendixField.Batch059
import AppendixPotential.Batch058
import AppendixPotential.Batch059
import AppendixPotential.Batch060
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_464 : cellBound ((504967497499/1000000000000 : ℚ) : ℝ) ((102052939401/200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (504967497499/1000000000000 : ℝ) ≤ (-26500980133111968371/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_464 (by norm_num)
  have hUr : potential (102052939401/200000000000 : ℝ) ≤ (-26500980133111968371/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_465 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_464
  linarith only [hU, hF]

theorem cell_bound_465 : cellBound ((102052939401/200000000000 : ℚ) : ℝ) ((515561896511/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (102052939401/200000000000 : ℝ) ≤ (-13121818417090085023/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_465 (by norm_num)
  have hUr : potential (515561896511/1000000000000 : ℝ) ≤ (-13121818417090085023/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_466 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_465
  linarith only [hU, hF]

theorem cell_bound_466 : cellBound ((515561896511/1000000000000 : ℚ) : ℝ) ((16577867570387/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (515561896511/1000000000000 : ℝ) ≤ (-51758802663611317249/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_466 (by norm_num)
  have hUr : potential (16577867570387/32000000000000 : ℝ) ≤ (-51758802663611317249/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_467 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_466
  linarith only [hU, hF]

theorem cell_bound_467 : cellBound ((16577867570387/32000000000000 : ℚ) : ℝ) ((8328877226211/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (16577867570387/32000000000000 : ℝ) ≤ (-102639008523423327831/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_467 (by norm_num)
  have hUr : potential (8328877226211/16000000000000 : ℝ) ≤ (-102639008523423327831/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_468 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_467
  linarith only [hU, hF]

theorem cell_bound_468 : cellBound ((8328877226211/16000000000000 : ℚ) : ℝ) ((16737641334457/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (8328877226211/16000000000000 : ℝ) ≤ (-50929594032047396141/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_468 (by norm_num)
  have hUr : potential (16737641334457/32000000000000 : ℝ) ≤ (-50929594032047396141/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_469 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_468
  linarith only [hU, hF]

theorem cell_bound_469 : cellBound ((16737641334457/32000000000000 : ℚ) : ℝ) ((33555169550949/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (16737641334457/32000000000000 : ℝ) ≤ (-50745296581088040531/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_469 (by norm_num)
  have hUr : potential (33555169550949/64000000000000 : ℝ) ≤ (-50745296581088040531/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_470 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_469
  linarith only [hU, hF]

theorem cell_bound_470 : cellBound ((33555169550949/64000000000000 : ℚ) : ℝ) ((4204382054123/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (33555169550949/64000000000000 : ℝ) ≤ (-12641555323196739763/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_470 (by norm_num)
  have hUr : potential (4204382054123/8000000000000 : ℝ) ≤ (-12641555323196739763/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_471 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_470
  linarith only [hU, hF]

theorem cell_bound_471 : cellBound ((4204382054123/8000000000000 : ℚ) : ℝ) ((33714943315019/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (4204382054123/8000000000000 : ℝ) ≤ (-20156600134024741093/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_471 (by norm_num)
  have hUr : potential (33714943315019/64000000000000 : ℝ) ≤ (-20156600134024741093/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_472 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_471
  linarith only [hU, hF]

theorem cell_bound_472 : cellBound ((33714943315019/64000000000000 : ℚ) : ℝ) ((16897415098527/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (33714943315019/64000000000000 : ℝ) ≤ (-25110250137493834231/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_472 (by norm_num)
  have hUr : potential (16897415098527/32000000000000 : ℝ) ≤ (-25110250137493834231/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_473 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_472
  linarith only [hU, hF]

theorem cell_bound_473 : cellBound ((16897415098527/32000000000000 : ℚ) : ℝ) ((33874717079089/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (16897415098527/32000000000000 : ℝ) ≤ (-50052741381149099261/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_473 (by norm_num)
  have hUr : potential (33874717079089/64000000000000 : ℝ) ≤ (-50052741381149099261/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_474 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_473
  linarith only [hU, hF]

theorem cell_bound_474 : cellBound ((33874717079089/64000000000000 : ℚ) : ℝ) ((8488650990281/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (33874717079089/64000000000000 : ℝ) ≤ (-99775699442222595043/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_474 (by norm_num)
  have hUr : potential (8488650990281/16000000000000 : ℝ) ≤ (-99775699442222595043/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_475 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_474
  linarith only [hU, hF]

theorem cell_bound_475 : cellBound ((8488650990281/16000000000000 : ℚ) : ℝ) ((34034490843159/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (8488650990281/16000000000000 : ℝ) ≤ (-49725527046536157687/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_475 (by norm_num)
  have hUr : potential (34034490843159/64000000000000 : ℝ) ≤ (-49725527046536157687/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_476 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_475
  linarith only [hU, hF]

theorem cell_bound_476 : cellBound ((34034490843159/64000000000000 : ℚ) : ℝ) ((17057188862597/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (34034490843159/64000000000000 : ℝ) ≤ (-99131060853763797239/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_476 (by norm_num)
  have hUr : potential (17057188862597/32000000000000 : ℝ) ≤ (-99131060853763797239/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_477 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_476
  linarith only [hU, hF]

theorem cell_bound_477 : cellBound ((17057188862597/32000000000000 : ℚ) : ℝ) ((34194264607229/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (17057188862597/32000000000000 : ℝ) ≤ (-4940765863852215979/5000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_477 (by norm_num)
  have hUr : potential (34194264607229/64000000000000 : ℝ) ≤ (-4940765863852215979/5000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_478 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_477
  linarith only [hU, hF]

theorem cell_bound_478 : cellBound ((34194264607229/64000000000000 : ℚ) : ℝ) ((68468416096493/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (34194264607229/64000000000000 : ℝ) ≤ (-49329465886445673369/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_478 (by norm_num)
  have hUr : potential (68468416096493/128000000000000 : ℝ) ≤ (-49329465886445673369/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_479 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_478
  linarith only [hU, hF]

theorem cell_bound_479 : cellBound ((68468416096493/128000000000000 : ℚ) : ℝ) ((2142134468079/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (68468416096493/128000000000000 : ℝ) ≤ (-12312935800304884781/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_479 (by norm_num)
  have hUr : potential (2142134468079/4000000000000 : ℝ) ≤ (-12312935800304884781/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_480 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_479
  linarith only [hU, hF]

#print axioms cell_bound_479
end Zeta5AppendixNumerics
