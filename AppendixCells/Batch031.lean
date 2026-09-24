import AppendixCellBase
import AppendixField.Batch061
import AppendixField.Batch062
import AppendixField.Batch063
import AppendixPotential.Batch062
import AppendixPotential.Batch063
import AppendixPotential.Batch064
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_496 : cellBound ((4364155818193/8000000000000 : ℚ) : ℝ) ((69906379973123/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (4364155818193/8000000000000 : ℝ) ≤ (-47989436117082278153/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_496 (by norm_num)
  have hUr : potential (69906379973123/128000000000000 : ℝ) ≤ (-47989436117082278153/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_497 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_496
  linarith only [hU, hF]

theorem cell_bound_497 : cellBound ((69906379973123/128000000000000 : ℚ) : ℝ) ((34993133427579/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (69906379973123/128000000000000 : ℝ) ≤ (-5989761709304896647/6250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_497 (by norm_num)
  have hUr : potential (34993133427579/64000000000000 : ℝ) ≤ (-5989761709304896647/6250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_498 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_497
  linarith only [hU, hF]

theorem cell_bound_498 : cellBound ((34993133427579/64000000000000 : ℚ) : ℝ) ((70066153737193/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (34993133427579/64000000000000 : ℝ) ≤ (-76555244983964373/80000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_498 (by norm_num)
  have hUr : potential (70066153737193/128000000000000 : ℝ) ≤ (-76555244983964373/80000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_499 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_498
  linarith only [hU, hF]

theorem cell_bound_499 : cellBound ((70066153737193/128000000000000 : ℚ) : ℝ) ((17536510154807/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (70066153737193/128000000000000 : ℝ) ≤ (-19110493635196345979/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_499 (by norm_num)
  have hUr : potential (17536510154807/32000000000000 : ℝ) ≤ (-19110493635196345979/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_500 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_499
  linarith only [hU, hF]

theorem cell_bound_500 : cellBound ((17536510154807/32000000000000 : ℚ) : ℝ) ((35152907191649/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (17536510154807/32000000000000 : ℝ) ≤ (-47635438689173243939/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_500 (by norm_num)
  have hUr : potential (35152907191649/64000000000000 : ℝ) ≤ (-47635438689173243939/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_501 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_500
  linarith only [hU, hF]

theorem cell_bound_501 : cellBound ((35152907191649/64000000000000 : ℚ) : ℝ) ((8808198518421/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (35152907191649/64000000000000 : ℝ) ≤ (-18998267055216478447/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_501 (by norm_num)
  have hUr : potential (8808198518421/16000000000000 : ℝ) ≤ (-18998267055216478447/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_502 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_501
  linarith only [hU, hF]

theorem cell_bound_502 : cellBound ((8808198518421/16000000000000 : ℚ) : ℝ) ((35312680955719/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (8808198518421/16000000000000 : ℝ) ≤ (-94713768041631904447/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_502 (by norm_num)
  have hUr : potential (35312680955719/64000000000000 : ℝ) ≤ (-94713768041631904447/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_503 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_502
  linarith only [hU, hF]

theorem cell_bound_503 : cellBound ((35312680955719/64000000000000 : ℚ) : ℝ) ((17696283918877/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (35312680955719/64000000000000 : ℝ) ≤ (-47219053827575327263/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_503 (by norm_num)
  have hUr : potential (17696283918877/32000000000000 : ℝ) ≤ (-47219053827575327263/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_504 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_503
  linarith only [hU, hF]

theorem cell_bound_504 : cellBound ((17696283918877/32000000000000 : ℚ) : ℝ) ((35472454719789/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (17696283918877/32000000000000 : ℝ) ≤ (-94164291620727725289/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_504 (by norm_num)
  have hUr : potential (35472454719789/64000000000000 : ℝ) ≤ (-94164291620727725289/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_505 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_504
  linarith only [hU, hF]

theorem cell_bound_505 : cellBound ((35472454719789/64000000000000 : ℚ) : ℝ) ((1111010675057/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (35472454719789/64000000000000 : ℝ) ≤ (-93892261417748629113/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_505 (by norm_num)
  have hUr : potential (1111010675057/2000000000000 : ℝ) ≤ (-93892261417748629113/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_506 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_505
  linarith only [hU, hF]

theorem cell_bound_506 : cellBound ((1111010675057/2000000000000 : ℚ) : ℝ) ((35632228483859/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1111010675057/2000000000000 : ℝ) ≤ (-93621963133449474753/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_506 (by norm_num)
  have hUr : potential (35632228483859/64000000000000 : ℝ) ≤ (-93621963133449474753/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_507 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_506
  linarith only [hU, hF]

theorem cell_bound_507 : cellBound ((35632228483859/64000000000000 : ℚ) : ℝ) ((17856057682947/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (35632228483859/64000000000000 : ℝ) ≤ (-93353346327715613813/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_507 (by norm_num)
  have hUr : potential (17856057682947/32000000000000 : ℝ) ≤ (-93353346327715613813/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_508 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_507
  linarith only [hU, hF]

theorem cell_bound_508 : cellBound ((17856057682947/32000000000000 : ℚ) : ℝ) ((35792002247929/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (17856057682947/32000000000000 : ℝ) ≤ (-23271590968851073303/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_508 (by norm_num)
  have hUr : potential (35792002247929/64000000000000 : ℝ) ≤ (-23271590968851073303/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_509 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_508
  linarith only [hU, hF]

theorem cell_bound_509 : cellBound ((35792002247929/64000000000000 : ℚ) : ℝ) ((8967972282491/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (35792002247929/64000000000000 : ℝ) ≤ (-11602621428094714673/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_509 (by norm_num)
  have hUr : potential (8967972282491/16000000000000 : ℝ) ≤ (-11602621428094714673/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_510 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_509
  linarith only [hU, hF]

theorem cell_bound_510 : cellBound ((8967972282491/16000000000000 : ℚ) : ℝ) ((35951776011999/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (8967972282491/16000000000000 : ℝ) ≤ (-92557127817217288261/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_510 (by norm_num)
  have hUr : potential (35951776011999/64000000000000 : ℝ) ≤ (-92557127817217288261/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_511 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_510
  linarith only [hU, hF]

theorem cell_bound_511 : cellBound ((35951776011999/64000000000000 : ℚ) : ℝ) ((18015831447017/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (35951776011999/64000000000000 : ℝ) ≤ (-18458958733444313223/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_511 (by norm_num)
  have hUr : potential (18015831447017/32000000000000 : ℝ) ≤ (-18458958733444313223/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_512 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_511
  linarith only [hU, hF]

#print axioms cell_bound_511
end Zeta5AppendixNumerics
