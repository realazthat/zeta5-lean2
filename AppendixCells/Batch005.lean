import AppendixCellBase
import AppendixField.Batch009
import AppendixField.Batch010
import AppendixField.Batch011
import AppendixPotential.Batch010
import AppendixPotential.Batch011
import AppendixPotential.Batch012
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_80 : cellBound ((1412931037823/32000000000000 : ℚ) : ℝ) ((71843627457/1600000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1412931037823/32000000000000 : ℝ) ≤ (-133105138160089795671/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_80 (by norm_num)
  have hUr : potential (71843627457/1600000000000 : ℝ) ≤ (-133105138160089795671/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_81 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_80
  linarith only [hU, hF]

theorem cell_bound_81 : cellBound ((71843627457/1600000000000 : ℚ) : ℝ) ((2897686609597/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (71843627457/1600000000000 : ℝ) ≤ (-265930208454059427849/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_81 (by norm_num)
  have hUr : potential (2897686609597/64000000000000 : ℝ) ≤ (-265930208454059427849/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_82 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_81
  linarith only [hU, hF]

theorem cell_bound_82 : cellBound ((2897686609597/64000000000000 : ℚ) : ℝ) ((1460814060457/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2897686609597/64000000000000 : ℝ) ≤ (-265662008385827419521/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_82 (by norm_num)
  have hUr : potential (1460814060457/32000000000000 : ℝ) ≤ (-265662008385827419521/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_83 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_82
  linarith only [hU, hF]

theorem cell_bound_83 : cellBound ((1460814060457/32000000000000 : ℚ) : ℝ) ((2945569632231/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1460814060457/32000000000000 : ℝ) ≤ (-66351025930724103983/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_83 (by norm_num)
  have hUr : potential (2945569632231/64000000000000 : ℝ) ≤ (-66351025930724103983/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_84 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_83
  linarith only [hU, hF]

theorem cell_bound_84 : cellBound ((2945569632231/64000000000000 : ℚ) : ℝ) ((742377785887/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2945569632231/64000000000000 : ℝ) ≤ (-16572204066664713469/6250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_84 (by norm_num)
  have hUr : potential (742377785887/16000000000000 : ℝ) ≤ (-16572204066664713469/6250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_85 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_84
  linarith only [hU, hF]

theorem cell_bound_85 : cellBound ((742377785887/16000000000000 : ℚ) : ℝ) ((598690530973/12800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (742377785887/16000000000000 : ℝ) ≤ (-16557156756969724473/6250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_85 (by norm_num)
  have hUr : potential (598690530973/12800000000000 : ℝ) ≤ (-16557156756969724473/6250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_86 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_85
  linarith only [hU, hF]

theorem cell_bound_86 : cellBound ((598690530973/12800000000000 : ℚ) : ℝ) ((1508697083091/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (598690530973/12800000000000 : ℝ) ≤ (-5293620581795602299/2000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_86 (by norm_num)
  have hUr : potential (1508697083091/32000000000000 : ℝ) ≤ (-5293620581795602299/2000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_87 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_86
  linarith only [hU, hF]

theorem cell_bound_87 : cellBound ((1508697083091/32000000000000 : ℚ) : ℝ) ((3041335677499/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1508697083091/32000000000000 : ℝ) ≤ (-264454160756986514317/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_87 (by norm_num)
  have hUr : potential (3041335677499/64000000000000 : ℝ) ≤ (-264454160756986514317/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_88 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_87
  linarith only [hU, hF]

theorem cell_bound_88 : cellBound ((3041335677499/64000000000000 : ℚ) : ℝ) ((191579824301/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (3041335677499/64000000000000 : ℝ) ≤ (-52846668221988895639/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_88 (by norm_num)
  have hUr : potential (191579824301/4000000000000 : ℝ) ≤ (-52846668221988895639/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_89 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_88
  linarith only [hU, hF]

theorem cell_bound_89 : cellBound ((191579824301/4000000000000 : ℚ) : ℝ) ((3089218700133/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (191579824301/4000000000000 : ℝ) ≤ (-132009045549624641339/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_89 (by norm_num)
  have hUr : potential (3089218700133/64000000000000 : ℝ) ≤ (-132009045549624641339/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_90 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_89
  linarith only [hU, hF]

theorem cell_bound_90 : cellBound ((3089218700133/64000000000000 : ℚ) : ℝ) ((62263204229/1280000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (3089218700133/64000000000000 : ℝ) ≤ (-263807997880725797281/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_90 (by norm_num)
  have hUr : potential (62263204229/1280000000000 : ℝ) ≤ (-263807997880725797281/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_91 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_90
  linarith only [hU, hF]

theorem cell_bound_91 : cellBound ((62263204229/1280000000000 : ℚ) : ℝ) ((3137101722767/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (62263204229/1280000000000 : ℝ) ≤ (-131801351077383215073/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_91 (by norm_num)
  have hUr : potential (3137101722767/64000000000000 : ℝ) ≤ (-131801351077383215073/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_92 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_91
  linarith only [hU, hF]

theorem cell_bound_92 : cellBound ((3137101722767/64000000000000 : ℚ) : ℝ) ((790260808521/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (3137101722767/64000000000000 : ℝ) ≤ (-263401888961425916419/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_92 (by norm_num)
  have hUr : potential (790260808521/16000000000000 : ℝ) ≤ (-263401888961425916419/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_93 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_92
  linarith only [hU, hF]

theorem cell_bound_93 : cellBound ((790260808521/16000000000000 : ℚ) : ℝ) ((3184984745401/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (790260808521/16000000000000 : ℝ) ≤ (-26320527971273523797/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_93 (by norm_num)
  have hUr : potential (3184984745401/64000000000000 : ℝ) ≤ (-26320527971273523797/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_94 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_93
  linarith only [hU, hF]

theorem cell_bound_94 : cellBound ((3184984745401/64000000000000 : ℚ) : ℝ) ((1604463128359/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (3184984745401/64000000000000 : ℝ) ≤ (-52602525305170464929/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_94 (by norm_num)
  have hUr : potential (1604463128359/32000000000000 : ℝ) ≤ (-52602525305170464929/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_95 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_94
  linarith only [hU, hF]

theorem cell_bound_95 : cellBound ((1604463128359/32000000000000 : ℚ) : ℝ) ((646573553607/12800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1604463128359/32000000000000 : ℝ) ≤ (-131411853770036829623/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_95 (by norm_num)
  have hUr : potential (646573553607/12800000000000 : ℝ) ≤ (-131411853770036829623/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_96 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_95
  linarith only [hU, hF]

#print axioms cell_bound_95
end Zeta5AppendixNumerics
