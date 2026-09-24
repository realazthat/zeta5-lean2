import AppendixCellBase
import AppendixField.Batch005
import AppendixField.Batch006
import AppendixField.Batch007
import AppendixPotential.Batch006
import AppendixPotential.Batch007
import AppendixPotential.Batch008
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_48 : cellBound ((11896075201/640000000000 : ℚ) : ℝ) ((605192942919/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (11896075201/640000000000 : ℝ) ≤ (-17592622528833800887/6250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_48 (by norm_num)
  have hUr : potential (605192942919/32000000000000 : ℝ) ≤ (-17592622528833800887/6250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_49 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_48
  linarith only [hU, hF]

theorem cell_bound_49 : cellBound ((605192942919/32000000000000 : ℚ) : ℝ) ((153895531447/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (605192942919/32000000000000 : ℝ) ≤ (-140666683483603195837/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_49 (by norm_num)
  have hUr : potential (153895531447/8000000000000 : ℝ) ≤ (-140666683483603195837/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_50 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_49
  linarith only [hU, hF]

theorem cell_bound_50 : cellBound ((153895531447/8000000000000 : ℚ) : ℝ) ((318180245763/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (153895531447/8000000000000 : ℝ) ≤ (-140527893592704965609/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_50 (by norm_num)
  have hUr : potential (318180245763/16000000000000 : ℝ) ≤ (-140527893592704965609/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_51 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_50
  linarith only [hU, hF]

theorem cell_bound_51 : cellBound ((318180245763/16000000000000 : ℚ) : ℝ) ((41071178579/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (318180245763/16000000000000 : ℝ) ≤ (-280800173891470908411/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_51 (by norm_num)
  have hUr : potential (41071178579/2000000000000 : ℝ) ≤ (-280800173891470908411/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_52 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_51
  linarith only [hU, hF]

theorem cell_bound_52 : cellBound ((41071178579/2000000000000 : ℚ) : ℝ) ((34934779437/1600000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (41071178579/2000000000000 : ℝ) ≤ (-280340841537137902271/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_52 (by norm_num)
  have hUr : potential (34934779437/1600000000000 : ℝ) ≤ (-280340841537137902271/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_53 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_52
  linarith only [hU, hF]

theorem cell_bound_53 : cellBound ((34934779437/1600000000000 : ℚ) : ℝ) ((92531540027/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (34934779437/1600000000000 : ℝ) ≤ (-69983804241556289193/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_53 (by norm_num)
  have hUr : potential (92531540027/4000000000000 : ℝ) ≤ (-69983804241556289193/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_54 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_53
  linarith only [hU, hF]

theorem cell_bound_54 : cellBound ((92531540027/4000000000000 : ℚ) : ℝ) ((6432545181/250000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (92531540027/4000000000000 : ℝ) ≤ (-55847936875570507079/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_54 (by norm_num)
  have hUr : potential (6432545181/250000000000 : ℝ) ≤ (-55847936875570507079/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_55 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_54
  linarith only [hU, hF]

theorem cell_bound_55 : cellBound ((6432545181/250000000000 : ℚ) : ℝ) ((213931144553/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (6432545181/250000000000 : ℝ) ≤ (-27726204545895238673/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_55 (by norm_num)
  have hUr : potential (213931144553/8000000000000 : ℝ) ≤ (-27726204545895238673/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_56 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_55
  linarith only [hU, hF]

theorem cell_bound_56 : cellBound ((213931144553/8000000000000 : ℚ) : ℝ) ((435951987867/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (213931144553/8000000000000 : ℝ) ≤ (-276764410723821756621/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_56 (by norm_num)
  have hUr : potential (435951987867/16000000000000 : ℝ) ≤ (-276764410723821756621/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_57 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_56
  linarith only [hU, hF]

theorem cell_bound_57 : cellBound ((435951987867/16000000000000 : ℚ) : ℝ) ((111010421657/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (435951987867/16000000000000 : ℝ) ≤ (-276333514745848384411/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_57 (by norm_num)
  have hUr : potential (111010421657/4000000000000 : ℝ) ≤ (-276333514745848384411/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_58 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_57
  linarith only [hU, hF]

theorem cell_bound_58 : cellBound ((111010421657/4000000000000 : ℚ) : ℝ) ((452131385389/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (111010421657/4000000000000 : ℝ) ≤ (-275946578583600782703/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_58 (by norm_num)
  have hUr : potential (452131385389/16000000000000 : ℝ) ≤ (-275946578583600782703/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_59 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_58
  linarith only [hU, hF]

theorem cell_bound_59 : cellBound ((452131385389/16000000000000 : ℚ) : ℝ) ((912352469539/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (452131385389/16000000000000 : ℝ) ≤ (-137882841978892228209/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_59 (by norm_num)
  have hUr : potential (912352469539/32000000000000 : ℝ) ≤ (-137882841978892228209/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_60 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_59
  linarith only [hU, hF]

theorem cell_bound_60 : cellBound ((912352469539/32000000000000 : ℚ) : ℝ) ((9204421683/320000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (912352469539/32000000000000 : ℝ) ≤ (-68897947415335831043/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_60 (by norm_num)
  have hUr : potential (9204421683/320000000000 : ℝ) ≤ (-68897947415335831043/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_61 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_60
  linarith only [hU, hF]

theorem cell_bound_61 : cellBound ((9204421683/320000000000 : ℚ) : ℝ) ((928531867061/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (9204421683/320000000000 : ℝ) ≤ (-275424120272640363291/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_61 (by norm_num)
  have hUr : potential (928531867061/32000000000000 : ℝ) ≤ (-275424120272640363291/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_62 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_61
  linarith only [hU, hF]

theorem cell_bound_62 : cellBound ((928531867061/32000000000000 : ℚ) : ℝ) ((468310782911/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (928531867061/32000000000000 : ℝ) ≤ (-275262042833101729769/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_62 (by norm_num)
  have hUr : potential (468310782911/16000000000000 : ℝ) ≤ (-275262042833101729769/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_63 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_62
  linarith only [hU, hF]

theorem cell_bound_63 : cellBound ((468310782911/16000000000000 : ℚ) : ℝ) ((944711264583/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (468310782911/16000000000000 : ℝ) ≤ (-275105031983238343023/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_63 (by norm_num)
  have hUr : potential (944711264583/32000000000000 : ℝ) ≤ (-275105031983238343023/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_64 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_63
  linarith only [hU, hF]

#print axioms cell_bound_63
end Zeta5AppendixNumerics
