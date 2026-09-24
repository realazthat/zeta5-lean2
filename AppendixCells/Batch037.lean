import AppendixCellBase
import AppendixField.Batch073
import AppendixField.Batch074
import AppendixField.Batch075
import AppendixPotential.Batch074
import AppendixPotential.Batch075
import AppendixPotential.Batch076
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_592 : cellBound ((8782653354179/12800000000000 : ℚ) : ℝ) ((10991296491131/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (8782653354179/12800000000000 : ℝ) ≤ (-64766392087427052227/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_592 (by norm_num)
  have hUr : potential (10991296491131/16000000000000 : ℝ) ≤ (-64766392087427052227/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_593 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_592
  linarith only [hU, hF]

theorem cell_bound_593 : cellBound ((10991296491131/16000000000000 : ℚ) : ℝ) ((44017105158153/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (10991296491131/16000000000000 : ℝ) ≤ (-64599898562593568309/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_593 (by norm_num)
  have hUr : potential (44017105158153/64000000000000 : ℝ) ≤ (-64599898562593568309/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_594 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_593
  linarith only [hU, hF]

theorem cell_bound_594 : cellBound ((44017105158153/64000000000000 : ℚ) : ℝ) ((22034512175891/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (44017105158153/64000000000000 : ℝ) ≤ (-64434209672379457217/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_594 (by norm_num)
  have hUr : potential (22034512175891/32000000000000 : ℝ) ≤ (-64434209672379457217/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_595 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_594
  linarith only [hU, hF]

theorem cell_bound_595 : cellBound ((22034512175891/32000000000000 : ℚ) : ℝ) ((44120943545411/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (22034512175891/32000000000000 : ℝ) ≤ (-401683116952933049/625000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_595 (by norm_num)
  have hUr : potential (44120943545411/64000000000000 : ℝ) ≤ (-401683116952933049/625000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_596 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_595
  linarith only [hU, hF]

theorem cell_bound_596 : cellBound ((44120943545411/64000000000000 : ℚ) : ℝ) ((276080392119/400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (44120943545411/64000000000000 : ℝ) ≤ (-32052570421662752749/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_596 (by norm_num)
  have hUr : potential (276080392119/400000000000 : ℝ) ≤ (-32052570421662752749/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_597 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_596
  linarith only [hU, hF]

theorem cell_bound_597 : cellBound ((276080392119/400000000000 : ℚ) : ℝ) ((44224781932669/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (276080392119/400000000000 : ℝ) ≤ (-63941712695807193469/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_597 (by norm_num)
  have hUr : potential (44224781932669/64000000000000 : ℝ) ≤ (-63941712695807193469/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_598 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_597
  linarith only [hU, hF]

theorem cell_bound_598 : cellBound ((44224781932669/64000000000000 : ℚ) : ℝ) ((22138350563149/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (44224781932669/64000000000000 : ℝ) ≤ (-12755798658263085883/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_598 (by norm_num)
  have hUr : potential (22138350563149/32000000000000 : ℝ) ≤ (-12755798658263085883/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_599 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_598
  linarith only [hU, hF]

theorem cell_bound_599 : cellBound ((22138350563149/32000000000000 : ℚ) : ℝ) ((44328620319927/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (22138350563149/32000000000000 : ℝ) ≤ (-63616962175232049351/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_599 (by norm_num)
  have hUr : potential (44328620319927/64000000000000 : ℝ) ≤ (-63616962175232049351/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_600 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_599
  linarith only [hU, hF]

theorem cell_bound_600 : cellBound ((44328620319927/64000000000000 : ℚ) : ℝ) ((11095134878389/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (44328620319927/64000000000000 : ℝ) ≤ (-63455600863324981253/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_600 (by norm_num)
  have hUr : potential (11095134878389/16000000000000 : ℝ) ≤ (-63455600863324981253/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_601 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_600
  linarith only [hU, hF]

theorem cell_bound_601 : cellBound ((11095134878389/16000000000000 : ℚ) : ℝ) ((8886491741437/12800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (11095134878389/16000000000000 : ℝ) ≤ (-6329489165006766893/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_601 (by norm_num)
  have hUr : potential (8886491741437/12800000000000 : ℝ) ≤ (-6329489165006766893/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_602 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_601
  linarith only [hU, hF]

theorem cell_bound_602 : cellBound ((8886491741437/12800000000000 : ℚ) : ℝ) ((22242188950407/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (8886491741437/12800000000000 : ℝ) ≤ (-15783704620934744949/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_602 (by norm_num)
  have hUr : potential (22242188950407/32000000000000 : ℝ) ≤ (-15783704620934744949/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_603 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_602
  linarith only [hU, hF]

theorem cell_bound_603 : cellBound ((22242188950407/32000000000000 : ℚ) : ℝ) ((5573527036009/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (22242188950407/32000000000000 : ℝ) ≤ (-31408259155498142053/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_603 (by norm_num)
  have hUr : potential (5573527036009/8000000000000 : ℝ) ≤ (-31408259155498142053/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_604 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_603
  linarith only [hU, hF]

theorem cell_bound_604 : cellBound ((5573527036009/8000000000000 : ℚ) : ℝ) ((4469205467533/6400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (5573527036009/8000000000000 : ℝ) ≤ (-31250293378707208373/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_604 (by norm_num)
  have hUr : potential (4469205467533/6400000000000 : ℝ) ≤ (-31250293378707208373/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_605 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_604
  linarith only [hU, hF]

theorem cell_bound_605 : cellBound ((4469205467533/6400000000000 : ℚ) : ℝ) ((11198973265647/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (4469205467533/6400000000000 : ℝ) ≤ (-31093461287703440817/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_605 (by norm_num)
  have hUr : potential (11198973265647/16000000000000 : ℝ) ≤ (-31093461287703440817/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_606 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_605
  linarith only [hU, hF]

theorem cell_bound_606 : cellBound ((11198973265647/16000000000000 : ℚ) : ℝ) ((22449865724923/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (11198973265647/16000000000000 : ℝ) ≤ (-61875434539300347853/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_606 (by norm_num)
  have hUr : potential (22449865724923/32000000000000 : ℝ) ≤ (-61875434539300347853/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_607 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_606
  linarith only [hU, hF]

theorem cell_bound_607 : cellBound ((22449865724923/32000000000000 : ℚ) : ℝ) ((2812723114819/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (22449865724923/32000000000000 : ℝ) ≤ (-30783019989264566129/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_607 (by norm_num)
  have hUr : potential (2812723114819/4000000000000 : ℝ) ≤ (-30783019989264566129/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_608 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_607
  linarith only [hU, hF]

#print axioms cell_bound_607
end Zeta5AppendixNumerics
