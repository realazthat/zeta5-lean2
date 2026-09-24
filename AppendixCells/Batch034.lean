import AppendixCellBase
import AppendixField.Batch067
import AppendixField.Batch068
import AppendixField.Batch069
import AppendixPotential.Batch068
import AppendixPotential.Batch069
import AppendixPotential.Batch070
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_544 : cellBound ((4969968043179/8000000000000 : ℚ) : ℝ) ((39828536950369/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (4969968043179/8000000000000 : ℝ) ≤ (-19661314047296956001/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_544 (by norm_num)
  have hUr : potential (39828536950369/64000000000000 : ℝ) ≤ (-19661314047296956001/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_545 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_544
  linarith only [hU, hF]

theorem cell_bound_545 : cellBound ((39828536950369/64000000000000 : ℚ) : ℝ) ((19948664777653/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (39828536950369/64000000000000 : ℝ) ≤ (-78412981897065512463/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_545 (by norm_num)
  have hUr : potential (19948664777653/32000000000000 : ℝ) ≤ (-78412981897065512463/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_546 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_545
  linarith only [hU, hF]

theorem cell_bound_546 : cellBound ((19948664777653/32000000000000 : ℚ) : ℝ) ((39966122160243/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (19948664777653/32000000000000 : ℝ) ≤ (-19545552250228356691/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_546 (by norm_num)
  have hUr : potential (39966122160243/64000000000000 : ℝ) ≤ (-19545552250228356691/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_547 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_546
  linarith only [hU, hF]

theorem cell_bound_547 : cellBound ((39966122160243/64000000000000 : ℚ) : ℝ) ((2001745738259/3200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (39966122160243/64000000000000 : ℝ) ≤ (-4872055029065017617/6250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_547 (by norm_num)
  have hUr : potential (2001745738259/3200000000000 : ℝ) ≤ (-4872055029065017617/6250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_548 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_547
  linarith only [hU, hF]

theorem cell_bound_548 : cellBound ((2001745738259/3200000000000 : ℚ) : ℝ) ((40103707370117/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2001745738259/3200000000000 : ℝ) ≤ (-38862472106222459409/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_548 (by norm_num)
  have hUr : potential (40103707370117/64000000000000 : ℝ) ≤ (-38862472106222459409/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_549 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_548
  linarith only [hU, hF]

theorem cell_bound_549 : cellBound ((40103707370117/64000000000000 : ℚ) : ℝ) ((20086249987527/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (40103707370117/64000000000000 : ℝ) ≤ (-77498352317391118481/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_549 (by norm_num)
  have hUr : potential (20086249987527/32000000000000 : ℝ) ≤ (-77498352317391118481/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_550 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_549
  linarith only [hU, hF]

theorem cell_bound_550 : cellBound ((20086249987527/32000000000000 : ℚ) : ℝ) ((40241292579991/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (20086249987527/32000000000000 : ℝ) ≤ (-7727306052572617993/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_550 (by norm_num)
  have hUr : potential (40241292579991/64000000000000 : ℝ) ≤ (-7727306052572617993/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_551 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_550
  linarith only [hU, hF]

theorem cell_bound_551 : cellBound ((40241292579991/64000000000000 : ℚ) : ℝ) ((1259690162029/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (40241292579991/64000000000000 : ℝ) ≤ (-19262256813966980829/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_551 (by norm_num)
  have hUr : potential (1259690162029/2000000000000 : ℝ) ≤ (-19262256813966980829/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_552 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_551
  linarith only [hU, hF]

theorem cell_bound_552 : cellBound ((1259690162029/2000000000000 : ℚ) : ℝ) ((8075775557973/12800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1259690162029/2000000000000 : ℝ) ≤ (-38413107431435375753/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_552 (by norm_num)
  have hUr : potential (8075775557973/12800000000000 : ℝ) ≤ (-38413107431435375753/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_553 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_552
  linarith only [hU, hF]

theorem cell_bound_553 : cellBound ((8075775557973/12800000000000 : ℚ) : ℝ) ((20223835197401/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (8075775557973/12800000000000 : ℝ) ≤ (-38302293958166894291/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_553 (by norm_num)
  have hUr : potential (20223835197401/32000000000000 : ℝ) ≤ (-38302293958166894291/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_554 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_553
  linarith only [hU, hF]

theorem cell_bound_554 : cellBound ((20223835197401/32000000000000 : ℚ) : ℝ) ((40516462999739/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (20223835197401/32000000000000 : ℝ) ≤ (-38192056326079339087/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_554 (by norm_num)
  have hUr : potential (40516462999739/64000000000000 : ℝ) ≤ (-38192056326079339087/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_555 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_554
  linarith only [hU, hF]

theorem cell_bound_555 : cellBound ((40516462999739/64000000000000 : ℚ) : ℝ) ((10146313901169/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (40516462999739/64000000000000 : ℝ) ≤ (-38082379389914732241/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_555 (by norm_num)
  have hUr : potential (10146313901169/16000000000000 : ℝ) ≤ (-38082379389914732241/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_556 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_555
  linarith only [hU, hF]

theorem cell_bound_556 : cellBound ((10146313901169/16000000000000 : ℚ) : ℝ) ((40654048209613/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (10146313901169/16000000000000 : ℝ) ≤ (-4746656031605889791/6250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_556 (by norm_num)
  have hUr : potential (40654048209613/64000000000000 : ℝ) ≤ (-4746656031605889791/6250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_557 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_556
  linarith only [hU, hF]

theorem cell_bound_557 : cellBound ((40654048209613/64000000000000 : ℚ) : ℝ) ((814456816291/1280000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (40654048209613/64000000000000 : ℝ) ≤ (-75729298926496797361/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_557 (by norm_num)
  have hUr : potential (814456816291/1280000000000 : ℝ) ≤ (-75729298926496797361/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_558 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_557
  linarith only [hU, hF]

theorem cell_bound_558 : cellBound ((814456816291/1280000000000 : ℚ) : ℝ) ((40791633419487/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (814456816291/1280000000000 : ℝ) ≤ (-15102627980159387251/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_558 (by norm_num)
  have hUr : potential (40791633419487/64000000000000 : ℝ) ≤ (-15102627980159387251/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_559 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_558
  linarith only [hU, hF]

theorem cell_bound_559 : cellBound ((40791633419487/64000000000000 : ℚ) : ℝ) ((5107553253053/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (40791633419487/64000000000000 : ℝ) ≤ (-75297995552895125371/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_559 (by norm_num)
  have hUr : potential (5107553253053/8000000000000 : ℝ) ≤ (-75297995552895125371/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_560 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_559
  linarith only [hU, hF]

#print axioms cell_bound_559
end Zeta5AppendixNumerics
