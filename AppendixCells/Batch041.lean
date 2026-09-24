import CertificateTactics
import AppendixCellBase
import AppendixField.Batch081
import AppendixField.Batch082
import AppendixField.Batch083
import AppendixPotential.Batch082
import AppendixPotential.Batch083
import AppendixPotential.Batch084
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_656 : cellBound ((194899235804257/256000000000000 : ℚ) : ℝ) ((78210366862569/102400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_656 potential_upper_657 field_lower_656

theorem cell_bound_657 : cellBound ((78210366862569/102400000000000 : ℚ) : ℝ) ((49038149627147/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_657 potential_upper_658 field_lower_657

theorem cell_bound_658 : cellBound ((49038149627147/64000000000000 : ℚ) : ℝ) ((393558559721507/512000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_658 potential_upper_659 field_lower_658

theorem cell_bound_659 : cellBound ((393558559721507/512000000000000 : ℚ) : ℝ) ((197405961212919/256000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_659 potential_upper_660 field_lower_659

theorem cell_bound_660 : cellBound ((197405961212919/256000000000000 : ℚ) : ℝ) ((396065285130169/512000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_660 potential_upper_661 field_lower_660

theorem cell_bound_661 : cellBound ((396065285130169/512000000000000 : ℚ) : ℝ) ((794637295669/1024000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_661 potential_upper_662 field_lower_661

theorem cell_bound_662 : cellBound ((794637295669/1024000000000 : ℚ) : ℝ) ((398572010538831/512000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_662 potential_upper_663 field_lower_662

theorem cell_bound_663 : cellBound ((398572010538831/512000000000000 : ℚ) : ℝ) ((199912686621581/256000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_663 potential_upper_664 field_lower_663

theorem cell_bound_664 : cellBound ((199912686621581/256000000000000 : ℚ) : ℝ) ((25145756165739/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_664 potential_upper_665 field_lower_664

theorem cell_bound_665 : cellBound ((25145756165739/32000000000000 : ℚ) : ℝ) ((202419412030243/256000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_665 potential_upper_666 field_lower_665

theorem cell_bound_666 : cellBound ((202419412030243/256000000000000 : ℚ) : ℝ) ((101836387367287/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_666 potential_upper_667 field_lower_666

theorem cell_bound_667 : cellBound ((101836387367287/128000000000000 : ℚ) : ℝ) ((40985227487781/51200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_667 potential_upper_668 field_lower_667

theorem cell_bound_668 : cellBound ((40985227487781/51200000000000 : ℚ) : ℝ) ((51544875035809/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_668 potential_upper_669 field_lower_668

theorem cell_bound_669 : cellBound ((51544875035809/64000000000000 : ℚ) : ℝ) ((104343112775949/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_669 potential_upper_670 field_lower_669

theorem cell_bound_670 : cellBound ((104343112775949/128000000000000 : ℚ) : ℝ) ((2639911887007/3200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_670 potential_upper_671 field_lower_670

theorem cell_bound_671 : cellBound ((2639911887007/3200000000000 : ℚ) : ℝ) ((106849838184611/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_671 potential_upper_672 field_lower_671

end Zeta5AppendixNumerics
