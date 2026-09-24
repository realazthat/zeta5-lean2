import AppendixCellBase
import AppendixField.Batch002
import AppendixField.Batch003
import AppendixPotential.Batch002
import AppendixPotential.Batch003
import AppendixPotential.Batch004
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_16 : cellBound ((974522519/2000000000000 : ℚ) : ℝ) ((289098953/500000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (974522519/2000000000000 : ℝ) ≤ (-17486881793147106031/6250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_16 (by norm_num)
  have hUr : potential (289098953/500000000000 : ℝ) ≤ (-17486881793147106031/6250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_17 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_17
  linarith only [hU, hF]

theorem cell_bound_17 : cellBound ((289098953/500000000000 : ℚ) : ℝ) ((729961631/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (289098953/500000000000 : ℝ) ≤ (-28059849443529300999/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_17 (by norm_num)
  have hUr : potential (729961631/1000000000000 : ℝ) ≤ (-28059849443529300999/10000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_18 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_18
  linarith only [hU, hF]

theorem cell_bound_18 : cellBound ((729961631/1000000000000 : ℚ) : ℝ) ((1611686987/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (729961631/1000000000000 : ℝ) ≤ (-140581447185642949741/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_18 (by norm_num)
  have hUr : potential (1611686987/2000000000000 : ℝ) ≤ (-140581447185642949741/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_19 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_19
  linarith only [hU, hF]

theorem cell_bound_19 : cellBound ((1611686987/2000000000000 : ℚ) : ℝ) ((220431339/250000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1611686987/2000000000000 : ℝ) ≤ (-70378683981217781883/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_19 (by norm_num)
  have hUr : potential (220431339/250000000000 : ℝ) ≤ (-70378683981217781883/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_20 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_20
  linarith only [hU, hF]

theorem cell_bound_20 : cellBound ((220431339/250000000000 : ℚ) : ℝ) ((4047462733/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (220431339/250000000000 : ℝ) ≤ (-7054177339360633269/2500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_20 (by norm_num)
  have hUr : potential (4047462733/4000000000000 : ℝ) ≤ (-7054177339360633269/2500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_21 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_21
  linarith only [hU, hF]

theorem cell_bound_21 : cellBound ((4047462733/4000000000000 : ℚ) : ℝ) ((2284012021/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (4047462733/4000000000000 : ℝ) ≤ (-141224206850766759839/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_21 (by norm_num)
  have hUr : potential (2284012021/2000000000000 : ℝ) ≤ (-141224206850766759839/50000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_22 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_22
  linarith only [hU, hF]

theorem cell_bound_22 : cellBound ((2284012021/2000000000000 : ℚ) : ℝ) ((5088585351/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (2284012021/2000000000000 : ℝ) ≤ (-4418234974938359807/1562500000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_22 (by norm_num)
  have hUr : potential (5088585351/4000000000000 : ℝ) ≤ (-4418234974938359807/1562500000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_23 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_23
  linarith only [hU, hF]

theorem cell_bound_23 : cellBound ((5088585351/4000000000000 : ℚ) : ℝ) ((280457333/200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (5088585351/4000000000000 : ℝ) ≤ (-283153106376515590653/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_23 (by norm_num)
  have hUr : potential (280457333/200000000000 : ℝ) ≤ (-283153106376515590653/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_24 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_24
  linarith only [hU, hF]

theorem cell_bound_24 : cellBound ((280457333/200000000000 : ℚ) : ℝ) ((6519108259/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (280457333/200000000000 : ℝ) ≤ (-283915306742885061363/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_24 (by norm_num)
  have hUr : potential (6519108259/4000000000000 : ℝ) ≤ (-283915306742885061363/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_25 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_25
  linarith only [hU, hF]

theorem cell_bound_25 : cellBound ((6519108259/4000000000000 : ℚ) : ℝ) ((3714534929/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (6519108259/4000000000000 : ℝ) ≤ (-284174530765020906673/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_25 (by norm_num)
  have hUr : potential (3714534929/2000000000000 : ℝ) ≤ (-284174530765020906673/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_26 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_26
  linarith only [hU, hF]

theorem cell_bound_26 : cellBound ((3714534929/2000000000000 : ℚ) : ℝ) ((8339031457/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (3714534929/2000000000000 : ℝ) ≤ (-56895465003123685643/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_26 (by norm_num)
  have hUr : potential (8339031457/4000000000000 : ℝ) ≤ (-56895465003123685643/20000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_27 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_27
  linarith only [hU, hF]

theorem cell_bound_27 : cellBound ((8339031457/4000000000000 : ℚ) : ℝ) ((289031033/125000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (8339031457/4000000000000 : ℝ) ≤ (-284860802644252254241/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_27 (by norm_num)
  have hUr : potential (289031033/125000000000 : ℝ) ≤ (-284860802644252254241/100000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_28 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_28
  linarith only [hU, hF]

theorem cell_bound_28 : cellBound ((289031033/125000000000 : ℚ) : ℝ) ((124379927/40000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (289031033/125000000000 : ℝ) ≤ (-71426923015583375527/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_28 (by norm_num)
  have hUr : potential (124379927/40000000000 : ℝ) ≤ (-71426923015583375527/25000000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_29 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_29
  linarith only [hU, hF]

theorem cell_bound_29 : cellBound ((124379927/40000000000 : ℚ) : ℝ) ((7016246261/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (124379927/40000000000 : ℝ) ≤ (-17876172367332115123/6250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_29 (by norm_num)
  have hUr : potential (7016246261/2000000000000 : ℝ) ≤ (-17876172367332115123/6250000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_30 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_30
  linarith only [hU, hF]

theorem cell_bound_30 : cellBound ((7016246261/2000000000000 : ℚ) : ℝ) ((1953374043/500000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (7016246261/2000000000000 : ℝ) ≤ (-4472651958345561057/1562500000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_30 (by norm_num)
  have hUr : potential (1953374043/500000000000 : ℝ) ≤ (-4472651958345561057/1562500000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_31 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_31
  linarith only [hU, hF]

theorem cell_bound_31 : cellBound ((1953374043/500000000000 : ℚ) : ℝ) ((59205077/10000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  norm_num [cellBound, lowerField]
  have hUl : potential (1953374043/500000000000 : ℝ) ≤ (-35853885368775070121/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_31 (by norm_num)
  have hUr : potential (59205077/10000000000 : ℝ) ≤ (-35853885368775070121/12500000000000000000 : ℝ) := by
    norm_num only
    exact le_trans potential_upper_32 (by norm_num)
  have hU := max_le hUl hUr
  have hF := field_lower_32
  linarith only [hU, hF]

#print axioms cell_bound_31
end Zeta5AppendixNumerics
