import CertificateTactics
import AppendixCellBase
import AppendixField.Batch071
import AppendixField.Batch072
import AppendixField.Batch073
import AppendixPotential.Batch072
import AppendixPotential.Batch073
import AppendixPotential.Batch074
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_576 : cellBound ((43082559672831/64000000000000 : ℚ) : ℝ) ((2156723943323/3200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_576 potential_upper_577 field_lower_576

theorem cell_bound_577 : cellBound ((2156723943323/3200000000000 : ℚ) : ℝ) ((43186398060089/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_577 potential_upper_578 field_lower_577

theorem cell_bound_578 : cellBound ((43186398060089/64000000000000 : ℚ) : ℝ) ((21619158626859/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_578 potential_upper_579 field_lower_578

theorem cell_bound_579 : cellBound ((21619158626859/32000000000000 : ℚ) : ℝ) ((43290236447347/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_579 potential_upper_580 field_lower_579

theorem cell_bound_580 : cellBound ((43290236447347/64000000000000 : ℚ) : ℝ) ((2708884727561/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_580 potential_upper_581 field_lower_580

theorem cell_bound_581 : cellBound ((2708884727561/4000000000000 : ℚ) : ℝ) ((8678814966921/12800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_581 potential_upper_582 field_lower_581

theorem cell_bound_582 : cellBound ((8678814966921/12800000000000 : ℚ) : ℝ) ((21722997014117/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_582 potential_upper_583 field_lower_582

theorem cell_bound_583 : cellBound ((21722997014117/32000000000000 : ℚ) : ℝ) ((43497913221863/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_583 potential_upper_584 field_lower_583

theorem cell_bound_584 : cellBound ((43497913221863/64000000000000 : ℚ) : ℝ) ((10887458103873/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_584 potential_upper_585 field_lower_584

theorem cell_bound_585 : cellBound ((10887458103873/16000000000000 : ℚ) : ℝ) ((43601751609121/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_585 potential_upper_586 field_lower_585

theorem cell_bound_586 : cellBound ((43601751609121/64000000000000 : ℚ) : ℝ) ((174614683211/256000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_586 potential_upper_587 field_lower_586

theorem cell_bound_587 : cellBound ((174614683211/256000000000 : ℚ) : ℝ) ((43705589996379/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_587 potential_upper_588 field_lower_587

theorem cell_bound_588 : cellBound ((43705589996379/64000000000000 : ℚ) : ℝ) ((5469688648751/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_588 potential_upper_589 field_lower_588

theorem cell_bound_589 : cellBound ((5469688648751/8000000000000 : ℚ) : ℝ) ((43809428383637/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_589 potential_upper_590 field_lower_589

theorem cell_bound_590 : cellBound ((43809428383637/64000000000000 : ℚ) : ℝ) ((21930673788633/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_590 potential_upper_591 field_lower_590

theorem cell_bound_591 : cellBound ((21930673788633/32000000000000 : ℚ) : ℝ) ((8782653354179/12800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_591 potential_upper_592 field_lower_591

end Zeta5AppendixNumerics
