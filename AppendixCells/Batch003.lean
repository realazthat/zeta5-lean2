import CertificateTactics
import AppendixCellBase
import AppendixField.Batch005
import AppendixField.Batch006
import AppendixField.Batch007
import AppendixPotential.Batch006
import AppendixPotential.Batch007
import AppendixPotential.Batch008
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_48 : cellBound ((11896075201/640000000000 : ℚ) : ℝ) ((605192942919/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_48 potential_upper_49 field_lower_48

theorem cell_bound_49 : cellBound ((605192942919/32000000000000 : ℚ) : ℝ) ((153895531447/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_49 potential_upper_50 field_lower_49

theorem cell_bound_50 : cellBound ((153895531447/8000000000000 : ℚ) : ℝ) ((318180245763/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_50 potential_upper_51 field_lower_50

theorem cell_bound_51 : cellBound ((318180245763/16000000000000 : ℚ) : ℝ) ((41071178579/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_51 potential_upper_52 field_lower_51

theorem cell_bound_52 : cellBound ((41071178579/2000000000000 : ℚ) : ℝ) ((34934779437/1600000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_52 potential_upper_53 field_lower_52

theorem cell_bound_53 : cellBound ((34934779437/1600000000000 : ℚ) : ℝ) ((92531540027/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_53 potential_upper_54 field_lower_53

theorem cell_bound_54 : cellBound ((92531540027/4000000000000 : ℚ) : ℝ) ((6432545181/250000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_54 potential_upper_55 field_lower_54

theorem cell_bound_55 : cellBound ((6432545181/250000000000 : ℚ) : ℝ) ((213931144553/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_55 potential_upper_56 field_lower_55

theorem cell_bound_56 : cellBound ((213931144553/8000000000000 : ℚ) : ℝ) ((435951987867/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_56 potential_upper_57 field_lower_56

theorem cell_bound_57 : cellBound ((435951987867/16000000000000 : ℚ) : ℝ) ((111010421657/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_57 potential_upper_58 field_lower_57

theorem cell_bound_58 : cellBound ((111010421657/4000000000000 : ℚ) : ℝ) ((452131385389/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_58 potential_upper_59 field_lower_58

theorem cell_bound_59 : cellBound ((452131385389/16000000000000 : ℚ) : ℝ) ((912352469539/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_59 potential_upper_60 field_lower_59

theorem cell_bound_60 : cellBound ((912352469539/32000000000000 : ℚ) : ℝ) ((9204421683/320000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_60 potential_upper_61 field_lower_60

theorem cell_bound_61 : cellBound ((9204421683/320000000000 : ℚ) : ℝ) ((928531867061/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_61 potential_upper_62 field_lower_61

theorem cell_bound_62 : cellBound ((928531867061/32000000000000 : ℚ) : ℝ) ((468310782911/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_62 potential_upper_63 field_lower_62

theorem cell_bound_63 : cellBound ((468310782911/16000000000000 : ℚ) : ℝ) ((944711264583/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_63 potential_upper_64 field_lower_63

end Zeta5AppendixNumerics
