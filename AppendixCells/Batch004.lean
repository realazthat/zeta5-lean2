import CertificateTactics
import AppendixCellBase
import AppendixField.Batch007
import AppendixField.Batch008
import AppendixField.Batch009
import AppendixPotential.Batch008
import AppendixPotential.Batch009
import AppendixPotential.Batch010
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_64 : cellBound ((944711264583/32000000000000 : ℚ) : ℝ) ((59550060209/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_64 potential_upper_65 field_lower_64

theorem cell_bound_65 : cellBound ((59550060209/2000000000000 : ℚ) : ℝ) ((192178132421/6400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_65 potential_upper_66 field_lower_65

theorem cell_bound_66 : cellBound ((192178132421/6400000000000 : ℚ) : ℝ) ((484490180433/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_66 potential_upper_67 field_lower_66

theorem cell_bound_67 : cellBound ((484490180433/16000000000000 : ℚ) : ℝ) ((977070059627/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_67 potential_upper_68 field_lower_67

theorem cell_bound_68 : cellBound ((977070059627/32000000000000 : ℚ) : ℝ) ((246289939597/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_68 potential_upper_69 field_lower_68

theorem cell_bound_69 : cellBound ((246289939597/8000000000000 : ℚ) : ℝ) ((100133915591/3200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_69 potential_upper_70 field_lower_69

theorem cell_bound_70 : cellBound ((100133915591/3200000000000 : ℚ) : ℝ) ((127189819179/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_70 potential_upper_71 field_lower_70

theorem cell_bound_71 : cellBound ((127189819179/4000000000000 : ℚ) : ℝ) ((516848975477/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_71 potential_upper_72 field_lower_71

theorem cell_bound_72 : cellBound ((516848975477/16000000000000 : ℚ) : ℝ) ((262469337119/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_72 potential_upper_73 field_lower_72

theorem cell_bound_73 : cellBound ((262469337119/8000000000000 : ℚ) : ℝ) ((6763975897/200000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_73 potential_upper_74 field_lower_73

theorem cell_bound_74 : cellBound ((6763975897/200000000000 : ℚ) : ℝ) ((278648734641/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_74 potential_upper_75 field_lower_74

theorem cell_bound_75 : cellBound ((278648734641/8000000000000 : ℚ) : ℝ) ((143369216701/4000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_75 potential_upper_76 field_lower_75

theorem cell_bound_76 : cellBound ((143369216701/4000000000000 : ℚ) : ℝ) ((75729457731/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_76 potential_upper_77 field_lower_76

theorem cell_bound_77 : cellBound ((75729457731/2000000000000 : ℚ) : ℝ) ((20954789123/500000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_77 potential_upper_78 field_lower_77

theorem cell_bound_78 : cellBound ((20954789123/500000000000 : ℚ) : ℝ) ((694494763253/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_78 potential_upper_79 field_lower_78

theorem cell_bound_79 : cellBound ((694494763253/16000000000000 : ℚ) : ℝ) ((1412931037823/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_79 potential_upper_80 field_lower_79

end Zeta5AppendixNumerics
