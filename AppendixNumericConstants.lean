import CertificateData
import AppendixNumericBase
import LogCertificates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem support_log_upper_0 : Real.log (1017189489/800000000000 : ℝ) ≤ (-666756829/100000000 : ℝ) := by
  convert Zeta5LogCertificates.log_le_of_check (1017189489/800000000000 : ℚ) (-666756829/100000000 : ℚ)
    log_roots%(1017189489/800000000000, 34) (by decide +kernel) using 1 <;> norm_num

theorem support_log_upper_1 : Real.log (13028749591/4000000000000 : ℝ) ≤ (-3579307/625000 : ℝ) := by
  convert Zeta5LogCertificates.log_le_of_check (13028749591/4000000000000 : ℚ) (-3579307/625000 : ℚ)
    log_roots%(13028749591/4000000000000, 34) (by decide +kernel) using 1 <;> norm_num

theorem support_log_upper_2 : Real.log (24327894059/4000000000000 : ℝ) ≤ (-510242603/100000000 : ℝ) := by
  convert Zeta5LogCertificates.log_le_of_check (24327894059/4000000000000 : ℚ) (-510242603/100000000 : ℚ)
    log_roots%(24327894059/4000000000000, 34) (by decide +kernel) using 1 <;> norm_num

theorem support_log_upper_3 : Real.log (4102785289/400000000000 : ℝ) ≤ (-91595969/20000000 : ℝ) := by
  convert Zeta5LogCertificates.log_le_of_check (4102785289/400000000000 : ℚ) (-91595969/20000000 : ℚ)
    log_roots%(4102785289/400000000000, 34) (by decide +kernel) using 1 <;> norm_num

theorem support_log_upper_4 : Real.log (65272891657/4000000000000 : ℝ) ≤ (-411547281/100000000 : ℝ) := by
  convert Zeta5LogCertificates.log_le_of_check (65272891657/4000000000000 : ℚ) (-411547281/100000000 : ℚ)
    log_roots%(65272891657/4000000000000, 34) (by decide +kernel) using 1 <;> norm_num

theorem support_log_upper_5 : Real.log (99084713271/4000000000000 : ℝ) ≤ (-73961489/20000000 : ℝ) := by
  convert Zeta5LogCertificates.log_le_of_check (99084713271/4000000000000 : ℚ) (-73961489/20000000 : ℚ)
    log_roots%(99084713271/4000000000000, 34) (by decide +kernel) using 1 <;> norm_num

theorem support_log_upper_6 : Real.log (144041816267/4000000000000 : ℝ) ≤ (-166197299/50000000 : ℝ) := by
  convert Zeta5LogCertificates.log_le_of_check (144041816267/4000000000000 : ℚ) (-166197299/50000000 : ℚ)
    log_roots%(144041816267/4000000000000, 34) (by decide +kernel) using 1 <;> norm_num

theorem support_log_upper_7 : Real.log (200893556541/4000000000000 : ℝ) ≤ (-299127443/100000000 : ℝ) := by
  convert Zeta5LogCertificates.log_le_of_check (200893556541/4000000000000 : ℚ) (-299127443/100000000 : ℚ)
    log_roots%(200893556541/4000000000000, 34) (by decide +kernel) using 1 <;> norm_num

theorem support_log_upper_8 : Real.log (269180899217/4000000000000 : ℝ) ≤ (-134933299/50000000 : ℝ) := by
  convert Zeta5LogCertificates.log_le_of_check (269180899217/4000000000000 : ℚ) (-134933299/50000000 : ℚ)
    log_roots%(269180899217/4000000000000, 34) (by decide +kernel) using 1 <;> norm_num

theorem support_log_upper_9 : Real.log (21684762939/250000000000 : ℝ) ≤ (-122242553/50000000 : ℝ) := by
  convert Zeta5LogCertificates.log_le_of_check (21684762939/250000000000 : ℚ) (-122242553/50000000 : ℚ)
    log_roots%(21684762939/250000000000, 34) (by decide +kernel) using 1 <;> norm_num

theorem support_log_upper_10 : Real.log (430695182301/4000000000000 : ℝ) ≤ (-111432451/50000000 : ℝ) := by
  convert Zeta5LogCertificates.log_le_of_check (430695182301/4000000000000 : ℚ) (-111432451/50000000 : ℚ)
    log_roots%(430695182301/4000000000000, 34) (by decide +kernel) using 1 <;> norm_num

theorem support_log_upper_11 : Real.log (128866386789/1000000000000 : ℝ) ≤ (-51224479/25000000 : ℝ) := by
  convert Zeta5LogCertificates.log_le_of_check (128866386789/1000000000000 : ℚ) (-51224479/25000000 : ℚ)
    log_roots%(128866386789/1000000000000, 34) (by decide +kernel) using 1 <;> norm_num

theorem support_log_upper_12 : Real.log (595362962907/4000000000000 : ℝ) ≤ (-95243919/50000000 : ℝ) := by
  convert Zeta5LogCertificates.log_le_of_check (595362962907/4000000000000 : ℚ) (-95243919/50000000 : ℚ)
    log_roots%(595362962907/4000000000000, 34) (by decide +kernel) using 1 <;> norm_num

theorem support_log_upper_13 : Real.log (166040678943/1000000000000 : ℝ) ≤ (-35910449/20000000 : ℝ) := by
  convert Zeta5LogCertificates.log_le_of_check (166040678943/1000000000000 : ℚ) (-35910449/20000000 : ℚ)
    log_roots%(166040678943/1000000000000, 34) (by decide +kernel) using 1 <;> norm_num

theorem support_log_upper_14 : Real.log (716086447547/4000000000000 : ℝ) ≤ (-172024873/100000000 : ℝ) := by
  convert Zeta5LogCertificates.log_le_of_check (716086447547/4000000000000 : ℚ) (-172024873/100000000 : ℚ)
    log_roots%(716086447547/4000000000000, 34) (by decide +kernel) using 1 <;> norm_num

theorem support_log_upper_15 : Real.log (746565554359/4000000000000 : ℝ) ≤ (-8392831/5000000 : ℝ) := by
  convert Zeta5LogCertificates.log_le_of_check (746565554359/4000000000000 : ℚ) (-8392831/5000000 : ℚ)
    log_roots%(746565554359/4000000000000, 34) (by decide +kernel) using 1 <;> norm_num

end Zeta5AppendixNumerics
