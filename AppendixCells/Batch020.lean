import CertificateTactics
import AppendixCellBase
import AppendixField.Batch039
import AppendixField.Batch040
import AppendixField.Batch041
import AppendixPotential.Batch040
import AppendixPotential.Batch041
import AppendixPotential.Batch042
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_320 : cellBound ((37663773450957/128000000000000 : ℚ) : ℝ) ((3774151700821/12800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_320 potential_upper_321 field_lower_320

theorem cell_bound_321 : cellBound ((3774151700821/12800000000000 : ℚ) : ℝ) ((37819260565463/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_321 potential_upper_322 field_lower_321

theorem cell_bound_322 : cellBound ((37819260565463/128000000000000 : ℚ) : ℝ) ((9474251030679/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_322 potential_upper_323 field_lower_322

theorem cell_bound_323 : cellBound ((9474251030679/32000000000000 : ℚ) : ℝ) ((37974747679969/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_323 potential_upper_324 field_lower_323

theorem cell_bound_324 : cellBound ((37974747679969/128000000000000 : ℚ) : ℝ) ((19026245618611/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_324 potential_upper_325 field_lower_324

theorem cell_bound_325 : cellBound ((19026245618611/64000000000000 : ℚ) : ℝ) ((1525209391779/5120000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_325 potential_upper_326 field_lower_325

theorem cell_bound_326 : cellBound ((1525209391779/5120000000000 : ℚ) : ℝ) ((2387998646983/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_326 potential_upper_327 field_lower_326

theorem cell_bound_327 : cellBound ((2387998646983/8000000000000 : ℚ) : ℝ) ((38285721908981/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_327 potential_upper_328 field_lower_327

theorem cell_bound_328 : cellBound ((38285721908981/128000000000000 : ℚ) : ℝ) ((19181732733117/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_328 potential_upper_329 field_lower_328

theorem cell_bound_329 : cellBound ((19181732733117/64000000000000 : ℚ) : ℝ) ((38441209023487/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_329 potential_upper_330 field_lower_329

theorem cell_bound_330 : cellBound ((38441209023487/128000000000000 : ℚ) : ℝ) ((1925947629037/6400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_330 potential_upper_331 field_lower_330

theorem cell_bound_331 : cellBound ((1925947629037/6400000000000 : ℚ) : ℝ) ((19337219847623/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_331 potential_upper_332 field_lower_331

theorem cell_bound_332 : cellBound ((19337219847623/64000000000000 : ℚ) : ℝ) ((4853740851219/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_332 potential_upper_333 field_lower_332

theorem cell_bound_333 : cellBound ((4853740851219/16000000000000 : ℚ) : ℝ) ((19492706962129/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_333 potential_upper_334 field_lower_333

theorem cell_bound_334 : cellBound ((19492706962129/64000000000000 : ℚ) : ℝ) ((9785225259691/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_334 potential_upper_335 field_lower_334

theorem cell_bound_335 : cellBound ((9785225259691/32000000000000 : ℚ) : ℝ) ((3929638815327/12800000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_335 potential_upper_336 field_lower_335

end Zeta5AppendixNumerics
