import CertificateTactics
import AppendixCellBase
import AppendixField.Batch035
import AppendixField.Batch036
import AppendixField.Batch037
import AppendixPotential.Batch036
import AppendixPotential.Batch037
import AppendixPotential.Batch038
/-! Cell bounds assembled from the named endpoint and field certificates. See `NUMERICAL_CERTIFICATES.md`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Zeta5AppendixNumerics

theorem cell_bound_288 : cellBound ((975023636351/4000000000000 : ℚ) : ℝ) ((3934214662491/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_288 potential_upper_289 field_lower_288

theorem cell_bound_289 : cellBound ((3934214662491/16000000000000 : ℚ) : ℝ) ((1984167389789/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_289 potential_upper_290 field_lower_289

theorem cell_bound_290 : cellBound ((1984167389789/8000000000000 : ℚ) : ℝ) ((504571876719/2000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_290 potential_upper_291 field_lower_290

theorem cell_bound_291 : cellBound ((504571876719/2000000000000 : ℚ) : ℝ) ((2052407623963/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_291 potential_upper_292 field_lower_291

theorem cell_bound_292 : cellBound ((2052407623963/8000000000000 : ℚ) : ℝ) ((41730554821/160000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_292 potential_upper_293 field_lower_292

theorem cell_bound_293 : cellBound ((41730554821/160000000000 : ℚ) : ℝ) ((269345996903/1000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_293 potential_upper_294 field_lower_293

theorem cell_bound_294 : cellBound ((269345996903/1000000000000 : ℚ) : ℝ) ((8696815458149/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_294 potential_upper_295 field_lower_294

theorem cell_bound_295 : cellBound ((8696815458149/32000000000000 : ℚ) : ℝ) ((4387279507701/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_295 potential_upper_296 field_lower_295

theorem cell_bound_296 : cellBound ((4387279507701/16000000000000 : ℚ) : ℝ) ((1770460514531/6400000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_296 potential_upper_297 field_lower_296

theorem cell_bound_297 : cellBound ((1770460514531/6400000000000 : ℚ) : ℝ) ((17782348702563/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_297 potential_upper_298 field_lower_297

theorem cell_bound_298 : cellBound ((17782348702563/64000000000000 : ℚ) : ℝ) ((2232511532477/8000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_298 potential_upper_299 field_lower_298

theorem cell_bound_299 : cellBound ((2232511532477/8000000000000 : ℚ) : ℝ) ((17937835817069/64000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_299 potential_upper_300 field_lower_299

theorem cell_bound_300 : cellBound ((17937835817069/64000000000000 : ℚ) : ℝ) ((9007789687161/32000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_300 potential_upper_301 field_lower_300

theorem cell_bound_301 : cellBound ((9007789687161/32000000000000 : ℚ) : ℝ) ((723732917263/2560000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_301 potential_upper_302 field_lower_301

theorem cell_bound_302 : cellBound ((723732917263/2560000000000 : ℚ) : ℝ) ((4542766622207/16000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_302 potential_upper_303 field_lower_302

theorem cell_bound_303 : cellBound ((4542766622207/16000000000000 : ℚ) : ℝ) ((36419876534909/128000000000000 : ℚ) : ℝ) < -6645002/1000000 := by
  cell_certificate potential_upper_303 potential_upper_304 field_lower_303

end Zeta5AppendixNumerics
