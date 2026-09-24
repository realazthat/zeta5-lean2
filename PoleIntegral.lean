import PositiveIntegrals
import GeometricMoments
import PoleKernel

noncomputable section
open scoped BigOperators
open MeasureTheory Set Polynomial

namespace Zeta5Construction

/-- The positive summands in the coth partial-fraction kernel. -/
def boseTerm (a : ℝ) (l : ℕ) (u : ℝ) : ℝ :=
  u^5 * Real.exp (-(a*u)) / (u^2+(2*Real.pi*(l+1 : ℕ))^2)

lemma boseTerm_nonneg {a u : ℝ} (l : ℕ) (hu : 0 ≤ u) : 0 ≤ boseTerm a l u := by
  unfold boseTerm
  positivity

lemma boseTerm_bound {a u : ℝ} (l : ℕ) (hu : 0 ≤ u) :
    boseTerm a l u ≤ (1/(2*Real.pi*(l+1 : ℕ))^2) * (u^5*Real.exp (-(a*u))) := by
  have hc : (0 : ℝ) < 2*Real.pi*(l+1 : ℕ) := by positivity
  unfold boseTerm
  rw [mul_comm (1 / _) _, ← div_eq_mul_one_div]
  exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hc)
    (by nlinarith [sq_nonneg u])

lemma boseTerm_integrable {a : ℝ} (ha : 0 < a) (l : ℕ) :
    IntegrableOn (boseTerm a l) (Ioi 0) := by
  apply ((power_exp_integrable 5 ha).const_mul
    ((1/(2*Real.pi*(l+1 : ℕ))^2))).mono'
  · have hm : Measurable (boseTerm a l) := by unfold boseTerm; fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_of_nonneg (boseTerm_nonneg l hu.le)]
    exact boseTerm_bound l hu.le

lemma boseTerm_integral_bound {a : ℝ} (ha : 0 < a) (l : ℕ) :
    (∫ u : ℝ in Ioi 0, ‖boseTerm a l u‖) ≤
      (120 / ((2*Real.pi)^2*a^6)) * (1/(l+1 : ℝ)^2) := by
  have hnorm : (∫ u : ℝ in Ioi 0, ‖boseTerm a l u‖) =
      ∫ u : ℝ in Ioi 0, boseTerm a l u := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    exact Real.norm_of_nonneg (boseTerm_nonneg l hu.le)
  rw [hnorm]
  calc
    _ ≤ ∫ u : ℝ in Ioi 0,
        (1/(2*Real.pi*(l+1 : ℕ))^2) * (u^5*Real.exp (-(a*u))) := by
      apply integral_mono_ae (boseTerm_integrable ha l)
        ((power_exp_integrable 5 ha).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact boseTerm_bound l hu.le
    _ = _ := by
      rw [integral_const_mul, power_exp_integral 5 ha]
      norm_num
      push_cast
      field_simp <;> ring

lemma boseTerm_norm_summable {a : ℝ} (ha : 0 < a) :
    Summable (fun l : ℕ => ∫ u : ℝ in Ioi 0, ‖boseTerm a l u‖) := by
  apply Summable.of_nonneg_of_le
    (fun l => integral_nonneg (fun u => norm_nonneg _))
    (boseTerm_integral_bound ha)
  apply Summable.mul_left
  simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hasSum_zeta_two.summable

/-- The original weight divided by y²+a² is integrable. -/
lemma poleWeight_integrable {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun y : ℝ => integralWeight y/(y^2+a^2)) (Ioi 0) := by
  change Integrable (fun y : ℝ => integralWeight y/(y^2+a^2)) (volume.restrict (Ioi 0))
  apply (integralWeight_integrable.const_mul (a^2)⁻¹).mono' 
  · have hm : Measurable (fun y : ℝ => (y^2+a^2)⁻¹) := by fun_prop
    have he : (fun y : ℝ => integralWeight y/(y^2+a^2)) =
        integralWeight * (fun y : ℝ => (y^2+a^2)⁻¹) := by
      funext y
      exact div_eq_mul_inv _ _
    rw [he]
    exact integralWeight_integrable.aestronglyMeasurable.mul hm.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hw : 0 ≤ integralWeight y := (integralWeight_pos hy).le
    rw [Real.norm_of_nonneg (div_nonneg hw (by positivity)), ← div_eq_inv_mul]
    exact div_le_div_of_nonneg_left hw (sq_pos_of_pos ha) (by nlinarith [sq_nonneg y])

/-- The lth original positive moment summand with the simple pole inserted. -/
def poleTerm (a : ℝ) (l : ℕ) (y : ℝ) : ℝ := momentTerm 0 (l+1) y / (y^2+a^2)

lemma poleTerm_integrable {a : ℝ} (ha : 0 < a) (l : ℕ) :
    IntegrableOn (poleTerm a l) (Ioi 0) := by
  apply ((momentTerm_integrable 0 (l+1)).const_mul (a^2)⁻¹).mono'
  · have hm : Measurable (poleTerm a l) := by unfold poleTerm momentTerm; fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hm := momentTerm_nonneg 0 (l+1) hy.le
    rw [show poleTerm a l y = momentTerm 0 (l+1) y / (y^2+a^2) from rfl,
      Real.norm_of_nonneg (div_nonneg hm (by positivity)), ← div_eq_inv_mul]
    exact div_le_div_of_nonneg_left hm (sq_pos_of_pos ha) (by nlinarith [sq_nonneg y])

lemma poleTerm_scaling {a : ℝ} (ha : 0 < a) (l : ℕ) (y : ℝ) :
    poleTerm a l y =
      (a^4/12*(2*Real.pi*(l+1 : ℕ)/a)) * boseTerm a l ((2*Real.pi*(l+1 : ℕ)/a)*y) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hc : (2*Real.pi*(l+1 : ℕ)) ≠ 0 := by positivity
  have he : a*((2*Real.pi*(l+1 : ℕ)/a)*y) = (2*Real.pi*(l+1 : ℕ))*y := by
    field_simp
  unfold poleTerm momentTerm boseTerm
  simp only [mul_zero, zero_add]
  rw [he]
  push_cast
  field_simp <;> ring

/-- The exact positive change of variables connecting the paper's weight
to the coth kernel. -/
theorem poleTerm_integral_eq_boseTerm {a : ℝ} (ha : 0 < a) (l : ℕ) :
    (∫ y : ℝ in Ioi 0, poleTerm a l y) =
      a^4/12 * (∫ u : ℝ in Ioi 0, boseTerm a l u) := by
  simp_rw [poleTerm_scaling ha l]
  rw [integral_const_mul, integral_comp_mul_left_Ioi _ _ (by positivity)]
  simp only [mul_zero, smul_eq_mul]
  field_simp <;> ring

lemma poleTerm_nonneg {a y : ℝ} (l : ℕ) (hy : 0 ≤ y) : 0 ≤ poleTerm a l y := by
  unfold poleTerm
  exact div_nonneg (momentTerm_nonneg 0 (l+1) hy) (by positivity)

lemma poleTerm_norm_summable {a : ℝ} (ha : 0 < a) :
    Summable (fun l : ℕ => ∫ y : ℝ in Ioi 0, ‖poleTerm a l y‖) := by
  have he (l : ℕ) : (∫ y : ℝ in Ioi 0, ‖poleTerm a l y‖) =
      a^4/12 * (∫ u : ℝ in Ioi 0, ‖boseTerm a l u‖) := by
    have h1 : (∫ y : ℝ in Ioi 0, ‖poleTerm a l y‖) =
        ∫ y : ℝ in Ioi 0, poleTerm a l y := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      exact Real.norm_of_nonneg (poleTerm_nonneg l hy.le)
    have h2 : (∫ u : ℝ in Ioi 0, ‖boseTerm a l u‖) =
        ∫ u : ℝ in Ioi 0, boseTerm a l u := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      exact Real.norm_of_nonneg (boseTerm_nonneg l hu.le)
    rw [h1, h2, poleTerm_integral_eq_boseTerm ha]
  simp_rw [he]
  exact (boseTerm_norm_summable ha).mul_left _

lemma momentTerm_zero_summable {y : ℝ} (hy : 0 < y) :
    Summable (fun l : ℕ => momentTerm 0 l y) := by
  have hs := (integralWeight_summable hy).mul_left ((2*Real.pi)^4*y^5/12)
  apply hs.congr
  intro l
  unfold momentTerm
  simp only [mul_zero, zero_add]
  have he : -((2*Real.pi*l)*y) = -(2*Real.pi*y)*l := by ring
  rw [he]
  ring

lemma poleWeight_eq_tsum {a y : ℝ} (hy : 0 < y) :
    integralWeight y/(y^2+a^2) = ∑' l : ℕ, poleTerm a l y := by
  unfold poleTerm
  rw [tsum_div_const]
  have hh := (momentTerm_zero_summable hy).tsum_eq_zero_add
  have hz : momentTerm 0 0 y = 0 := by simp [momentTerm]
  rw [hz, zero_add] at hh
  rw [← hh, ← evenPowerWeight_eq_tsum]
  simp

/-- The full exact transformation between the paper's pole integral and
the positive coth-kernel integral, including both justified interchanges. -/
theorem poleIntegral_eq_boseIntegral {a : ℝ} (ha : 0 < a) :
    (∫ y : ℝ in Ioi 0, integralWeight y/(y^2+a^2)) =
      a^4/12 * (∫ u : ℝ in Ioi 0, ∑' l : ℕ, boseTerm a l u) := by
  calc
    _ = ∫ y : ℝ in Ioi 0, ∑' l : ℕ, poleTerm a l y := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      exact poleWeight_eq_tsum hy
    _ = ∑' l : ℕ, ∫ y : ℝ in Ioi 0, poleTerm a l y :=
      (integral_tsum_of_summable_integral_norm (poleTerm_integrable ha)
        (poleTerm_norm_summable ha)).symm
    _ = a^4/12 * ∑' l : ℕ, ∫ u : ℝ in Ioi 0, boseTerm a l u := by
      simp_rw [poleTerm_integral_eq_boseTerm ha, tsum_mul_left]
    _ = _ := by
      rw [integral_tsum_of_summable_integral_norm (boseTerm_integrable ha)
        (boseTerm_norm_summable ha)]

/-- The elementary coth partial-fraction formula is the only input needed
for the remaining identity; it is proved separately using Mittag-Leffler. -/
def BoseKernelIdentity : Prop :=
  ∀ u : ℝ, 0 < u →
    1/(1-Real.exp (-u)) = 1/u+1/2 +
      2*u*(∑' l : ℕ, 1/(u^2+(2*Real.pi*(l+1 : ℕ))^2))

lemma boseSum_eq_kernelDifference (hkernel : BoseKernelIdentity) (j : ℕ) {u : ℝ}
    (hu : 0 < u) :
    2*(∑' l : ℕ, boseTerm (j : ℝ) l u) =
      boseIntegrand j u - u^3*Real.exp (-(j*u)) -
        (1/2)*(u^4*Real.exp (-(j*u))) := by
  have he : boseIntegrand j u =
      u^4*Real.exp (-(j*u))*(1/u+1/2+
        2*u*(∑' l : ℕ, 1/(u^2+(2*Real.pi*(l+1 : ℕ))^2))) := by
    unfold boseIntegrand
    rw [div_eq_mul_one_div, hkernel u hu]
  have hs : (∑' l : ℕ, boseTerm (j : ℝ) l u) =
      u^5*Real.exp (-(j*u))*(∑' l : ℕ, 1/(u^2+(2*Real.pi*(l+1 : ℕ))^2)) := by
    simp only [boseTerm, div_eq_mul_inv, one_div, tsum_mul_left, one_mul]
  rw [he, hs]
  have hu0 := ne_of_gt hu
  field_simp <;> ring

/-- Integrability of the entire coth kernel follows from the proved
geometric integrand identity and elementary Gamma integrability. -/
lemma boseSum_integrable (hkernel : BoseKernelIdentity) (j : ℕ) (hj : 0 < j) :
    IntegrableOn (fun u : ℝ => ∑' l : ℕ, boseTerm (j : ℝ) l u) (Ioi 0) := by
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have hi := ((boseIntegrand_integrable j hj).sub (power_exp_integrable 3 hj')).sub
    ((power_exp_integrable 4 hj').const_mul (1/2))
  apply (hi.const_mul (1/2)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hh := boseSum_eq_kernelDifference hkernel j hu
  dsimp
  linarith

/-- Proposition 2.2 for simple poles, assuming only the independently
proved coth partial-fraction kernel. All integral and series steps are proved. -/
theorem poleIntegral_eq_fifthPowerTail (hkernel : BoseKernelIdentity)
    (j : ℕ) (hj : 0 < j) :
    (∫ y : ℝ in Ioi 0, integralWeight y/(y^2+(j : ℝ)^2)) =
      (j : ℝ)^4*(∑' n : ℕ, 1/(j+n : ℝ)^5) - 1/4 - 1/(2*(j : ℝ)) := by
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have hi : 2*(∫ u : ℝ in Ioi 0, ∑' l : ℕ, boseTerm (j : ℝ) l u) =
      24*(∑' n : ℕ, 1/(j+n : ℝ)^5) - 6/(j : ℝ)^4 - 12/(j : ℝ)^5 := by
    rw [← integral_const_mul]
    calc
      _ = ∫ u : ℝ in Ioi 0,
          boseIntegrand j u-u^3*Real.exp (-(j*u))-(1/2)*(u^4*Real.exp (-(j*u))) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u hu
        exact boseSum_eq_kernelDifference hkernel j hu
      _ = _ := by
        have h1 := boseIntegrand_integrable j hj
        have h2 := power_exp_integrable 3 hj'
        have h3 := power_exp_integrable 4 hj'
        have e1 := integral_sub h1 h2
        have e2 := integral_sub (h1.sub h2) (h3.const_mul (1/2))
        simp only [Pi.sub_apply] at e1 e2
        rw [e2, e1, integral_const_mul, boseIntegral_eq_fifthPowerTail j hj,
          power_exp_integral 3 hj', power_exp_integral 4 hj']
        norm_num
        ring
  rw [poleIntegral_eq_boseIntegral hj']
  calc
    _ = (j : ℝ)^4/24 * (2*(∫ u : ℝ in Ioi 0, ∑' l : ℕ, boseTerm (j : ℝ) l u)) := by ring
    _ = _ := by
      rw [hi]
      have hj0 := ne_of_gt hj'
      field_simp <;> ring

/-- The exact simple-pole value (2.3) in ordinary reciprocal-series form. -/
theorem poleIntegral_eq_paper_value (hkernel : BoseKernelIdentity)
    (j : ℕ) (hj : 0 < j) :
    (∫ y : ℝ in Ioi 0, integralWeight y/(y^2+(j : ℝ)^2)) =
      (j : ℝ)^4*((∑' n : ℕ, 1/(n : ℝ)^5) - (harmonic5 j : ℝ)) -
        1/4 + 1/(2*(j : ℝ)) := by
  rw [poleIntegral_eq_fifthPowerTail hkernel j hj, fifthPowerTail_eq_series_sub_harmonic]
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hj
  field_simp <;> ring

/-- Proposition 2.2 for each basic simple pole, expressed with the exact
affine polynomial defining the rational functional in Construction.lean. -/
theorem poleFunctional_eq_integral (hkernel : BoseKernelIdentity)
    (j : ℕ) (hj : 0 < j) :
    (poleFunctional j).eval₂ (Rat.castHom ℝ) (∑' n : ℕ, 1/(n : ℝ)^5) =
      ∫ y : ℝ in Ioi 0, integralWeight y/(y^2+(j : ℝ)^2) := by
  rw [poleIntegral_eq_paper_value hkernel j hj]
  simp only [poleFunctional, eval₂_add, eval₂_sub, eval₂_mul, eval₂_C, eval₂_X]
  simp only [Rat.coe_castHom, Rat.cast_pow, Rat.cast_natCast, Rat.cast_div,
    Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat]

/-- The kernel input is discharged by the proved cotangent expansion. -/
theorem boseKernelIdentity : BoseKernelIdentity := by
  intro u hu
  simpa only [Nat.cast_add, Nat.cast_one] using Zeta5Kernel.bose_kernel u hu

/-- Unconditional Proposition 2.2 for every basic simple pole. Together
with polynomialFunctional_eq_integral this covers the generators of the
paper's rational-functional domain. -/
theorem paper_poleFunctional_eq_integral (j : ℕ) (hj : 0 < j) :
    (poleFunctional j).eval₂ (Rat.castHom ℝ) (∑' n : ℕ, 1/(n : ℝ)^5) =
      ∫ y : ℝ in Ioi 0, integralWeight y/(y^2+(j : ℝ)^2) :=
  poleFunctional_eq_integral boseKernelIdentity j hj

theorem paper_poleIntegral_eq_value (j : ℕ) (hj : 0 < j) :
    (∫ y : ℝ in Ioi 0, integralWeight y/(y^2+(j : ℝ)^2)) =
      (j : ℝ)^4*((∑' n : ℕ, 1/(n : ℝ)^5) - (harmonic5 j : ℝ)) -
        1/4 + 1/(2*(j : ℝ)) :=
  poleIntegral_eq_paper_value boseKernelIdentity j hj

#print axioms paper_poleFunctional_eq_integral

end Zeta5Construction
