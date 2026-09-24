import NormalizationTail

noncomputable section
namespace Zeta5NormalizationTail

/-- Sum of the five proved prime-range contributions at the fixed cutoff. -/
theorem normalizationCoefficient_eq_prime_contributions :
    (normalizationCoefficient:ℝ)=
      6*(37/40)/100000-(6970198065777:ℝ)/125000000000000+
      322437603634266857629/7535670527041937280000+129101/96000+1/36 := by
  norm_num [normalizationCoefficient]

/-- A fixed positive error for each of the two eventual estimates still leaves
more than the ten units of quadratic decay used by the final argument. -/
theorem normalizationCoefficient_decay_margin :
    1600*((normalizationCoefficient:ℝ)+1/10000-
      2733991/2000000+1/10000) < -10 := by
  norm_num [normalizationCoefficient]

#print axioms normalizationCoefficient_eq_prime_contributions
#print axioms normalizationCoefficient_decay_margin
end Zeta5NormalizationTail
