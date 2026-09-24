import Main

/-! Proved counterparts of the independent statements in `Challenge.lean`. -/
namespace Zeta5Palomar

theorem irrational_zeta_five : Irrational ((riemannZeta (5 : ℂ)).re) :=
  Zeta5.irrational_zeta_five

theorem irrational_reciprocal_fifth_power_sum :
    Irrational (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 5) :=
  Zeta5.irrational_reciprocal_fifth_power_sum

#print axioms irrational_zeta_five
#print axioms irrational_reciprocal_fifth_power_sum

end Zeta5Palomar
