import FullPullbackCertificate
import LocalDiskValue
import InnerDistributionBound

namespace Zeta5Local
open Polynomial
variable {p : ℕ} [Fact p.Prime]

/-- The full signed-pole local presentation is exactly the disk term in
the distribution formula for the source matrix. -/
theorem actual_full_disk_value (N h : ℕ) (A : ℚ[X]) (x : ℚ_[p]) (c : ℕ) :
    tauPolynomial (((actualPullbackPolynomial N h A).map (Rat.castHom ℚ_[p])).comp
      (C (p:ℚ_[p])*X+C (c:ℚ_[p]))) +
      ∑ ib : Fin (N+h) × Bool, ((fullPullbackResidue N h A ib.1 : ℚ_[p])/(p:ℚ_[p]))*
        residuePoleValue ((p:ℚ_[p])^5*x+distributionConstant p)
          (actualSignedIntegerRoot 0 ib-c) =
      Zeta5InnerDistributionBound.diskValue N h A x c := by
  rw [fullPullback_pole_value_sum]
  have ht := tauPolynomial_affine_rat (p := p) (actualPullbackPolynomial N h A) (c:ℚ) (p:ℚ)
  simp only [Rat.cast_natCast] at ht
  rw [add_comm (C (p:ℚ_[p])*X), ht]
  rfl

#print axioms actual_full_disk_value
end Zeta5Local
