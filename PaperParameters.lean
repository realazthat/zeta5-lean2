import Construction
import Normalization
import Mathlib.Data.List.Sort

/-!
# The paper's exact prime normalization

Definitions (4.4)--(4.8), (4.14), and (5.1)--(5.2), with K=40n.
These definitions retain signed exponents. The local valuation estimates
are not asserted here. Admissibility excludes the small, degenerate values
at which the paper itself does not define the normalization.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace Zeta5Parameters

def K (n : ℕ) : ℕ := 40*n
def N (n : ℕ) : ℕ := 3*n
def h (n : ℕ) : ℕ := 37*n

def Admissible (n M : ℕ) : Prop := 40 ≤ M ∧ 200*M^2 ≤ K n

/-- The exact number of poles in an ordinary square class. -/
def poleCount (A p a : ℕ) : ℕ :=
  ((Finset.Icc 1 A).filter fun j => j % p = a % p ∨ j % p = (p-a) % p).card

def ordinaryClasses (p : ℕ) : List ℕ := (List.range ((p-1)/2)).map (·+1)
def zeroDimension (M : ℕ) : ℕ := 4*M+10

def allocationBudget (n M p : ℕ) : ℕ :=
  h n - zeroDimension M + 3*(N n - N n / p)

def baseAllocation (n M p : ℕ) : ℕ := allocationBudget n M p / ((p-1)/2)
def extraCount (n M p : ℕ) : ℕ := allocationBudget n M p % ((p-1)/2)

/-- Descending pole count; any order among ties is allowed in the paper. -/
def prioritizedClasses (n p : ℕ) : List ℕ :=
  (ordinaryClasses p).mergeSort fun a b => poleCount (K n) p b ≤ poleCount (K n) p a

def extra (n M p a : ℕ) : ℕ :=
  if a ∈ (prioritizedClasses n p).take (extraCount n M p) then 1 else 0

def classDimension (n M p a : ℕ) : ℕ :=
  baseAllocation n M p - 3*poleCount (N n) p a + extra n M p a

def twiceOrdinaryWeight (n p a i : ℕ) : ℤ :=
  2*(i : ℤ) + 6*(poleCount (N n) p a : ℤ) - (poleCount (K n) p a : ℤ) - 4

def twiceZeroWeight (n M p i : ℕ) : ℤ :=
  (ordinaryClasses p).foldl
    (fun w a => min w (2*((classDimension n M p a : ℤ) +
      3*(poleCount (N n) p a : ℤ)) - (poleCount (K n) p a : ℤ) - 4))
    (4*(i : ℤ) + 12*(N n / p : ℤ) - 2*(K n / p : ℤ) + 1)

/-- Twice the sum of all assigned half-integer weights, equation (4.8). -/
def innerExponent (n M p : ℕ) : ℤ :=
  (∑ i ∈ Finset.range (zeroDimension M), twiceZeroWeight n M p i) +
    ∑ a ∈ Finset.Icc 1 ((p-1)/2),
      ∑ i ∈ Finset.range (classDimension n M p a), twiceOrdinaryWeight n p a i

def correctionRank (n p : ℕ) : ℕ := K n + 4*N n + 2 - 2*p
def overlap (n p : ℕ) : ℕ := N n + K n % p + 1 - p
def removedExtraCount (n p : ℕ) : ℕ := min (N n) (K n % p) + overlap n p

/-- The outer exponent (4.14), extended by zero for p>K as in Section 5. -/
def outerExponent (n p : ℕ) : ℤ :=
  if K n < p then 0 else
  if K n < 2*p then
    -7*((K n : ℤ) - p) + 6*(removedExtraCount n p : ℤ) - 1 -
      (min (correctionRank n p) (p - 1 - N n + overlap n p) : ℕ)
  else
    -7*((K n : ℤ) - p) + 3 + 12*(N n : ℤ) +
      5*(removedExtraCount n p : ℤ) -
      (min (correctionRank n p) (p + overlap n p) : ℕ)

/-- A sufficient outer bound obtained by allowing the entire polynomial
correction rank to lower the determinant valuation. -/
def coarseOuterExponent (n p : ℕ) : ℤ :=
  if K n < p then 0 else
  if K n < 2*p then
    -7*((K n : ℤ) - p) + 6*(removedExtraCount n p : ℤ) - 1 - correctionRank n p
  else
    -7*((K n : ℤ) - p) + 3 + 12*(N n : ℤ) +
      5*(removedExtraCount n p : ℤ) - correctionRank n p

theorem coarseOuterExponent_le_outerExponent (n p : ℕ) :
    coarseOuterExponent n p ≤ outerExponent n p := by
  unfold coarseOuterExponent outerExponent
  split_ifs with hK htwo
  · exact le_rfl
  · have h := Nat.min_le_left (correctionRank n p) (p-1-N n+overlap n p)
    have hz : ((min (correctionRank n p) (p-1-N n+overlap n p):ℕ):ℤ) ≤ correctionRank n p := by exact_mod_cast h
    omega
  · have h := Nat.min_le_left (correctionRank n p) (p+overlap n p)
    have hz : ((min (correctionRank n p) (p+overlap n p):ℕ):ℤ) ≤ correctionRank n p := by exact_mod_cast h
    omega

/-- Signed local bound L_p(K,M), equation (5.1). -/
def localExponent (n M p : ℕ) : ℤ :=
  if p*M ≤ K n then
    -6*(h n : ℤ)*(Nat.log p (5*K n) : ℤ) -
      (h n : ℤ)*(padicValNat p 24 : ℤ)
  else
    padicValRat p (Zeta5Construction.normalizingScalar (N n) (h n)) +
      if 3*p ≤ K n then innerExponent n M p else coarseOuterExponent n p

def normalizationPrimes (n : ℕ) : Finset ℕ :=
  (Finset.range (2*h n+1)).filter Nat.Prime

lemma normalizationPrimes_prime (n p : ℕ) (hp : p ∈ normalizationPrimes n) : p.Prime :=
  (Finset.mem_filter.mp hp).2

/-- m_{40n,M}, equation (5.2). -/
def normalizer (n M : ℕ) : ℚ :=
  Zeta5Normalization.primeNormalizer (normalizationPrimes n) (localExponent n M)

theorem normalizer_pos (n M : ℕ) : 0 < normalizer n M :=
  Zeta5Normalization.primeNormalizer_pos _ _ (normalizationPrimes_prime n)

/-- The actual rational polynomial before its integer coefficients are proved. -/
def paperPolynomial (n M : ℕ) : ℚ[X] :=
  C (normalizer n M) * Zeta5Construction.normalizedDeterminant (N n) (h n)

/-- Degree 37n is unconditional, even before the arithmetic estimates. -/
theorem paperPolynomial_degree (n M : ℕ) : (paperPolynomial n M).natDegree = 37*n := by
  rw [paperPolynomial, Polynomial.natDegree_C_mul (ne_of_gt (normalizer_pos n M)),
    Zeta5Construction.normalizedDeterminant_degree]
  rfl

theorem admissible_zeroDimension_le {n M : ℕ} (ha : Admissible n M) :
    zeroDimension M ≤ h n := by
  obtain ⟨hM, hn⟩ := ha
  dsimp [zeroDimension, h, K] at *
  nlinarith [sq_nonneg (M : ℤ)]

/-- Proposition 5.1's final algebraic step applied to the actual polynomial.
The two hypotheses here are precisely the local estimates still to be proved. -/
theorem paperPolynomial_integer_of_local_bounds (n M : ℕ)
    (hlocal : ∀ p ∈ normalizationPrimes n, ∀ i : ℕ,
      (Zeta5Construction.normalizedDeterminant (N n) (h n)).coeff i ≠ 0 →
      localExponent n M p ≤ padicValRat p
        ((Zeta5Construction.normalizedDeterminant (N n) (h n)).coeff i))
    (houtside : ∀ p : ℕ, p.Prime → p ∉ normalizationPrimes n → ∀ i : ℕ,
      (Zeta5Construction.normalizedDeterminant (N n) (h n)).coeff i ≠ 0 →
      0 ≤ padicValRat p ((Zeta5Construction.normalizedDeterminant (N n) (h n)).coeff i)) :
    ∃ Q : ℤ[X], Q.map (Int.castRingHom ℚ) = paperPolynomial n M := by
  exact Zeta5Normalization.normalized_polynomial_is_integer _ _ _
    (normalizationPrimes_prime n) hlocal houtside

#print axioms paperPolynomial_degree
#print axioms paperPolynomial_integer_of_local_bounds

end Zeta5Parameters
