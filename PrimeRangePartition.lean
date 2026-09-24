import PrimeSums
import NormalizationLog

noncomputable section
open scoped BigOperators
namespace Zeta5PrimeSums

lemma prime_sum_Ioc_eq_difference (a b : ℕ) (hab : a≤b) (f : ℕ→ℝ) :
    (∑p∈Finset.Ioc a b with p.Prime, f p)=
      (∑p∈Finset.Icc 0 b with p.Prime,f p)-(∑p∈Finset.Icc 0 a with p.Prime,f p) := by
  simpa only [Finset.sum_filter] using sum_Ioc_eq_difference a b hab (fun p=>if p.Prime then f p else 0)

lemma prime_allocation_sum_le (a : ℕ) (x : ℝ) :
    (∑p∈Finset.Ioc a ⌊x⌋₊ with p.Prime,(p:ℝ)/2*Real.log p)≤weightedTheta x/2 := by
  have he : weightedTheta x/2=∑p∈Finset.Icc 0 ⌊x⌋₊ with p.Prime,(p:ℝ)/2*Real.log p := by
    unfold weightedTheta
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [he]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hp,hpp⟩:=Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _,(Finset.mem_Ioc.mp hp).2⟩,hpp⟩
  · intro p hp hnot
    have hl : 0≤Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_le)
    positivity

end Zeta5PrimeSums
namespace Zeta5Parameters

def tailCorrectedLocalSum (n M : ℕ) : ℝ :=
  ∑p∈Finset.Ioc ⌊(K n:ℝ)/(M:ℝ)⌋₊ ⌊(K n:ℝ)/20⌋₊ with p.Prime,
    (-(localExponent n M p:ℝ)-(p:ℝ)/2)*Real.log p

lemma normalizer_prime_sum (n : ℕ) (M : ℕ) :
    Real.log (normalizer n M:ℝ)=
      ∑p∈Finset.Icc 0 ⌊(37/20:ℝ)*(K n:ℝ)⌋₊ with p.Prime,
        -(localExponent n M p:ℝ)*Real.log p := by
  rw [log_normalizer]
  have he : (37/20:ℝ)*(K n:ℝ)=(2*h n:ℕ) := by
    unfold K h
    push_cast
    ring
  rw [he,Nat.floor_natCast]
  have hs : Finset.Icc 0 (2*h n)=Finset.range (2*h n+1) := by
    ext p
    simp only [Finset.mem_Icc,Finset.mem_range]
    omega
  rw [hs]
  simp only [normalizationPrimes,neg_mul,Finset.sum_neg_distrib]

end Zeta5Parameters
