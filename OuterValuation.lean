import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-!
# The rank-sensitive perturbation bound in Section 4.2

This file formalizes Lemma 4.2 of Aabir Fauzan's "ζ(5) is irrational"
(Zenodo 22826419). It does not assume or prove the paper's moment estimates.
-/

namespace Zeta5Outer
open scoped BigOperators
open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The number of zero weights. -/
def zeroCount (a : ι → ℕ) : ℕ := (univ.filter fun i => a i = 0).card

omit [DecidableEq ι] in
/-- A sum of nonnegative integer deficits dominates the number of nonzero terms. -/
theorem deficit_sum_lower (a : ι → ℕ) (s : Finset ι) :
    (s.card : ℚ) - zeroCount a ≤ ∑ i ∈ s, (a i : ℚ) := by
  have hcount : (s.filter fun i => a i = 0).card ≤ zeroCount a := by
    apply Finset.card_le_card
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    exact hi.2
  have hsum : (s.filter fun i => a i ≠ 0).card ≤ ∑ i ∈ s, a i := by
    calc
      (s.filter fun i => a i ≠ 0).card =
          ∑ i ∈ s, if a i = 0 then 0 else 1 := by simp [Finset.card_filter, ite_not]
      _ ≤ ∑ i ∈ s, a i := by
        apply Finset.sum_le_sum
        intro i hi
        split_ifs with h
        · omega
        · omega
  have hpartition : (s.filter fun i => a i = 0).card +
      (s.filter fun i => a i ≠ 0).card = s.card := by
    simpa using Finset.card_filter_add_card_filter_not (s := s) (p := fun i => a i = 0)
  have hh : s.card ≤ zeroCount a + ∑ i ∈ s, a i := by omega
  have hc : (s.card : ℚ) ≤ (zeroCount a : ℚ) + ∑ i ∈ s, (a i : ℚ) := by
    exact_mod_cast hh
  linarith

omit [DecidableEq ι] in
/-- The sharp loss calculation in Lemma 4.2, without sorting the weights. -/
theorem perturbation_loss (a : ι → ℕ) (s t : Finset ι) (r : ℕ)
    (hst : t.card = s.card) (hr : s.card ≤ r) :
    (s.card : ℚ) - ((∑ i ∈ s, (a i : ℚ)) + ∑ i ∈ t, (a i : ℚ)) / 2 ≤
      (min r (zeroCount a) : ℕ) := by
  have hs := deficit_sum_lower a s
  have ht := deficit_sum_lower a t
  have hs0 : (0 : ℚ) ≤ ∑ i ∈ s, (a i : ℚ) := sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have ht0 : (0 : ℚ) ≤ ∑ i ∈ t, (a i : ℚ) := sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  rw [hst] at ht
  have hr' : (s.card : ℚ) ≤ r := by exact_mod_cast hr
  rw [Nat.cast_min]
  exact le_min (by linarith) (by linarith)

/-- Too many selected rows from a rank-bounded matrix force a mixed determinant to vanish. -/
theorem mixed_det_eq_zero_of_rank_lt {F : Type*} [Field F]
    (A B : Matrix ι ι F) (s : Finset ι) (hr : B.rank < s.card) :
    Matrix.det (s.piecewise B A) = 0 := by
  by_contra hne
  have hli := Matrix.linearIndependent_rows_of_det_ne_zero hne
  have hli' : LinearIndependent F (fun i : s => B i) := by
    simpa [Matrix.row, Function.comp_def, Finset.piecewise] using hli.comp (fun i : s => (i : ι)) Subtype.val_injective
  have hdim : s.card ≤ Module.finrank F (Submodule.span F (Set.range fun i : s => B i)) := by
    simpa [Set.finrank] using (linearIndependent_iff_card_le_finrank_span.mp hli')
  have hspan : Submodule.span F (Set.range fun i : s => B i) ≤
      Submodule.span F (Set.range B.row) := by
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨i, rfl⟩
  have hdim' := Submodule.finrank_mono hspan
  rw [Matrix.rank_eq_finrank_span_row] at hr
  omega

/-- The permutation-by-permutation bound used for every surviving mixed determinant. -/
theorem permutation_exponent_bound (a : ι → ℕ) (s : Finset ι)
    (σ : Equiv.Perm ι) (r : ℕ) (hr : s.card ≤ r) :
    -(∑ i, (a i : ℚ)) - (min r (zeroCount a) : ℕ) ≤
      ∑ i, if i ∈ s then (-1 : ℚ) else -((a i : ℚ) + a (σ i)) / 2 := by
  have himage : (s.image σ).card = s.card := card_image_of_injective s σ.injective
  have hloss := perturbation_loss a s (s.image σ) r himage hr
  rw [sum_image (fun i _ j _ h => σ.injective h)] at hloss
  have hsum : (∑ i, (a (σ i) : ℚ)) = ∑ i, (a i : ℚ) := Equiv.sum_comp σ (fun i => (a i : ℚ))
  have heq : (∑ i, if i ∈ s then (-1 : ℚ) else -((a i : ℚ) + a (σ i)) / 2) =
      -(∑ i, (a i : ℚ)) - (s.card : ℚ) +
        ((∑ i ∈ s, (a i : ℚ)) + ∑ i ∈ s, (a (σ i) : ℚ)) / 2 := by
    have hpoint : ∀ i, (if i ∈ s then (-1 : ℚ) else -((a i : ℚ) + a (σ i)) / 2) =
        -((a i : ℚ) + a (σ i)) / 2 +
          (if i ∈ s then -1 + ((a i : ℚ) + a (σ i)) / 2 else 0) := by
      intro i
      split_ifs <;> ring
    simp_rw [hpoint]
    simp only [sum_add_distrib, ← sum_div, sum_neg_distrib, sum_ite_mem, univ_inter,
      sum_add_distrib, sum_const, nsmul_eq_mul]
    rw [hsum]
    ring
  rw [heq]
  linarith

omit [Fintype ι] in
/-- Multiplicativity gives a sum of any specified lower bounds for the factors. -/
theorem valuation_prod_lower {F : Type*} [Field F] (v : AddValuation F (WithTop ℚ))
    (s : Finset ι) (f : ι → F) (b : ι → ℚ)
    (hb : ∀ i ∈ s, (b i : WithTop ℚ) ≤ v (f i)) :
    ((∑ i ∈ s, b i : ℚ) : WithTop ℚ) ≤ v (∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [sum_insert hi, prod_insert hi, AddValuation.map_mul, WithTop.coe_add]
    apply add_le_add (hb i (mem_insert_self _ _))
    exact ih (fun j hj => hb j (mem_insert_of_mem hj))

/-- A general valuation bound for determinants from bounds on all permutation terms. -/
theorem det_lower_of_permutation_bounds {F : Type*} [Field F]
    (v : AddValuation F (WithTop ℚ)) (M : Matrix ι ι F) (b : ι → ι → ℚ) (e : ℚ)
    (hentry : ∀ i j, (b i j : WithTop ℚ) ≤ v (M i j))
    (hexp : ∀ σ : Equiv.Perm ι, e ≤ ∑ i, b i (σ i)) :
    (e : WithTop ℚ) ≤ v M.det := by
  rw [← Matrix.det_transpose, Matrix.det_apply']
  apply v.map_le_sum
  intro σ hσ
  have hp := valuation_prod_lower v univ (fun i => M i (σ i))
    (fun i => b i (σ i)) (fun i _ => hentry i (σ i))
  have he : (e : WithTop ℚ) ≤ ((∑ i, b i (σ i) : ℚ) : WithTop ℚ) :=
    WithTop.coe_le_coe.mpr (hexp σ)
  have hs : v (((Equiv.Perm.sign σ : ℤ) : F)) = 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  simpa only [Matrix.transpose_apply, AddValuation.map_mul, hs, zero_add] using he.trans hp

/-- **Lemma 4.2, general rank-sensitive perturbation form.**

The weights are `w i = -a i / 2`, where `a i` is a natural number. Thus they
range over all nonpositive half-integers. The matrix `B` is the already-scaled
perturbation `p⁻¹ L`; its entries have valuation at least `-1` and its rank is
at most `r`. The conclusion is `v(det(A+B)) ≥ 2∑wᵢ - min(r,z)`.
-/
theorem det_rank_perturbation {F : Type*} [Field F]
    (v : AddValuation F (WithTop ℚ)) (A B : Matrix ι ι F)
    (a : ι → ℕ) (r : ℕ)
    (hA : ∀ i j, ((-((a i : ℚ) + a j) / 2 : ℚ) : WithTop ℚ) ≤ v (A i j))
    (hB : ∀ i j, (-1 : WithTop ℚ) ≤ v (B i j))
    (hrank : B.rank ≤ r) :
    ((-(∑ i, (a i : ℚ)) - (min r (zeroCount a) : ℕ) : ℚ) : WithTop ℚ) ≤
      v (A + B).det := by
  have hexpand : (B + A).det = ∑ s : Finset ι, Matrix.det (s.piecewise B A) := by
    exact Matrix.detRowAlternating.toMultilinearMap.map_add_univ B A
  rw [add_comm A B, hexpand]
  apply v.map_le_sum
  intro s hs
  by_cases hsr : s.card ≤ r
  · apply det_lower_of_permutation_bounds v (s.piecewise B A)
      (fun i j => if i ∈ s then -1 else -((a i : ℚ) + a j) / 2)
    · intro i j
      by_cases hi : i ∈ s
      · simpa [hi, Finset.piecewise] using hB i j
      · simpa [hi, Finset.piecewise] using hA i j
    · intro σ
      exact permutation_exponent_bound a s σ r hsr
  · have hlt : B.rank < s.card := lt_of_le_of_lt hrank (Nat.lt_of_not_ge hsr)
    rw [mixed_det_eq_zero_of_rank_lt A B s hlt, AddValuation.map_zero]
    exact le_top

/-- Multiplication of an integral matrix by a scalar of valuation at least `-1`
specializes the preceding theorem to the form stated in the paper. -/
theorem det_integral_rank_correction {F : Type*} [Field F]
    (v : AddValuation F (WithTop ℚ)) (A L : Matrix ι ι F)
    (c : F) (a : ι → ℕ) (r : ℕ)
    (hA : ∀ i j, ((-((a i : ℚ) + a j) / 2 : ℚ) : WithTop ℚ) ≤ v (A i j))
    (hL : ∀ i j, (0 : WithTop ℚ) ≤ v (L i j))
    (hc : (-1 : WithTop ℚ) ≤ v c)
    (hrank : L.rank ≤ r) :
    ((-(∑ i, (a i : ℚ)) - (min r (zeroCount a) : ℕ) : ℚ) : WithTop ℚ) ≤
      v (A + c • L).det := by
  apply det_rank_perturbation v A (c • L) a r hA
  · intro i j
    change (-1 : WithTop ℚ) ≤ v (c * L i j)
    rw [AddValuation.map_mul]
    simpa using add_le_add hc (hL i j)
  · have heq : c • L = Matrix.diagonal (fun _ : ι => c) * L := by
      ext i j
      simp [Matrix.diagonal_mul]
    rw [heq]
    exact (Matrix.rank_mul_le_right _ L).trans hrank

/-- A matrix supported on `s` rows has rank at most `s.card`. -/
theorem rank_le_card_support_rows {F : Type*} [Field F]
    (L : Matrix ι ι F) (s : Finset ι)
    (hzero : ∀ i, i ∉ s → ∀ j, L i j = 0) : L.rank ≤ s.card := by
  let E : Matrix ι s F := fun i j => if i = j then 1 else 0
  let R : Matrix s ι F := fun i j => L i j
  have heq : L = E * R := by
    ext i j
    by_cases hi : i ∈ s
    · symm
      apply (Finset.sum_eq_single (⟨i, hi⟩ : s) ?_ ?_).trans
      · simp [E, R]
      · intro k hk hki
        have hk' : i ≠ (k : ι) := by
          intro h
          apply hki
          exact Subtype.ext h.symm
        simp [E, hk']
      · simp
    · simp only [Matrix.mul_apply]
      rw [hzero i hi j]
      symm
      apply sum_eq_zero
      intro k hk
      have hk' : i ≠ (k : ι) := by
        intro h
        exact hi (h ▸ k.property)
      simp [E, hk']
  rw [heq]
  exact (Matrix.rank_mul_le_right E R).trans (by simpa using R.rank_le_card_height)

/-- Vanishing of the first `h-r` rows implies a rank bound of `r`. -/
theorem rank_le_of_initial_rows_zero {F : Type*} [Field F] {h r : ℕ}
    (L : Matrix (Fin h) (Fin h) F)
    (hzero : ∀ i : Fin h, i.val < h - r → ∀ j, L i j = 0) : L.rank ≤ r := by
  let s : Finset (Fin h) := univ.filter fun i => h - r ≤ i.val
  have hrank : L.rank ≤ s.card := rank_le_card_support_rows L s (by
    intro i hi j
    apply hzero i
    simp only [s, mem_filter, mem_univ, true_and, not_le] at hi
    exact hi)
  have hcard : s.card ≤ r := by
    let f : s → Fin r := fun i => ⟨i.val.val - (h - r), by
      have hi := i.val.isLt
      have his : h - r ≤ i.val.val := (mem_filter.mp i.property).2
      omega⟩
    have hf : Function.Injective f := by
      intro i j hij
      have hi : h - r ≤ i.val.val := (mem_filter.mp i.property).2
      have hj : h - r ≤ j.val.val := (mem_filter.mp j.property).2
      have he : i.val.val - (h - r) = j.val.val - (h - r) := congrArg Fin.val hij
      apply Subtype.ext
      apply Fin.ext
      omega
    simpa using Fintype.card_le_of_injective f hf
  exact hrank.trans hcard

/-- The exact support-to-rank implication in equation (4.10).

The support hypothesis is written without subtraction: it is equivalent to
`Lᵢⱼ = 0` when `i+j < K-6N+2p-3`. The natural subtraction on the right
is exactly `max(0, K+4N-2p+2)`.
-/
theorem correction_rank_bound {F : Type*} [Field F] (K N p h : ℕ)
    (hsize : K = N + h) (L : Matrix (Fin h) (Fin h) F)
    (hzero : ∀ i j, i.val + j.val + 6 * N + 3 < K + 2 * p → L i j = 0) :
    L.rank ≤ K + 4 * N + 2 - 2 * p := by
  apply rank_le_of_initial_rows_zero L
  intro i hi j
  apply hzero i j
  have hj := j.isLt
  omega

section PolynomialCoefficients

variable {F : Type*} [Field F]

/-- A Gauss-valuation lower bound, expressed directly on every coefficient.
This definition includes zero coefficients, since `v(0)=⊤`. -/
def CoeffLower (v : AddValuation F (WithTop ℚ)) (P : Polynomial F) (e : ℚ) : Prop :=
  ∀ n : ℕ, (e : WithTop ℚ) ≤ v (P.coeff n)

theorem coeffLower_zero (v : AddValuation F (WithTop ℚ)) (e : ℚ) :
    CoeffLower v 0 e := by
  intro n
  simp

theorem coeffLower_mono (v : AddValuation F (WithTop ℚ)) {P : Polynomial F}
    {e f : ℚ} (h : CoeffLower v P e) (hf : f ≤ e) : CoeffLower v P f := by
  intro n
  exact (WithTop.coe_le_coe.mpr hf).trans (h n)

theorem coeffLower_C (v : AddValuation F (WithTop ℚ)) (x : F) (e : ℚ)
    (h : (e : WithTop ℚ) ≤ v x) : CoeffLower v (Polynomial.C x) e := by
  intro n
  by_cases hn : n = 0
  · simpa [hn] using h
  · simp [Polynomial.coeff_C, hn]

theorem coeffLower_sum {κ : Type*} (v : AddValuation F (WithTop ℚ))
    (s : Finset κ) (P : κ → Polynomial F) (e : ℚ)
    (h : ∀ i ∈ s, CoeffLower v (P i) e) : CoeffLower v (∑ i ∈ s, P i) e := by
  intro n
  simp only [Polynomial.finsetSum_coeff]
  exact v.map_le_sum (fun i hi => h i hi n)

theorem coeffLower_mul (v : AddValuation F (WithTop ℚ))
    {P Q : Polynomial F} {e f : ℚ}
    (hP : CoeffLower v P e) (hQ : CoeffLower v Q f) : CoeffLower v (P * Q) (e + f) := by
  intro n
  rw [Polynomial.coeff_mul]
  apply v.map_le_sum
  intro ij hij
  rw [AddValuation.map_mul, WithTop.coe_add]
  exact add_le_add (hP ij.1) (hQ ij.2)

theorem coeffLower_prod {κ : Type*} [DecidableEq κ] (v : AddValuation F (WithTop ℚ))
    (s : Finset κ) (P : κ → Polynomial F) (e : κ → ℚ)
    (h : ∀ i ∈ s, CoeffLower v (P i) (e i)) :
    CoeffLower v (∏ i ∈ s, P i) (∑ i ∈ s, e i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [prod_empty, sum_empty]
    simpa using coeffLower_C v (1 : F) 0 (by simp)
  | @insert i s hi ih =>
    rw [prod_insert hi, sum_insert hi]
    exact coeffLower_mul v (h i (mem_insert_self _ _))
      (ih (fun j hj => h j (mem_insert_of_mem hj)))

theorem coeffLower_neg (v : AddValuation F (WithTop ℚ))
    {P : Polynomial F} {e : ℚ} (h : CoeffLower v P e) : CoeffLower v (-P) e := by
  intro n
  simpa using h n

/-- Determinant bounds for the Gauss valuation need only coefficient convolution;
no valuation on a rational-function field is assumed. -/
theorem polynomial_det_lower_of_permutation_bounds
    (v : AddValuation F (WithTop ℚ)) (M : Matrix ι ι (Polynomial F))
    (b : ι → ι → ℚ) (e : ℚ)
    (hentry : ∀ i j, CoeffLower v (M i j) (b i j))
    (hexp : ∀ σ : Equiv.Perm ι, e ≤ ∑ i, b i (σ i)) :
    CoeffLower v M.det e := by
  rw [← Matrix.det_transpose, Matrix.det_apply']
  apply coeffLower_sum
  intro σ hσ
  have hp := coeffLower_prod v univ (fun i => M i (σ i))
    (fun i => b i (σ i)) (fun i _ => hentry i (σ i))
  have hp' := coeffLower_mono v hp (hexp σ)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · simpa [h, Matrix.transpose_apply] using hp'
  · simpa [h, Matrix.transpose_apply] using coeffLower_neg v hp'

/-- Rank-killing for polynomial matrices with a constant perturbation.
Infinite fields include both `ℚ` and `ℚ_p`. -/
theorem mixed_polynomial_det_eq_zero_of_rank_lt [Infinite F]
    (A : Matrix ι ι (Polynomial F)) (B : Matrix ι ι F) (s : Finset ι)
    (hr : B.rank < s.card) :
    Matrix.det (s.piecewise (B.map Polynomial.C) A) = 0 := by
  apply Polynomial.funext
  intro x
  rw [Polynomial.eval_zero]
  change (Polynomial.evalRingHom x) (Matrix.det (s.piecewise (B.map Polynomial.C) A)) = 0
  erw [(Polynomial.evalRingHom x).map_det]
  have hmap : Matrix.map (s.piecewise (B.map Polynomial.C) A) (Polynomial.evalRingHom x) =
      s.piecewise B (A.map (Polynomial.evalRingHom x)) := by
    ext i j
    by_cases hi : i ∈ s <;> simp [Matrix.map, Finset.piecewise, hi]
  change Matrix.det (Matrix.map (s.piecewise (B.map Polynomial.C) A) (Polynomial.evalRingHom x)) = 0
  rw [hmap]
  exact mixed_det_eq_zero_of_rank_lt _ B s hr

/-- **Polynomial/Gauss form of Lemma 4.2**, proved coefficient by coefficient.
The only rank hypothesis is on the constant matrix `B`, over the original field. -/
theorem polynomial_det_rank_perturbation [Infinite F]
    (v : AddValuation F (WithTop ℚ)) (A : Matrix ι ι (Polynomial F))
    (B : Matrix ι ι F) (a : ι → ℕ) (r : ℕ)
    (hA : ∀ i j, CoeffLower v (A i j) (-((a i : ℚ) + a j) / 2))
    (hB : ∀ i j, (-1 : WithTop ℚ) ≤ v (B i j))
    (hrank : B.rank ≤ r) :
    CoeffLower v (A + B.map Polynomial.C).det
      (-(∑ i, (a i : ℚ)) - (min r (zeroCount a) : ℕ)) := by
  have hexpand : (B.map Polynomial.C + A).det =
      ∑ s : Finset ι, Matrix.det (s.piecewise (B.map Polynomial.C) A) := by
    exact Matrix.detRowAlternating.toMultilinearMap.map_add_univ _ A
  rw [add_comm A (B.map Polynomial.C), hexpand]
  apply coeffLower_sum
  intro s hs
  by_cases hsr : s.card ≤ r
  · apply polynomial_det_lower_of_permutation_bounds v
      (s.piecewise (B.map Polynomial.C) A)
      (fun i j => if i ∈ s then -1 else -((a i : ℚ) + a j) / 2)
    · intro i j
      by_cases hi : i ∈ s
      · simpa [hi, Finset.piecewise, Matrix.map_apply] using coeffLower_C v (B i j) (-1) (hB i j)
      · simpa [hi, Finset.piecewise] using hA i j
    · intro σ
      exact permutation_exponent_bound a s σ r hsr
  · have hlt : B.rank < s.card := lt_of_le_of_lt hrank (Nat.lt_of_not_ge hsr)
    rw [mixed_polynomial_det_eq_zero_of_rank_lt A B s hlt]
    exact coeffLower_zero v _

/-- The paper's exact correction `A + c L`, with integral constant `L`,
now as a lower bound on *every coefficient* of the determinant polynomial. -/
theorem polynomial_det_integral_rank_correction [Infinite F]
    (v : AddValuation F (WithTop ℚ)) (A : Matrix ι ι (Polynomial F))
    (L : Matrix ι ι F) (c : F) (a : ι → ℕ) (r : ℕ)
    (hA : ∀ i j, CoeffLower v (A i j) (-((a i : ℚ) + a j) / 2))
    (hL : ∀ i j, (0 : WithTop ℚ) ≤ v (L i j))
    (hc : (-1 : WithTop ℚ) ≤ v c) (hrank : L.rank ≤ r) :
    ∀ n, ((-(∑ i, (a i : ℚ)) - (min r (zeroCount a) : ℕ) : ℚ) : WithTop ℚ) ≤
      v ((A + (c • L).map Polynomial.C).det.coeff n) := by
  apply polynomial_det_rank_perturbation v A (c • L) a r hA
  · intro i j
    change (-1 : WithTop ℚ) ≤ v (c * L i j)
    rw [AddValuation.map_mul]
    simpa using add_le_add hc (hL i j)
  · have heq : c • L = Matrix.diagonal (fun _ : ι => c) * L := by
      ext i j
      simp [Matrix.diagonal_mul]
    rw [heq]
    exact (Matrix.rank_mul_le_right _ L).trans hrank

end PolynomialCoefficients

/-- The rational p-adic valuation with its mathematically correct value at zero,
embedded in `WithTop ℚ` to permit half-integer row weights. -/
def rationalPadicValuation (p : ℕ) [Fact p.Prime] : AddValuation ℚ (WithTop ℚ) := by
  refine AddValuation.of
    (fun q : ℚ => if q = 0 then ⊤ else (((padicValRat p q : ℤ) : ℚ) : WithTop ℚ))
    (by simp) (by simp) ?_ ?_
  · intro q r
    by_cases hq : q = 0
    · simp [hq]
    by_cases hr : r = 0
    · simp [hr]
    by_cases hqr : q + r = 0
    · simp [hqr]
    simp only [if_neg hq, if_neg hr, if_neg hqr, ← WithTop.coe_min, WithTop.coe_le_coe]
    exact_mod_cast padicValRat.min_le_padicValRat_add (p := p) hqr
  · intro q r
    by_cases hq : q = 0
    · simp [hq]
    by_cases hr : r = 0
    · simp [hr]
    simp [hq, hr, mul_ne_zero hq hr, padicValRat.mul hq hr, WithTop.coe_add]

@[simp] theorem rationalPadicValuation_apply (p : ℕ) [Fact p.Prime] (q : ℚ) :
    rationalPadicValuation p q =
      if q = 0 then ⊤ else (((padicValRat p q : ℤ) : ℚ) : WithTop ℚ) := rfl

/-- Converts safely between valuations with `v(0)=⊤` and mathlib's
`padicValRat`, which has the conventional fallback `padicValRat p 0 = 0`. -/
theorem rationalPadicValuation_lower_iff (p : ℕ) [Fact p.Prime] (q e : ℚ) :
    (e : WithTop ℚ) ≤ rationalPadicValuation p q ↔ q = 0 ∨ e ≤ (padicValRat p q : ℚ) := by
  by_cases hq : q = 0 <;> simp [hq]

/-- Lemma 4.2 directly usable with rational-coefficient paper matrices and
`padicValRat`; every zero-coefficient case is stated explicitly. -/
theorem rational_polynomial_det_padic_correction (p : ℕ) [hp : Fact p.Prime]
    (A : Matrix ι ι (Polynomial ℚ)) (L : Matrix ι ι ℚ) (a : ι → ℕ) (r : ℕ)
    (hA : ∀ i j n, (A i j).coeff n = 0 ∨
      -((a i : ℚ) + a j) / 2 ≤ (padicValRat p ((A i j).coeff n) : ℚ))
    (hL : ∀ i j, 0 ≤ padicValRat p (L i j)) (hrank : L.rank ≤ r) :
    ∀ n, ((A + ((p : ℚ)⁻¹ • L).map Polynomial.C).det).coeff n = 0 ∨
      -(∑ i, (a i : ℚ)) - (min r (zeroCount a) : ℕ) ≤
        (padicValRat p (((A + ((p : ℚ)⁻¹ • L).map Polynomial.C).det).coeff n) : ℚ) := by
  have hA' : ∀ i j, CoeffLower (rationalPadicValuation p) (A i j)
      (-((a i : ℚ) + a j) / 2) := by
    intro i j n
    exact (rationalPadicValuation_lower_iff p _ _).mpr (hA i j n)
  have hL' : ∀ i j, (0 : WithTop ℚ) ≤ rationalPadicValuation p (L i j) := by
    intro i j
    apply (rationalPadicValuation_lower_iff p _ 0).mpr
    right
    exact_mod_cast hL i j
  have hc : (-1 : WithTop ℚ) ≤ rationalPadicValuation p (p : ℚ)⁻¹ := by
    apply (rationalPadicValuation_lower_iff p _ (-1)).mpr
    right
    rw [padicValRat.inv, padicValRat.self hp.out.one_lt]
    norm_num
  have h := polynomial_det_integral_rank_correction (rationalPadicValuation p)
    A L (p : ℚ)⁻¹ a r hA' hL' hc hrank
  intro n
  exact (rationalPadicValuation_lower_iff p _ _).mp (h n)

section OrdinaryPoleCongruence

/-- Integer inputs are integral for the rational p-adic valuation. -/
theorem rationalPadicValuation_int_nonneg (p : ℕ) [Fact p.Prime] (z : ℤ) :
    (0 : WithTop ℚ) ≤ rationalPadicValuation p (z : ℚ) := by
  apply (rationalPadicValuation_lower_iff p _ 0).mpr
  right
  rw [padicValRat.of_int]
  positivity

/-- Every positive integer below `p` is a p-adic unit. -/
theorem rationalPadicValuation_unit_below (p k : ℕ) [Fact p.Prime]
    (hk : 0 < k) (hkp : k < p) : rationalPadicValuation p (k : ℚ) = 0 := by
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [rationalPadicValuation_apply, if_neg hk0, padicValRat.of_nat,
    padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt hk hkp)]
  rfl

/-- Pairing reflected fifth reciprocals supplies one factor of `p`.
This is the harmonic congruence used for the two near poles in Section 4.2. -/
theorem reflected_fifth_reciprocals (p k : ℕ) [hp : Fact p.Prime]
    (hk : 0 < k) (hkp : k < p) :
    (1 : WithTop ℚ) ≤ rationalPadicValuation p
      (((k : ℚ)^5)⁻¹ + (((p-k : ℕ) : ℚ)^5)⁻¹) := by
  have hpk : 0 < p-k := Nat.sub_pos_of_lt hkp
  have hpkp : p-k < p := Nat.sub_lt hp.out.pos hk
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have hpk0 : ((p-k : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hpk.ne'
  let z : ℤ := (p : ℤ)^4 - 5*(p : ℤ)^3*k + 10*(p : ℤ)^2*(k : ℤ)^2 -
    10*(p : ℤ)*(k : ℤ)^3 + 5*(k : ℤ)^4
  have heq : ((k : ℚ)^5)⁻¹ + (((p-k : ℕ) : ℚ)^5)⁻¹ =
      (p : ℚ)*(z : ℚ)*(((k : ℚ)^5 * (((p-k : ℕ) : ℚ)^5))⁻¹) := by
    field_simp
    rw [Nat.cast_sub hkp.le]
    dsimp [z]
    push_cast
    ring
  rw [heq, AddValuation.map_mul, AddValuation.map_mul]
  have hpv : rationalPadicValuation p (p : ℚ) = 1 := by
    rw [rationalPadicValuation_apply, if_neg (by exact_mod_cast hp.out.ne_zero),
      padicValRat.self hp.out.one_lt]
    rfl
  have hden : rationalPadicValuation p (((k : ℚ)^5 * (((p-k : ℕ) : ℚ)^5))⁻¹) = 0 := by
    have hkn : padicValRat p (k : ℚ) = 0 := by
      rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt hk hkp)]
      rfl
    have hpkn : padicValRat p ((p-k : ℕ) : ℚ) = 0 := by
      rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt hpk hpkp)]
      rfl
    rw [rationalPadicValuation_apply, if_neg (inv_ne_zero (mul_ne_zero (pow_ne_zero _ hk0)
      (pow_ne_zero _ hpk0))), padicValRat.inv,
      padicValRat.mul (pow_ne_zero _ hk0) (pow_ne_zero _ hpk0),
      padicValRat.pow (k : ℚ), padicValRat.pow ((p-k : ℕ) : ℚ), hkn, hpkn]
    norm_num
  rw [hpv, hden, add_zero]
  simpa using add_le_add (le_refl (1 : WithTop ℚ)) (rationalPadicValuation_int_nonneg p z)

/-- The finite fifth harmonic sum, with the same definition as the paper construction. -/
def fifthHarmonic (m : ℕ) : ℚ := ∑ k ∈ range m, 1 / (((k+1 : ℕ) : ℚ)^5)

lemma fifthHarmonic_Ico (m : ℕ) :
    fifthHarmonic m = ∑ k ∈ Ico 1 (m+1), ((k : ℚ)^5)⁻¹ := by
  simp [fifthHarmonic, Finset.sum_Ico_eq_sum_range, one_div, Nat.add_comm]

/-- The ordinary-pole harmonic reflection congruence stated in Section 4.2:
`H_(p-a)^(5) ≡ H_(a-1)^(5) (mod p)`.
It is proved over the rationals with the exact p-adic valuation. -/
theorem fifthHarmonic_reflection (p a : ℕ) [Fact p.Prime]
    (hp : 3 ≤ p) (ha : 0 < a) (hap : 2*a < p) :
    (1 : WithTop ℚ) ≤ rationalPadicValuation p (fifthHarmonic (p-a) - fifthHarmonic (a-1)) := by
  let f : ℕ → ℚ := fun k => ((k : ℚ)^5)⁻¹
  let S : ℚ := ∑ k ∈ Ico a (p-a+1), f k
  have hreflect : (∑ k ∈ Ico a (p-a+1), f (p-k)) = S := by
    have hh := Finset.sum_Ico_reflect f a (n := p) (m := p-a+1) (by omega)
    have hleft : p+1-(p-a+1) = a := by omega
    have hright : p+1-a = p-a+1 := by omega
    simpa only [hleft, hright] using hh
  have hpair : (1 : WithTop ℚ) ≤ rationalPadicValuation p (2*S) := by
    have hs : (1 : WithTop ℚ) ≤ rationalPadicValuation p
        (∑ k ∈ Ico a (p-a+1), (f k + f (p-k))) := by
      apply (rationalPadicValuation p).map_le_sum
      intro k hk
      obtain ⟨hak, hkp⟩ := mem_Ico.mp hk
      exact reflected_fifth_reciprocals p k (by omega) (by omega)
    rw [Finset.sum_add_distrib, hreflect] at hs
    simpa only [S, two_mul] using hs
  have htwo : rationalPadicValuation p (2 : ℚ) = 0 :=
    rationalPadicValuation_unit_below p 2 (by omega) (by omega)
  rw [AddValuation.map_mul, htwo, zero_add] at hpair
  have hsplit := Finset.sum_Ico_consecutive f (m := 1) (n := a) (k := p-a+1)
    (by omega) (by omega)
  have ha1 : a-1+1 = a := by omega
  rw [fifthHarmonic_Ico, fifthHarmonic_Ico, ha1]
  have heq : (∑ k ∈ Ico 1 (p-a+1), f k) - (∑ k ∈ Ico 1 a, f k) = S := by
    dsimp [S]
    linarith
  change (1 : WithTop ℚ) ≤ rationalPadicValuation p
    ((∑ k ∈ Ico 1 (p-a+1), f k) - (∑ k ∈ Ico 1 a, f k))
  rw [heq]
  exact hpair

theorem rationalPadicValuation_prime_mul_int (p : ℕ) [hp : Fact p.Prime] (z : ℤ) :
    (1 : WithTop ℚ) ≤ rationalPadicValuation p ((p : ℚ)*(z : ℚ)) := by
  have hpv : rationalPadicValuation p (p : ℚ) = 1 := by
    rw [rationalPadicValuation_apply, if_neg (by exact_mod_cast hp.out.ne_zero),
      padicValRat.self hp.out.one_lt]
    rfl
  rw [AddValuation.map_mul, hpv]
  simpa using add_le_add (le_refl (1 : WithTop ℚ)) (rationalPadicValuation_int_nonneg p z)

theorem rationalPadicValuation_inv_unit (p : ℕ) [Fact p.Prime] (q : ℚ)
    (hq : rationalPadicValuation p q = 0) : rationalPadicValuation p q⁻¹ = 0 := by
  have hq0 : q ≠ 0 := by
    intro h
    simp [h] at hq
  have hv : padicValRat p q = 0 := by
    rw [rationalPadicValuation_apply, if_neg hq0] at hq
    exact_mod_cast hq
  rw [rationalPadicValuation_apply, if_neg (inv_ne_zero hq0), padicValRat.inv, hv]
  rfl

theorem fifthHarmonic_integral_below (p m : ℕ) [Fact p.Prime] (hm : m < p) :
    (0 : WithTop ℚ) ≤ rationalPadicValuation p (fifthHarmonic m) := by
  unfold fifthHarmonic
  apply (rationalPadicValuation p).map_le_sum
  intro k hk
  have hk' := mem_range.mp hk
  have hv := rationalPadicValuation_unit_below p (k+1) (by omega) (by omega)
  have hpow : rationalPadicValuation p (((k+1 : ℕ) : ℚ)^5) = 0 := by
    rw [AddValuation.map_pow, hv]
    simp
  simpa only [one_div, rationalPadicValuation_inv_unit p _ hpow] using (le_refl (0 : WithTop ℚ))

lemma fifthHarmonic_succ (m : ℕ) :
    fifthHarmonic (m+1) = fifthHarmonic m + 1 / (((m+1 : ℕ) : ℚ)^5) := by
  simp only [fifthHarmonic, sum_range_succ]

/-- The two ordinary-class fourth powers agree modulo `p`. -/
theorem reflected_fourth_powers (p a : ℕ) [Fact p.Prime] (ha : a ≤ p) :
    (1 : WithTop ℚ) ≤ rationalPadicValuation p
      ((a : ℚ)^4 - (((p-a : ℕ) : ℚ)^4)) := by
  let z : ℤ := -(p : ℤ)^3 + 4*(p : ℤ)^2*a - 6*(p : ℤ)*(a : ℤ)^2 + 4*(a : ℤ)^3
  have heq : (a : ℚ)^4 - (((p-a : ℕ) : ℚ)^4) = (p : ℚ)*(z : ℚ) := by
    rw [Nat.cast_sub ha]
    dsimp [z]
    push_cast
    ring
  rw [heq]
  exact rationalPadicValuation_prime_mul_int p z

/-- The constant coefficient in the paper's affine simple-pole functional. -/
def localPoleConstant (j : ℕ) : ℚ :=
  -(j : ℚ)^4 * fifthHarmonic j - 1/4 + 1/(2*(j : ℚ))

/-- The actual ordinary-class near-pole constants agree modulo `p`.
Together with `reflected_fourth_powers`, this proves the coefficientwise
congruence invoked in Section 4.2, including the constant coefficient. -/
theorem localPoleConstant_reflection (p a : ℕ) [Fact p.Prime]
    (hp : 3 ≤ p) (ha : 0 < a) (hap : 2*a < p) :
    (1 : WithTop ℚ) ≤ rationalPadicValuation p (localPoleConstant (p-a) - localPoleConstant a) := by
  have hap' : a < p := by omega
  have hb : 0 < p-a := by omega
  have hbp : p-a < p := by omega
  have ha0 : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb0 : ((p-a : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hH : fifthHarmonic a = fifthHarmonic (a-1) + 1/(a : ℚ)^5 := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ a)] using fifthHarmonic_succ (a-1)
  have heq : localPoleConstant (p-a) - localPoleConstant a =
      -(((p-a : ℕ) : ℚ)^4) * (fifthHarmonic (p-a) - fifthHarmonic (a-1)) +
      ((a : ℚ)^4 - (((p-a : ℕ) : ℚ)^4)) * fifthHarmonic (a-1) +
      (p : ℚ) / (2*(a : ℚ)*((p-a : ℕ) : ℚ)) := by
    dsimp [localPoleConstant]
    rw [hH]
    field_simp
    rw [Nat.cast_sub hap'.le]
    ring
  have hfirst : (1 : WithTop ℚ) ≤ rationalPadicValuation p
      (-(((p-a : ℕ) : ℚ)^4) * (fifthHarmonic (p-a) - fifthHarmonic (a-1))) := by
    rw [AddValuation.map_mul, AddValuation.map_neg, AddValuation.map_pow,
      rationalPadicValuation_unit_below p (p-a) hb hbp]
    simpa using fifthHarmonic_reflection p a hp ha hap
  have hsecond : (1 : WithTop ℚ) ≤ rationalPadicValuation p
      (((a : ℚ)^4 - (((p-a : ℕ) : ℚ)^4)) * fifthHarmonic (a-1)) := by
    rw [AddValuation.map_mul]
    simpa using add_le_add (reflected_fourth_powers p a hap'.le)
      (fifthHarmonic_integral_below p (a-1) (by omega))
  have hthird : (1 : WithTop ℚ) ≤ rationalPadicValuation p
      ((p : ℚ) / (2*(a : ℚ)*((p-a : ℕ) : ℚ))) := by
    have hden : rationalPadicValuation p (2*(a : ℚ)*((p-a : ℕ) : ℚ)) = 0 := by
      have htwo : rationalPadicValuation p (2 : ℚ) = 0 :=
        rationalPadicValuation_unit_below p 2 (by omega) (by omega)
      rw [AddValuation.map_mul, AddValuation.map_mul, htwo,
        rationalPadicValuation_unit_below p a ha hap',
        rationalPadicValuation_unit_below p (p-a) hb hbp]
      simp
    rw [div_eq_mul_inv, AddValuation.map_mul, rationalPadicValuation_inv_unit p _ hden, add_zero]
    simpa using rationalPadicValuation_prime_mul_int p 1
  rw [heq]
  exact (rationalPadicValuation p).map_le_add
    ((rationalPadicValuation p).map_le_add hfirst hsecond) hthird

theorem rationalPadicValuation_inv_finite (p : ℕ) [Fact p.Prime] (q e : ℚ)
    (hq : rationalPadicValuation p q = (e : WithTop ℚ)) :
    rationalPadicValuation p q⁻¹ = ((-e : ℚ) : WithTop ℚ) := by
  have hq0 : q ≠ 0 := by
    intro h
    simp [h] at hq
  have hv : (padicValRat p q : ℚ) = e := by
    rw [rationalPadicValuation_apply, if_neg hq0] at hq
    exact WithTop.coe_injective hq
  rw [rationalPadicValuation_apply, if_neg (inv_ne_zero hq0), padicValRat.inv, Int.cast_neg, hv]

/-- The two near square nodes have distance of valuation exactly one. -/
theorem reflected_square_difference_valuation (p a : ℕ) [hp : Fact p.Prime]
    (ha : 0 < a) (hap : 2*a < p) :
    rationalPadicValuation p ((a : ℚ)^2 - (((p-a : ℕ) : ℚ)^2)) = 1 := by
  have heq : (a : ℚ)^2 - (((p-a : ℕ) : ℚ)^2) =
      -((p : ℚ)*((p-2*a : ℕ) : ℚ)) := by
    rw [Nat.cast_sub (by omega : a ≤ p), Nat.cast_sub hap.le]
    push_cast
    ring
  have hpv : rationalPadicValuation p (p : ℚ) = 1 := by
    rw [rationalPadicValuation_apply, if_neg (by exact_mod_cast hp.out.ne_zero),
      padicValRat.self hp.out.one_lt]
    rfl
  rw [heq, AddValuation.map_neg, AddValuation.map_mul, hpv,
    rationalPadicValuation_unit_below p (p-2*a) (by omega) (by omega), add_zero]

/-- The constant coefficient of the near-pole divided difference is integral. -/
theorem localPoleConstant_divided_difference_integral (p a : ℕ) [Fact p.Prime]
    (hp : 3 ≤ p) (ha : 0 < a) (hap : 2*a < p) :
    (0 : WithTop ℚ) ≤ rationalPadicValuation p
      ((localPoleConstant a - localPoleConstant (p-a)) /
        ((a : ℚ)^2 - (((p-a : ℕ) : ℚ)^2))) := by
  have hnum : (1 : WithTop ℚ) ≤ rationalPadicValuation p
      (localPoleConstant a - localPoleConstant (p-a)) := by
    rw [(rationalPadicValuation p).map_sub_swap]
    exact localPoleConstant_reflection p a hp ha hap
  have hden := rationalPadicValuation_inv_finite p
    ((a : ℚ)^2 - (((p-a : ℕ) : ℚ)^2)) 1
    (reflected_square_difference_valuation p a ha hap)
  rw [div_eq_mul_inv, AddValuation.map_mul, hden]
  have hcancel : (1 : WithTop ℚ) + ((-1 : ℚ) : WithTop ℚ) = 0 := by
    change (↑((1 : ℚ) + (-1 : ℚ)) : WithTop ℚ) = 0
    norm_num
  have hh := add_le_add hnum (le_refl ((-1 : ℚ) : WithTop ℚ))
  rw [hcancel] at hh
  exact hh

/-- The linear coefficient of the same divided difference is integral. -/
theorem localPoleLinear_divided_difference_integral (p a : ℕ) [Fact p.Prime]
    (ha : 0 < a) (hap : 2*a < p) :
    (0 : WithTop ℚ) ≤ rationalPadicValuation p
      (((a : ℚ)^4 - (((p-a : ℕ) : ℚ)^4)) /
        ((a : ℚ)^2 - (((p-a : ℕ) : ℚ)^2))) := by
  have hnum := reflected_fourth_powers p a (by omega : a ≤ p)
  have hden := rationalPadicValuation_inv_finite p
    ((a : ℚ)^2 - (((p-a : ℕ) : ℚ)^2)) 1
    (reflected_square_difference_valuation p a ha hap)
  rw [div_eq_mul_inv, AddValuation.map_mul, hden]
  have hcancel : (1 : WithTop ℚ) + ((-1 : ℚ) : WithTop ℚ) = 0 := by
    change (↑((1 : ℚ) + (-1 : ℚ)) : WithTop ℚ) = 0
    norm_num
  have hh := add_le_add hnum (le_refl ((-1 : ℚ) : WithTop ℚ))
  rw [hcancel] at hh
  exact hh

/-- Integral-coefficient polynomials preserve integrality on integral arguments. -/
theorem polynomial_eval_integral {F : Type*} [Field F]
    (v : AddValuation F (WithTop ℚ)) (P : Polynomial F)
    (hP : CoeffLower v P 0) (x : F) (hx : (0 : WithTop ℚ) ≤ v x) :
    (0 : WithTop ℚ) ≤ v (P.eval x) := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum]
  apply v.map_le_sum
  intro n hn
  rw [AddValuation.map_mul, AddValuation.map_pow]
  simpa using add_le_add (hP n) (nsmul_nonneg hx n)

/-- Powers preserve p-adic congruences between integral arguments. -/
theorem power_preserves_congruence {F : Type*} [Field F]
    (v : AddValuation F (WithTop ℚ)) (x y : F) (e : ℚ)
    (hx : (0 : WithTop ℚ) ≤ v x) (hy : (0 : WithTop ℚ) ≤ v y)
    (hxy : (e : WithTop ℚ) ≤ v (x-y)) (n : ℕ) :
    (e : WithTop ℚ) ≤ v (x^n-y^n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have heq : x^(n+1)-y^(n+1) = x*(x^n-y^n)+(x-y)*y^n := by ring
    rw [heq]
    apply v.map_le_add
    · rw [AddValuation.map_mul]
      simpa using add_le_add hx ih
    · rw [AddValuation.map_mul, AddValuation.map_pow]
      simpa using add_le_add hxy (nsmul_nonneg hy n)

/-- Integral-coefficient polynomials preserve p-adic congruences.
This gives the numerator-preservation assertion in the outer-prime proof. -/
theorem polynomial_preserves_congruence {F : Type*} [Field F]
    (v : AddValuation F (WithTop ℚ)) (P : Polynomial F)
    (hP : CoeffLower v P 0) (x y : F) (e : ℚ)
    (hx : (0 : WithTop ℚ) ≤ v x) (hy : (0 : WithTop ℚ) ≤ v y)
    (hxy : (e : WithTop ℚ) ≤ v (x-y)) :
    (e : WithTop ℚ) ≤ v (P.eval x-P.eval y) := by
  rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum, Polynomial.sum, Polynomial.sum,
    ← Finset.sum_sub_distrib]
  apply v.map_le_sum
  intro n hn
  rw [← mul_sub, AddValuation.map_mul]
  simpa using add_le_add (hP n) (power_preserves_congruence v x y e hx hy hxy n)

/-- An arbitrary integral polynomial numerator preserves integrality of the
near-pole divided difference. The statement keeps the two source values
explicit so it applies to both coefficients of the affine pole functional. -/
theorem integral_numerator_divided_difference (p : ℕ) [Fact p.Prime]
    (P : Polynomial ℚ) (hP : CoeffLower (rationalPadicValuation p) P 0)
    (x y u w : ℚ)
    (hx : (0 : WithTop ℚ) ≤ rationalPadicValuation p x)
    (hy : (0 : WithTop ℚ) ≤ rationalPadicValuation p y)
    (hw : (0 : WithTop ℚ) ≤ rationalPadicValuation p w)
    (hxy : rationalPadicValuation p (x-y) = 1)
    (huw : (1 : WithTop ℚ) ≤ rationalPadicValuation p (u-w)) :
    (0 : WithTop ℚ) ≤ rationalPadicValuation p
      ((P.eval x*u-P.eval y*w)/(x-y)) := by
  have hcong : (1 : WithTop ℚ) ≤ rationalPadicValuation p (P.eval x-P.eval y) :=
    polynomial_preserves_congruence (rationalPadicValuation p) P hP x y 1 hx hy (by simpa only [WithTop.coe_one] using (le_of_eq hxy.symm))
  have hnum : (1 : WithTop ℚ) ≤ rationalPadicValuation p (P.eval x*u-P.eval y*w) := by
    have heq : P.eval x*u-P.eval y*w = P.eval x*(u-w)+(P.eval x-P.eval y)*w := by ring
    rw [heq]
    apply (rationalPadicValuation p).map_le_add
    · rw [AddValuation.map_mul]
      simpa using add_le_add
        (polynomial_eval_integral (rationalPadicValuation p) P hP x hx) huw
    · rw [AddValuation.map_mul]
      simpa using add_le_add hcong hw
  rw [div_eq_mul_inv, AddValuation.map_mul, rationalPadicValuation_inv_finite p (x-y) 1 hxy]
  have hcancel : (1 : WithTop ℚ) + ((-1 : ℚ) : WithTop ℚ) = 0 := by
    change (↑((1 : ℚ) + (-1 : ℚ)) : WithTop ℚ) = 0
    norm_num
  have hh := add_le_add hnum (le_refl ((-1 : ℚ) : WithTop ℚ))
  rw [hcancel] at hh
  exact hh

/-- Each simple-pole constant below `p` is integral. -/
theorem localPoleConstant_integral_below (p j : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (hj : 0 < j) (hjp : j < p) :
    (0 : WithTop ℚ) ≤ rationalPadicValuation p (localPoleConstant j) := by
  have hjv := rationalPadicValuation_unit_below p j hj hjp
  have hfirst : (0 : WithTop ℚ) ≤ rationalPadicValuation p
      (-(j : ℚ)^4*fifthHarmonic j) := by
    rw [AddValuation.map_mul, AddValuation.map_neg, AddValuation.map_pow, hjv]
    simpa using fifthHarmonic_integral_below p j hjp
  have hfour : rationalPadicValuation p (4 : ℚ) = 0 :=
    rationalPadicValuation_unit_below p 4 (by omega) (by omega)
  have hquarter : rationalPadicValuation p (1/4 : ℚ) = 0 := by
    simpa only [one_div] using rationalPadicValuation_inv_unit p 4 hfour
  have htwo : rationalPadicValuation p (2 : ℚ) = 0 :=
    rationalPadicValuation_unit_below p 2 (by omega) (by omega)
  have hlast : rationalPadicValuation p (1/(2*(j : ℚ))) = 0 := by
    rw [one_div]
    apply rationalPadicValuation_inv_unit p (2*(j : ℚ))
    rw [AddValuation.map_mul, htwo, hjv, add_zero]
  unfold localPoleConstant
  apply (rationalPadicValuation p).map_le_add
  · exact (rationalPadicValuation p).map_le_sub hfirst (by rw [hquarter])
  · rw [hlast]

/-- The paired near-pole contribution with any integral polynomial numerator:
constant coefficient, including harmonic values. -/
theorem ordinary_pair_numerator_constant_integral (p a : ℕ) [Fact p.Prime]
    (P : Polynomial ℚ) (hP : CoeffLower (rationalPadicValuation p) P 0)
    (hp : 5 ≤ p) (ha : 0 < a) (hap : 2*a < p) :
    (0 : WithTop ℚ) ≤ rationalPadicValuation p
      ((P.eval (-(a : ℚ)^2)*localPoleConstant a -
          P.eval (-(((p-a : ℕ) : ℚ)^2))*localPoleConstant (p-a)) /
        (-(a : ℚ)^2 - (-(((p-a : ℕ) : ℚ)^2)))) := by
  apply integral_numerator_divided_difference p P hP
  · rw [AddValuation.map_neg, AddValuation.map_pow, rationalPadicValuation_unit_below p a ha (by omega)]
    simp
  · rw [AddValuation.map_neg, AddValuation.map_pow, rationalPadicValuation_unit_below p (p-a) (by omega) (by omega)]
    simp
  · exact localPoleConstant_integral_below p (p-a) hp (by omega) (by omega)
  · have heq : -(a : ℚ)^2 - (-(((p-a : ℕ) : ℚ)^2)) =
        -((a : ℚ)^2 - (((p-a : ℕ) : ℚ)^2)) := by ring
    rw [heq, AddValuation.map_neg]
    exact reflected_square_difference_valuation p a ha hap
  · rw [(rationalPadicValuation p).map_sub_swap]
    exact localPoleConstant_reflection p a (by omega) ha hap

/-- The same paired contribution's coefficient of `X`. -/
theorem ordinary_pair_numerator_linear_integral (p a : ℕ) [Fact p.Prime]
    (P : Polynomial ℚ) (hP : CoeffLower (rationalPadicValuation p) P 0)
    (ha : 0 < a) (hap : 2*a < p) :
    (0 : WithTop ℚ) ≤ rationalPadicValuation p
      ((P.eval (-(a : ℚ)^2)*(a : ℚ)^4 -
          P.eval (-(((p-a : ℕ) : ℚ)^2))*(((p-a : ℕ) : ℚ)^4)) /
        (-(a : ℚ)^2 - (-(((p-a : ℕ) : ℚ)^2)))) := by
  apply integral_numerator_divided_difference p P hP
  · rw [AddValuation.map_neg, AddValuation.map_pow, rationalPadicValuation_unit_below p a ha (by omega)]
    simp
  · rw [AddValuation.map_neg, AddValuation.map_pow, rationalPadicValuation_unit_below p (p-a) (by omega) (by omega)]
    simp
  · rw [AddValuation.map_pow, rationalPadicValuation_unit_below p (p-a) (by omega) (by omega)]
    simp
  · have heq : -(a : ℚ)^2 - (-(((p-a : ℕ) : ℚ)^2)) =
        -((a : ℚ)^2 - (((p-a : ℕ) : ℚ)^2)) := by ring
    rw [heq, AddValuation.map_neg]
    exact reflected_square_difference_valuation p a ha hap
  · exact reflected_fourth_powers p a (by omega)

end OrdinaryPoleCongruence

/-- Twice the ordinary-class row weight in equation (4.12). -/
def twiceOuterWeight (ell delta i : ℕ) : ℤ :=
  if i < ell-2 then min 0 (2*(i : ℤ)+6*(delta : ℤ)-(ell : ℤ)-4) else 0

def outerClassCost (ell delta : ℕ) : ℤ :=
  -(∑ i ∈ range (ell-delta), twiceOuterWeight ell delta i)

def outerClassZeros (ell delta : ℕ) : ℕ :=
  ((range (ell-delta)).filter fun i => twiceOuterWeight ell delta i = 0).card

theorem twiceOuterWeight_nonpos (ell delta i : ℕ) : twiceOuterWeight ell delta i ≤ 0 := by
  unfold twiceOuterWeight
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

/-- The exact removed-class cost and zero-weight count table in Section 4.2. -/
theorem removed_outer_class_table (ell : ℕ) (hlo : 2 ≤ ell) (hhi : ell ≤ 6) :
    (outerClassCost ell 1, outerClassZeros ell 1) =
      match ell with
      | 2 => ((0 : ℤ), 1)
      | 3 => ((1 : ℤ), 1)
      | 4 => ((2 : ℤ), 2)
      | 5 => ((4 : ℤ), 2)
      | 6 => ((6 : ℤ), 3)
      | _ => ((0 : ℤ), 0) := by
  interval_cases ell <;> decide +revert

/-- Unremoved ordinary classes have cost `7(ell-2)` and two zero weights. -/
theorem unremoved_outer_class_table (ell : ℕ) (hlo : 2 ≤ ell) (hhi : ell ≤ 6) :
    outerClassCost ell 0 = 7*((ell : ℤ)-2) ∧ outerClassZeros ell 0 = 2 := by
  interval_cases ell <;> decide +revert

#print axioms det_integral_rank_correction
#print axioms polynomial_det_integral_rank_correction
#print axioms rational_polynomial_det_padic_correction
#print axioms correction_rank_bound
#print axioms ordinary_pair_numerator_constant_integral
#print axioms ordinary_pair_numerator_linear_integral

end Zeta5Outer
