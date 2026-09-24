import AppendixNumericBase

namespace Zeta5AppendixNumerics

noncomputable def lowerField (l r : ℝ) : ℝ :=
  if r ≤ 59205077/10000000000 then field r
  else if 59205079/10000000000 ≤ l then field l
  else vstar

noncomputable def cellBound (l r : ℝ) : ℝ :=
  2 * max (potential l) (potential r) - lowerField l r

def partitionCheck (a b : ℚ) : List (ℚ × ℚ) → Bool
  | [] => decide (a = b)
  | (l, r) :: cs => decide (a = l ∧ l < r) && partitionCheck r b cs

theorem partition_covers (a b : ℚ) (cs : List (ℚ × ℚ))
    (h : partitionCheck a b cs = true) (t : ℝ)
    (ht : (a : ℝ) < t ∧ t ≤ b) :
    ∃ c ∈ cs, (c.1 : ℝ) ≤ t ∧ t ≤ c.2 := by
  induction cs generalizing a with
  | nil =>
    have hab : a = b := by simpa [partitionCheck] using h
    subst b
    exact (not_lt_of_ge ht.2 ht.1).elim
  | cons c cs ih =>
    have hh : (a = c.1 ∧ c.1 < c.2) ∧ partitionCheck c.2 b cs = true := by
      simpa only [partitionCheck, Bool.and_eq_true, decide_eq_true_eq] using h
    by_cases hc : t ≤ c.2
    · refine ⟨c, List.mem_cons_self, ?_, hc⟩
      rw [← hh.1.1]
      exact ht.1.le
    · obtain ⟨d, hd, htd⟩ := ih c.2 hh.2 ⟨lt_of_not_ge hc, ht.2⟩
      exact ⟨d, List.mem_cons_of_mem c hd, htd⟩

end Zeta5AppendixNumerics
