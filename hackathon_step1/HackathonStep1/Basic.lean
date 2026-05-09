import Mathlib

noncomputable def finsetAvg {a : Type*} (S : Finset a) (f : a → ℚ) : ℚ :=
  (∑ x ∈ S, f x) / S.card

/-- Finite averaging lemma: some element of S achieves at least the average value of f. -/
theorem exists_go_finsetAvg
    {a : Type*}
    (S : Finset a)
    (f : a → ℚ)
    (hS : S.Nonempty) :
    ∃ x ∈ S, finsetAvg S f ≤ f x := by
  obtain ⟨x, hx, hmax⟩ := S.exists_max_image f hS
  refine ⟨x, hx, ?_⟩
  simp only [finsetAvg]
  have hcard : (0 : ℚ) < S.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hS)
  rw [div_le_iff₀ hcard]
  have hle : ∑ y ∈ S, f y ≤ ∑ _y ∈ S, f x :=
    Finset.sum_le_sum fun y hy => hmax y hy
  have heq : ∑ _y ∈ S, f x = f x * ↑S.card := by
    simp [Finset.sum_const, mul_comm]
  linarith
