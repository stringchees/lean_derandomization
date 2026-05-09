import Mathlib

/-- **Method of conditional expectations — boolean variable step.**

    Interpret `f b` as the conditional expectation of the objective after fixing
    the next boolean variable `x_k` to `b`.  The current conditional expectation
    (before fixing `x_k`) equals `(f false + f true) / 2` — the average of the
    two branches.

    At least one choice `b ∈ {false, true}` yields a conditional expectation
    no worse than the current one. -/
theorem condexp_step_bool (f : Bool → ℚ) :
    ∃ b : Bool, (f false + f true) / 2 ≤ f b := by
  obtain ⟨b, -, hb⟩ :=
    (Finset.univ : Finset Bool).exists_max_image f ⟨false, Finset.mem_univ _⟩
  refine ⟨b, ?_⟩
  have hf : f false ≤ f b := hb false (Finset.mem_univ _)
  have ht : f true  ≤ f b := hb true  (Finset.mem_univ _)
  have h2 : (0 : ℚ) < 2 := by norm_num
  rw [div_le_iff₀ h2]
  linarith
