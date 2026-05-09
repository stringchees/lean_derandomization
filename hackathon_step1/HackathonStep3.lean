import Mathlib

/-!
# Hackathon Step 3 — Greedy Derandomization (Method of Conditional Expectations)

We prove that for any objective `f : (Fin n → Bool) → ℚ`, the greedy
algorithm — which at each step fixes the next variable to whichever value
gives the higher conditional expectation — produces a deterministic
assignment `x* : Fin n → Bool` satisfying `E[f] ≤ f x*`.
-/

noncomputable def finsetAvg' {α : Type*} (S : Finset α) (f : α → ℚ) : ℚ :=
  (∑ x ∈ S, f x) / S.card

/-! ## HackathonStep2 -/

/-- Fixing the best of {false, true} never decreases the conditional expectation. -/
theorem condexp_step_bool' (f : Bool → ℚ) :
    ∃ b : Bool, (f false + f true) / 2 ≤ f b := by
  obtain ⟨b, -, hb⟩ :=
    (Finset.univ : Finset Bool).exists_max_image f ⟨false, Finset.mem_univ _⟩
  have hf := hb false (Finset.mem_univ _)
  have ht := hb true  (Finset.mem_univ _)
  exact ⟨b, by linarith⟩

/-! ## Averaging decomposition -/

/-- The average of `f` over all `(n+1)`-bit strings equals the average of the
    two sub-averages obtained by fixing the leading bit to `false` or `true`.

    **Proof outline:** Decompose `Finset.univ` via the bijection
    `Fin.cons : Bool × (Fin n → Bool) ≃ Fin (n+1) → Bool`, giving
    `∑_{x} f x = ∑_{b : Bool} ∑_{r} f (Fin.cons b r)`.
    Since `|Fin n → Bool| = 2ⁿ` and `|Fin (n+1) → Bool| = 2·2ⁿ`, the
    factor of 2 in the denominator is exactly right. -/
lemma avg_split (n : ℕ) (f : (Fin (n + 1) → Bool) → ℚ) :
    finsetAvg' Finset.univ f =
      (finsetAvg' Finset.univ (fun r => f (Fin.cons false r)) +
       finsetAvg' Finset.univ (fun r => f (Fin.cons true  r))) / 2 := by
  simp only [finsetAvg', Finset.card_univ]
  have hcard : Fintype.card (Fin (n + 1) → Bool) = 2 * Fintype.card (Fin n → Bool) := by
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    ring
  have hsum : ∑ x : Fin (n + 1) → Bool, f x =
      (∑ r : Fin n → Bool, f (Fin.cons false r)) +
      (∑ r : Fin n → Bool, f (Fin.cons true r)) := by
    have h1 : ∑ x : Fin (n + 1) → Bool, f x =
        ∑ p : Bool × (Fin n → Bool), f (Fin.cons p.1 p.2) :=
      Fintype.sum_equiv (Fin.consEquiv (fun _ => Bool)).symm _ _
        (fun x => by simp [Fin.consEquiv, Fin.cons_self_tail])
    rw [h1, Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
  have hN : (Fintype.card (Fin n → Bool) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  rw [hsum, hcard]
  push_cast
  field_simp [hN]


/-! ## Main theorem -/

/-- **Greedy Derandomization (Method of Conditional Expectations).**

    For any `f : (Fin n → Bool) → ℚ`, the greedy algorithm produces a
    deterministic `x* : Fin n → Bool` with `E[f] ≤ f x*`.

    **Algorithm (implicit in the proof):**
    At step `k`, let `g : (Fin (n-k) → Bool) → ℚ` be the conditional
    expectation of `f` given the choices already made.  Pick the leading
    bit `b₀` that maximises `finsetAvg univ (g ∘ Fin.cons b₀)`, then
    recurse on the resulting slice.  After `n` steps every variable is
    fixed and the accumulated inequality chain gives `E[f] ≤ f x*`. -/
theorem greedy_derandomization (n : ℕ) (f : (Fin n → Bool) → ℚ) :
    ∃ x : Fin n → Bool, finsetAvg' Finset.univ f ≤ f x := by
  induction n with
  | zero =>
    -- `Fin 0 → Bool` is a singleton, so the average equals `f` at the unique point.
    refine ⟨Fin.elim0, le_of_eq ?_⟩
    simp only [finsetAvg', Finset.univ_unique, Finset.sum_singleton,
               Finset.card_singleton, Nat.cast_one, div_one]
    exact congr_arg f (Subsingleton.elim _ _)
  | succ n ih =>
    -- (1) Decompose E[f] as the average of sub-averages for each leading bit.
    have havg : finsetAvg' Finset.univ f =
        (finsetAvg' Finset.univ (fun r => f (Fin.cons false r)) +
         finsetAvg' Finset.univ (fun r => f (Fin.cons true  r))) / 2 :=
      avg_split n f
    -- (2) condexp_step_bool picks a leading bit b₀ whose sub-average ≥ E[f].
    obtain ⟨b₀, hb₀⟩ := condexp_step_bool'
      (fun b => finsetAvg' Finset.univ (fun r => f (Fin.cons b r)))
    -- `hb₀ : (avg_false + avg_true) / 2 ≤ finsetAvg univ (f (b₀, ·))`
    have hstep : finsetAvg' Finset.univ f ≤
        finsetAvg' Finset.univ (fun r => f (Fin.cons b₀ r)) := by
      rw [havg]; exact hb₀
    -- (3) IH applied to the slice f(b₀, ·) yields a tail x_rest.
    obtain ⟨x_rest, hx_rest⟩ := ih (fun r => f (Fin.cons b₀ r))
    -- (4) x* = Fin.cons b₀ x_rest satisfies E[f] ≤ f x*.
    exact ⟨Fin.cons b₀ x_rest, le_trans hstep hx_rest⟩
