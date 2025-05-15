variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _x : α, r) → r := by
  rintro ⟨ hx, hr ⟩
  exact hr

example (a : α) : r → (∃ _x : α, r) := by
  intro hr
  exact Exists.intro a hr

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  constructor
  · rintro ⟨ hx, ⟨ px, hr ⟩ ⟩
    refine And.intro ?_ hr
    exact Exists.intro hx px
  -- More explicit version
  -- · intro h
  --   have (And.intro (Exists.intro hx px) hr) := h
  --   exact ⟨ hx, ⟨ px, hr ⟩ ⟩
  · rintro ⟨ ⟨ hx, px ⟩, hr ⟩
    exact ⟨ hx, ⟨ px, hr ⟩ ⟩

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
  constructor
  · rintro fa ⟨ x, px ⟩
    specialize fa x
    contradiction
  · intro nex a
    apply Classical.byContradiction
    intro np
    exact nex ⟨ a, np ⟩

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
    constructor
    · -- Pattern match the exists in the hypothesis
      rintro ⟨x, px⟩ fa
      exact px (fa x) -- note that `a` doesn't work here instead of x
    · intro fa
      -- The idea of this proof is to get a forall we can specialize with a.
      -- In order to do that, Classical is needed to rewrite an exists prop
      apply Classical.byContradiction
      intro nex
      -- The rest of this proof could be replaced by `simp_all`
      rw [not_exists] at nex
      have : r := by
        -- Proving the non-emptiness of a forall is essential proving existence
        have ne : Nonempty (∀ (x : α), p x) := by
          apply Nonempty.intro
          intro x
          -- Sometimes an intro (or equivalently a lambda) is required to enter
          -- an expression (for demonstration, as `simp [not_imp] at nex` also
          -- works. Or even better, specializing nex first):
          conv at nex => intro; rw [not_imp]
          specialize nex x
          exact nex.left
        rwa [forall_const] at fa
      -- Same idea, but with a instead of x. There is definitely a better way
      -- that combines these two specializations.
      specialize nex a
      rw [not_imp] at nex
      exact nex.right this

-- Example proof of `forall_const`
theorem my_forall_const (p q : Prop) [ne : Nonempty p] : (p → q) ↔ q := by
  constructor
  case mp =>
    intro p_imp_q
    obtain ⟨ val ⟩ := ne
    exact p_imp_q val
  -- a function that returns a function
  case mpr => exact λ q => λ  _ => q
  -- or just a function of two arguments
  -- case mpr => exact λ q  _ => q
