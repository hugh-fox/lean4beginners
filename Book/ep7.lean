
#check Classical.em
#check Classical.byContradiction
#check Classical.not_not -- double negation elimination
#check Classical.not_imp
#check Classical.and_or_imp

variable (p q r : Prop)

theorem imp_not_or {p q} : (p → q) → (¬p ∨ q) := by
  intro hpq
  have hp_or_hnp : p ∨ ¬p :=  Classical.em p
  exact match hp_or_hnp with
  | Or.inl hp => Or.inr (hpq hp)
  | Or.inr hnp => Or.inl hnp

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  intro hp_or
  cases imp_not_or hp_or
  case inl hnp => exact Or.inl λ hp => (hnp hp).elim
  case inr hq_or_hr =>
    cases hq_or_hr
    case inl hq => exact Or.inl (λ _ => hq)
    case inr hr => exact Or.inr (λ _ => hr)

-- A better way is to use Classical.and_or_imp instead of our imp_not_or
-- theorem:
example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  intro hp_or
  -- Like and, we can call `mpr` to get the left arrow of an iff, which can
  -- then be applied like a function:
  obtain ⟨ hp, hq ⟩ | hpr := Classical.and_or_imp.mpr hp_or
  · exact Or.inl (λ _ => hq)
  · exact Or.inr hpr


example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
example : ¬(p → q) → p ∧ ¬q := sorry

-- Using rintro
example : (p → q) → (¬p ∨ q) := by
  intro hpq
  obtain (hp | hnp) := Classical.em p
  · exact Or.inr (hpq hp)
  · exact Or.inl hnp

example : (¬q → ¬p) → (p → q) := sorry
example : p ∨ ¬p := sorry
example : (((p → q) → p) → p) := sorry

-- an example that requires classical reasoning
example (p q : Prop) : ¬(p ∧ ¬q) → (p → q) := by
  sorry
