example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  ⟨
    λ hnpq => ⟨ hnpq ∘ Or.inl, hnpq ∘ Or.inr ⟩,
    λ ⟨ hnp, hnq ⟩ => λ hpq => Or.elim hpq hnp hnq,
  ⟩

example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  rintro (hnp | hnq)
  · -- Using the predefined function `left`
    exact hnp ∘ And.left
  · -- Just using pattern matching
    rintro ⟨ _, hq ⟩
    exact hnq hq

example : ¬(p ∧ ¬p) := λ ⟨ hp, hnp ⟩ => hnp hp

example : p ∧ ¬q → ¬(p → q) := λ ⟨ hp, hnq ⟩ =>
  λ hpq => hnq (hpq hp)

example : ¬p → (p → q) := (False.elim ∘ ·)

example : (¬p ∨ q) → (p → q) := λ hor hp =>
  match hor with
  | Or.inl hnp => (hnp hp).elim
  | Or.inr hq => hq

example : p ∨ False ↔ p := ⟨
  λ hp_or => hp_or.elim id False.elim,
  λ hp => show p ∨ False from Or.inl hp,
⟩

example : p ∧ False ↔ False := ⟨
  And.right,
  False.elim,
⟩
