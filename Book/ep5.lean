

theorem contrapositive : (p → q) → (¬q → ¬p) := by
  intro hpq hnq hp
  have hq := hpq hp
  exact hnq hq



example : (p → q) → p → q := id


example : (p → q) → (¬q → ¬p) :=
  flip (· ∘ ·) -- uh, what?

example : (p → q) → (q → False) → (p → False) := flip (· ∘ ·)

example : (q → False) → (p → q) → (p → False) := (· ∘ ·)
