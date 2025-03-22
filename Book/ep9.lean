variable (p q r : Prop)

-- Similar but not the same
#check Classical.or_iff_not_imp_left

theorem imp_or_not : (p → q) → (¬p ∨ q) := λ hpq => by
  obtain (hp | hnp) := Classical.em p
  · exact Or.inr (hpq hp)
  · exact Or.inl (hnp)

example : (¬q → ¬p) → (p → q) := by
  intro hnqnp
  obtain (hq | hnq) := Classical.em q
  · exact λ _ => hq
  · exact λ hp => by
      have hnp : ¬p := hnqnp hnq
      exact (hnp hp).elim

example : p ∨ ¬p := Classical.em p

example : ((p → q) → p) → p := by
  intro hpqp
  obtain (hp | hnp) := Classical.em p
  · exact hp
  ·
    have hpq : p → q := False.elim ∘ hnp
    exact hpqp hpq

-- do this example without Classical
example : ¬(p ↔ ¬p) := by
  rintro ⟨ hpnp : p → p → False, hnpp : (p → False) → p ⟩
  have hnp : p → False := λ hp => hpnp hp hp
  have hp := hnpp hnp
  exact hnp hp
