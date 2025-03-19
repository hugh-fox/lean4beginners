variable { p q : Prop }

theorem my_or_comm : p ∨ q -> q ∨ p :=
  λ p_or_q : p ∨ q =>
    match p_or_q with
    | Or.inl hp => Or.inr hp
    | Or.inr hq => Or.inl hq

theorem or_comm_tactic : p ∨ q -> q ∨ p := by
  rintro (p | q)
  · exact Or.inr p
  · exact Or.inl q

example : (p → False) → p → False := λ not_p p =>
  not_p p

example : ¬p → p → False := id
