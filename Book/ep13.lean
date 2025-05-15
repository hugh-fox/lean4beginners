variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  constructor
  · rintro ⟨ x, p_or_q ⟩
    exact match p_or_q with
    | Or.inl hp => Or.inl ⟨ x, hp ⟩
    | Or.inr hq => Or.inr ⟨ x, hq ⟩
  · rintro (⟨ x, hp ⟩ | ⟨ x, hq ⟩)
    · exact ⟨ x, Or.inl hp ⟩
    · exact ⟨ x, Or.inr hq ⟩

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
  constructor
  · rintro ⟨ x, px ⟩
    intro fa
    specialize fa x
    exact show False from fa px
  · intro nfa
    apply Classical.byContradiction
    intro nex
    have fa : ∀ x : α, ¬ p x := by
      intro x px
      exact nex ⟨ x, px ⟩
    exact show False from nfa fa

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  constructor
  · intro nex x px
    exact nex ⟨ x, px ⟩
  · intro fa ⟨ x, px ⟩
    specialize fa x
    exact fa px

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
  constructor
  · intro nfa
    apply Classical.byContradiction
    intro nex
    have fa : ∀ x : α, p x := by
      intro x
      apply Classical.byContradiction
      intro npx
      exact nex ⟨ x, npx ⟩
    exact show False from nfa fa
  · rintro ⟨ x, npx ⟩ fa
    specialize fa x
    exact show False from npx fa

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by
  constructor
  · intro fa ⟨ x, px ⟩
    specialize fa x px
    assumption
  · intro ex_imp_r x px
    exact ex_imp_r ⟨ x, px ⟩

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by
  constructor
  · rintro ⟨ x, px ⟩ hr
    exact ⟨ x, px hr ⟩
  · rintro r_imp_ex
    apply Classical.byContradiction
    intro nex
    have hnr : ¬r := by
      intro hr
      obtain ⟨ x, px ⟩ := r_imp_ex hr
      exact nex ⟨ x, λ _ => px ⟩
    exact nex ⟨ a, False.elim ∘ hnr ⟩
