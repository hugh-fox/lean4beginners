variable { p q : Prop }

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  have mp : (p ∧ q) ∧ r → p ∧ (q ∧ r) := by
    rintro ⟨ ⟨ p, q ⟩, r ⟩
    exact ⟨ p, ⟨ q, r ⟩ ⟩

  have mpr : p ∧ (q ∧ r) → (p ∧ q) ∧ r := by
      rintro ⟨ p, ⟨ q, r ⟩ ⟩
      exact ⟨ ⟨ p, q ⟩, r ⟩

  -- exact ⟨ mp, mpr ⟩
  exact Iff.intro mp mpr


example : p ∧ (q ∧ r) → (p ∧ q) ∧ r :=
  λ ⟨p, ⟨q, r⟩ ⟩ => ⟨ ⟨ p, q ⟩, r ⟩

---

example : p ∧ q → q ∧ p := λ h_and => match h_and with
  | And.intro p q => And.intro q p

example (p q r : Prop) :
  p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := Iff.intro
  (λ h_and => match h_and with
    | And.intro hp _ => sorry
    | And.intro hp _ => sorry
  )
  (λ h_or => match h_or with
    | Or.inl _ => sorry
    | Or.inr _ => sorry

  )
example (p q r : Prop) :
  p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  have mp : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
    rintro ⟨ p, (q | r) ⟩
    · have p_and_q := And.intro p q
      exact Or.inl p_and_q
    · have p_and_r := And.intro p r
      exact Or.inr p_and_r

  have mpr : (p ∧ q) ∨ (p ∧ r) → p ∧ (q ∨ r) := by
    rintro (⟨ p, q ⟩ | ⟨ p, r ⟩)
    · exact ⟨p, Or.inl q ⟩
    · exact ⟨ p, Or.inr r ⟩

  exact ⟨ mp, mpr ⟩
