variable { p q : Prop }

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  let mp : ((p ∨ q) → r) → (p → r) ∧ (q → r) := λ hpqr =>
    -- alternative one-liner:
    -- And.intro (hpqr ∘ Or.inl) (hpqr ∘ Or.inr)
    ⟨
      λ hp => hpqr (Or.inl hp),
      λ hq => hpqr (Or.inr hq),
    ⟩
  let mpr : (p → r) ∧ (q → r) → ((p ∨ q) → r) := λ ⟨ hpr, hqr ⟩ =>
    λ hpq => Or.elim hpq hpr hqr
  ⟨ mp, mpr ⟩


example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  let mp : ¬(p ∨ q) → ¬p ∧ ¬q := λ hnpq => ⟨
    λ hp => hnpq (Or.inl hp),
    λ hq => hnpq (Or.inr hq),
  ⟩
  let mpr : ¬p ∧ ¬q → ¬(p ∨ q) := λ ⟨ hnp, hnq ⟩ =>
    λ hp_or_hq => match hp_or_hq with
      | Or.inl hp => hnp hp
      | Or.inr hq => hnq hq
  ⟨ mp, mpr ⟩

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  have mp : ((p ∨ q) → r) → (p → r) ∧ (q → r) := by
    intro or_to_r
    have left : p → r := by
      exact λ hp => or_to_r (Or.inl hp)
    have right : q → r := by
      exact λ hq => or_to_r (Or.inr hq)
    exact And.intro left right
  have mpr : (p → r) ∧ (q → r) → ((p ∨ q) → r) := by
    rintro ⟨ hpr, hqr ⟩
    exact λ p_or_q =>
      match p_or_q with
      | Or.inl hp => hpr hp
      | Or.inr hq => hqr hq

  exact Iff.intro mp mpr

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  have mp : ¬(p ∨ q) → ¬p ∧ ¬q := by
    intro hn_p_or_q
    have left : ¬p := λ hp =>
      hn_p_or_q (Or.inl hp)
    have right : ¬q := λ hq =>
      hn_p_or_q (Or.inr hq)
    exact And.intro left right

  have mpr : ¬p ∧ ¬q → ¬(p ∨ q) := by
    rintro ⟨ hnp, hnq ⟩
    exact λ p_or_q => match p_or_q with
    | Or.inl hp => hnp hp
    | Or.inr hq => hnq hq

  exact Iff.intro mp mpr
