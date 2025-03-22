variable (p q r : Prop)

#check Classical.em
#check Classical.not_not -- double negation elimination
#check Classical.byContradiction

#check Classical.not_and_iff_or_not_not

-- this is a building block in the following proofs
theorem specialize_not : ¬p → (p → q) :=
  λ hnp hp => (hnp hp).elim

-- the "relationship" between an implication and an or
theorem imp_to_or : (p → q) → q ∨ ¬p :=
  (Classical.em p).imp_left

theorem not_and_imp_or_not_not {p q} : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro hnpq
  have hem : p ∨ ¬p := Classical.em p
  rw [Or.comm] at hem

  have hpnq : p → ¬q := λ hp =>
    Classical.byContradiction λ hnnq => by
      have hq := Classical.not_not.mp hnnq
      apply hnpq ⟨ hp, hq ⟩

  exact hem.imp_right hpnq

-- the better way mentioned in the video. same proof as above, but using
-- suffices and skipping a redundant byContradiction:
example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro hnpq
  have hem : p ∨ ¬p := Classical.em p
  rw [Or.comm] at hem
  -- show we just need a mapping from ¬p ∨ p to ¬p ∨ ¬q
  suffices hpnq : p → ¬q from hem.imp_right hpnq
  -- prove p → ¬q by giving a function from p to q to false
  exact λ hp hq => hnpq ⟨ hp, hq ⟩

-- using pattern matching instead of rewriting on an or
example : ¬(p ∧ q) → ¬p ∨ ¬q := λ hnpq =>
  match Classical.em p with
  | Or.inl hp => Or.inr λ hq => hnpq ⟨ hp, hq ⟩
  | Or.inr hnp => Or.inl hnp

theorem or_not_not_imp_not_and {p q} : ¬p ∨ ¬q → ¬(p ∧ q) := by
  rintro (hnp | hnq)
  · exact λ hpq => hnp hpq.left
  · exact λ hpq => hnq hpq.right

theorem not_and_iff_or_not_not {p q} : ¬(p ∧ q) ↔ ¬p ∨ ¬q :=
  ⟨ not_and_imp_or_not_not, or_not_not_imp_not_and ⟩

#check Classical.not_imp

theorem not_imp_and {p q} : ¬(p → q) → p ∧ ¬q := by
  intro hnpq
  obtain (hp | hnp) := Classical.em p
  ·
    suffices hnq : ¬q from And.intro hp hnq
    exact λ hq => hnpq (λ _ => hq)
  ·
    have hpq : p → q := λ hp => (hnp hp).elim
    exact (hnpq hpq).elim


theorem and_imp_not {p q} : p ∧ ¬q → ¬(p → q) := by
  rintro ⟨ hp, hnq ⟩
  exact λ hpq => hnq (hpq hp)
