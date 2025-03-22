open Classical

-- same proof doesn't work with eq. We could rewrite with Eq.to_iff and use the
-- previous proof or prove a contradiction:
example : ¬(p = ¬p) := λ hn => by
  obtain (hp | hnp) := Classical.em p
  · have hnp := by
      rw [hn] at hp
      exact hp
    exact hnp hp
  · have hp := by
      rw [<- hn] at hnp
      exact hnp
    exact hnp hp

example : ¬(p = ¬p) := λ hn =>
  match Classical.em p with
  | Or.inl hp => (hn ▸ hp) hp
  | Or.inr hnp => (hn ▸ hnp) hnp

-- an example that requires classical reasoning
example (p q : Prop) : ¬(p ∧ ¬q) → (p → q) :=
  fun h : ¬(p ∧ ¬q) =>
  fun hp : p =>
  show q from
    Or.elim (em q)
      (fun hq : q => hq)
      (fun hnq : ¬q => absurd (And.intro hp hnq) h)

example (p q : Prop) : ¬(p ∧ ¬q) → (p → q) := by
  sorry


---


-- exists / use
example : ∃ x, x < 3 := by
  sorry

-- specific case
example (h : 1 < 3) : ∃ x, x < 3 :=
  Exists.intro 1 h

-- general case
example (h : x < 3) : ∃ x, x < 3 :=
  Exists.intro x h

-- without an existing hypothesis
example : ∃ x, x < 3 :=
  sorry

-- same proof works for p → (p = p)
example : ∀ x : ℕ, x = x := by
  intro x
  rfl -- handles x = x

example : ∀ x : ℕ, x = x :=
  λ x => Eq.refl x

example { x : ℕ } : x = x :=
  Eq.refl x

-- convert to exists
example : ¬∀ x, x < 3 := by
  -- change the goal to showing a counter-example
  rw [not_forall]
  -- give an example of a number that is not less than 3
  refine Exists.intro 3 ?_ -- same as: `apply Exists.intro 3`
  rw [Nat.not_lt] -- this step isn't actually necessary
  trivial -- 3 ≤ 3
