open Classical

-- Lean's can prove by actually computing (decide)
example : 2 + 3 = 5 := rfl

example {p q r : Prop} ( h₁ : p = q) (h₂ : q = r) : p = r := by
  subst h₁ -- rewrite q as p in h₂ to get h₂ : p = r
  subst h₂ -- rewrite r as p in ⊢ to get p = p
  rfl -- p = p

example {p q r : Prop} ( h₁ : p = q) (h₂ : q = r) : p = r := by
  rw [<- h₁] at h₂
  rw [h₂]


example {p q r : Prop} ( h₁ : p = q) (h₂ : q = r) : p = r := by
  subst h₁
  assumption -- use p = r to prove p = r directly


-- same proof doesn't work with eq. We could rewrite with Eq.to_iff and use the
-- previous proof or prove a contradiction:
example {p} : ¬(p = ¬p) := λ hn => by
  obtain (hp | hnp) := Classical.em p
  · have hnp := by
      rw [hn] at hp
      exact hp
    exact hnp hp
  · have hp := by
      rw [<- hn] at hnp
      exact hnp
    exact hnp hp

example {p} : ¬(p = ¬p) := λ hn =>
  match Classical.em p with
  | Or.inl hp => (hn ▸ hp) hp
  | Or.inr hnp => (hn ▸ hnp) hnp


-- same proof works for p → (p = p)
example : ∀ x : Nat, x = x := by
  intro x
  rfl -- handles x = x

example : ∀ x : Nat, x = x :=
  Eq.refl

example { x : Nat } : x = x :=
  Eq.refl x


-- exists / use
example : ∃ x, x < 3 := by
  exists 2

-- specific case
example (h : 1 < 3) : ∃ x, x < 3 :=
  Exists.intro 1 h

-- general case
example {x : Nat} (h : x < 3) : ∃ x, x < 3 :=
  Exists.intro x h

-- without an existing hypothesis
example : ∃ x, x < 3 := by
  apply Exists.intro 1
  trivial
  -- or with: simp only [Nat.reduceLT]
  -- or with: exact Nat.lt_of_sub_eq_succ rfl

example : ∃ x, x < 3 := by
  exact Exists.intro 1 (Nat.lt_of_sub_eq_succ rfl)

-- convert to exists
example : ¬∀ x, x < 3 := by
  -- change the goal to showing a counter-example
  rw [not_forall]
  -- give an example of a number that is not less than 3
  refine Exists.intro 3 ?_ -- same as: `apply Exists.intro 3`
  rw [Nat.not_lt] -- this step isn't actually necessary
  trivial -- 3 ≤ 3


-- review

-- the book's solution
example {p q} : ¬(p ∧ ¬q) → (p → q) :=
  fun h : ¬(p ∧ ¬q) =>
  fun hp : p =>
  show q from
    Or.elim (em q)
      (fun hq : q => hq)
      (fun hnq : ¬q => absurd (And.intro hp hnq) h)

-- finally, a real proof byContradiction
example {p q} : ¬(p ∧ ¬q) → (p → q) := by
  intro hn_and hp
  exact byContradiction λ hnq => hn_and ⟨ hp, hnq ⟩
