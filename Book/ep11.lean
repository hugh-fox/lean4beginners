example (a b c d : Nat)
  (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) :
  a < d :=
  calc a
    _ = b     := exact?%
    _ < b + 1 := exact?%
    _ ≤ c + 1 := exact?%
    _ < d     := exact?%

-- How to apply equations to expressions
example (a b c : Nat) (h₁ : a = 2) (h₂ : b = 2) : a - b ≤ c := by
  calc a - b
    _ = 2 - b := by subst h₁; rfl
    _ = 2 - 2 := by subst h₂; rfl
    _ = 0 := by rfl
    _ ≤ c := by exact Nat.zero_le c

-- How to manipulate equations themselves. These examples are a little
-- contrived, because when using Mathlib almost all of them can be done with
-- `ring`, `linear_combination`, or `field_simp`.
example (a b c : Int)
  (h₁ : a + (3*b + c) = 3)
  (h₂ : b + c - 9 = a)
  (h₃ : c = b + 1)
    : b = 2 := by
  -- You might think of moving something to the other side of an equation as
  -- one step, but it is actually two: apply to both sides, then simplify.
  replace h₁ : a = 3 - (3*b + c) := by
    -- congrArg is the bread and butter for working with equations.
    -- This happens to be an example where exact/apply are slightly different
    have := by apply congrArg (· - (3*b + c)) h₁
    -- Simplify subtraction of the form: a - b + b
    -- This only works for Naturals if a ≥ b
    rw [Int.add_sub_cancel] at this
    exact this -- can be skipped if rwa is used above instead
  -- The above wasn't necessary, subst can use h₂ either way
  subst h₂ h₃
  simp [Int.add_sub_assoc] at h₁
  simp [Int.neg_add, <- Int.add_assoc, Int.sub_eq_add_neg] at h₁
  simp [<- Int.neg_mul] at h₁
  rw [<- Int.mul_neg_one b, Int.mul_comm] at h₁
  -- Algebra can be annoying to do manually in lean. As usual in programming,
  -- anything that can be implicit has at least one inscrutable error message.
  -- In this case, `failed to find b * -3 + b * -1` even though its quite
  -- literally there. This is because operators are actually functions that
  -- take their arguments based on precedence, from left to right. So there are
  -- implied parentheses around `3 + b * -3`, because the first `+` happens
  -- first.
  replace : b + b + -8 = 3 + -(b * 4) + -1 := by
    -- The intuitive approach doesn't work:
    --  rw [<- @Int.mul_add b (-3) (-1)] at h₁
    -- First we need to change the implied parens. Alternatively, we could use
    -- a surgical tool like `conv`, to apply `add_comm` at a specific location.
    -- However, the easiest way is to specify the arguments to add_comm:
    rw [Int.add_assoc 3] at h₁
    rw [<- @Int.mul_add b (-3) (-1)] at h₁
    simp [h₁]
  -- This proof would have been easier if we started with congrArg to group
  -- like terms, starting from each lhs so that associativity doesn't get in
  -- the way.
  sorry

variable (α : Type) (p q : α → Prop)

#check Exists.elim
example  -- basically the definition of elim
  {x}
  (h_ex : ∃ x : Nat, x = 0)
  (hf : ∀ y, y = 0 → x = 0) :
    x = 0 := by
  have := h_ex.elim hf



-- book's example
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
    (fun w =>
     fun hw : p w ∧ q w =>
     show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩)

-- my version
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x := by
  -- Pattern match the `Exists` constructor
  have (Exists.intro x ⟨ hp, hq ⟩) := h
  -- Create a new exists from the parts
  exact Exists.intro x ⟨ hq, hp ⟩

-- alternative with suffices
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x := by
  have ⟨ x, p_and_q ⟩ := h
  suffices q x ∧ p x by
    exact Exists.intro x this
  exact p_and_q.symm



def is_even (x : Nat) := ∃ y, x = 2 * y

-- book's example
example {a b : Nat } (h1 : is_even a) (h2 : is_even b) :
  is_even (a + b) :=
  Exists.elim h1 (fun w1 (hw1 : a = 2 * w1) =>
  Exists.elim h2 (fun w2 (hw2 : b = 2 * w2) =>
    Exists.intro (w1 + w2)
      (calc a + b
        _ = 2 * w1 + 2 * w2 := by rw [hw1, hw2]
        _ = 2 * (w1 + w2)   := by rw [Nat.mul_add])))

-- my version
example {a b : Nat } (h1 : is_even a) (h2 : is_even b) :
  is_even (a + b) := by
  -- Use pattern matching to elim h1 and h2
  -- These could also be more implicit, e.g. obtain ⟨ x, a_even ⟩ := h1
  have (Exists.intro x (a_even : a = 2 * x)) := h1
  have (Exists.intro y (b_even : b = 2 * y)) := h2
  -- Specialize `exists` in the goal to x + y
  exists x + y
  -- Finish with algebra
  calc a + b
    _ = 2 * x + 2 * y := by rw [a_even, b_even]
    _ = 2 * (x + y) := by rw [Nat.mul_add]
