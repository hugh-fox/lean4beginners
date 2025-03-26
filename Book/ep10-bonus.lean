-- This file contains some alternative proofs for ¬(p ≠ p)
open Classical
variable (p : Prop)

-- by distributing negation
theorem my_iff_not_self : ¬(p ↔ ¬p) := by
  rw [← eq_iff_iff] -- convert to eq
  rw [Lean.Grind.not_eq_prop]
  rw [Classical.not_not]

-- using false_of_not_eq_self
example : ¬(p ↔ ¬p) := by
  rw [← propext_iff] -- convert to eq
  apply Lean.Grind.false_of_not_eq_self ∘ Eq.symm

example : ¬(p ≠ p) :=
  Ne.irrefl -- another existing lemma

example : ¬(p ↔ ¬p) := by
  rw [<- eq_iff_iff] -- by converting to eq
  -- copied from the false_of_not_eq_self's implementation
  by_cases p <;> simp_all


-- by converting to iff and using an existing lemma
theorem not_eq_not : ¬(p = ¬p) := by
  rw [eq_iff_iff]
  exact iff_not_self

-- golfing
example : ¬(p ≠ p) :=
  (· rfl) -- p_p
