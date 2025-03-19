variable { p q : Prop }

theorem t1 : p → q → p :=
  fun (hp : p) _ => hp

theorem t1_tactic : p → q → p := by
  intro hp _
  exact hp

theorem t2 : p → q → p ∧ q :=
  fun hp hq => ⟨ hp, hq ⟩

theorem t3 : p ∧ q → p :=
  fun hp_and_hq => hp_and_hq.left
