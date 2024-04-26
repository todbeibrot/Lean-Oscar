import Mathlib

-- TODO this definition probably exists in Mathlib
def List.toSet : List α → Set α
 | [] => {}
 | [a] => {a}
 | a :: as => Set.insert a (List.toSet as)

lemma List.toSet_insert {a : α} {as : List α} : List.toSet (a :: as) = Set.insert a (List.toSet as) := by
  induction as
  · simp only [toSet]
    exact Set.toFinset_inj.mp rfl
  · rfl

-- TODO this could be added to Mathlib
@[simp] theorem Set.mem_insert_self {α : Type u_1} (a : α) (s : Set α) : a ∈ Set.insert a s := by
  left
  rfl

theorem List.toSet_mem {a : α} {l : List α} : a ∈ List.toSet l ↔ a ∈ l := by
  induction l with
   | nil => simp only [Set.mem_empty_iff_false, List.not_mem_nil, List.toSet]
   | cons x xs h =>
      by_cases hax : x = a
      · simp [List.toSet_insert, hax, h]
      · simp [List.toSet_insert, hax, h]
        constructor
        · intro h2
          right
          rw [← h]
          apply Set.mem_of_mem_insert_of_ne h2 (Ne.symm hax)
        · rintro (rfl | h4)
          · exact (hax rfl).elim
          · right
            rw [h]
            exact h4
