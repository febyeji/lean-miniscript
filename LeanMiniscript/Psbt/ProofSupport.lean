import Init

namespace LeanMiniscript.Psbt

/-- A successful bind supplies a successful value to its continuation. -/
theorem bind_eq_ok {α β ε : Type} {first : Except ε α} {next : α → Except ε β}
    {value : β} :
    (first >>= next) = .ok value ↔ ∃ prior, first = .ok prior ∧ next prior = .ok value := by
  cases first <;> simp [bind, Except.bind]

/-- A successful conditional records the branch that returned its value. -/
theorem ite_eq_ok {α ε : Type} {condition : Prop} [Decidable condition]
    {yes no : Except ε α} {value : α} :
    (if condition then yes else no) = .ok value ↔
      (condition ∧ yes = .ok value) ∨ (¬condition ∧ no = .ok value) := by
  by_cases condition <;> simp [*]

/-- Successful monadic mapping preserves each indexed source/result pair. -/
theorem getElem?_of_mapM_ok {α β ε : Type} {f : α → Except ε β}
    {xs : List α} {ys : List β} (mapped : xs.mapM f = .ok ys)
    {index : Nat} {x : α} (found : xs[index]? = some x) :
    ∃ y, ys[index]? = some y ∧ f x = .ok y := by
  induction xs generalizing ys index with
  | nil => simp at found
  | cons head tail ih =>
      simp only [List.mapM_cons, bind, Except.bind] at mapped
      cases first : f head with
      | error error => simp [first] at mapped
      | ok value =>
          simp only [first] at mapped
          cases rest : tail.mapM f with
          | error error => simp [rest] at mapped
          | ok values =>
              simp only [rest, pure, Except.pure, Except.ok.injEq] at mapped
              subst ys
              cases index with
              | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found
                        subst x; exact ⟨value, rfl, first⟩
              | succ index => exact ih rest found

theorem length_of_mapM_ok {α β ε : Type} {f : α → Except ε β}
    {xs : List α} {ys : List β} (mapped : xs.mapM f = .ok ys) :
    ys.length = xs.length := by
  induction xs generalizing ys with
  | nil => cases mapped; rfl
  | cons head tail ih =>
    simp only [List.mapM_cons, bind, Except.bind] at mapped
    cases first : f head with
    | error error => simp [first] at mapped
    | ok value =>
      simp only [first] at mapped
      cases rest : tail.mapM f with
      | error error => simp [rest] at mapped
      | ok values =>
        simp only [rest, pure, Except.pure, Except.ok.injEq] at mapped
        subst ys
        simp [ih rest]

end LeanMiniscript.Psbt
