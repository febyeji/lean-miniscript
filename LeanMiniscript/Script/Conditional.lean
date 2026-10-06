import LeanMiniscript.Script.State
import LeanMiniscript.Script.ControlFlow

/-! Conditional splitting, branch selection and structural laws used by Script execution. -/

namespace LeanMiniscript.Script

/-- The top-level branch segments and suffix delimited by the matching
    `OP_ENDIF` for one leading `OP_IF` or `OP_NOTIF`.

    A list, rather than a then/else pair, matches Bitcoin Core's behavior of
    toggling the current execution flag at every same-depth `OP_ELSE`. -/
structure ConditionalFrame where
  branches : List Script
  after : Script
  deriving Repr

/-- Concatenate exactly the branch segments enabled by repeated `OP_ELSE`
    toggles, starting with `executeFirst` for the first segment. -/
def selectConditionalBranches : Bool → List Script → Script
  | _, [] => []
  | executeFirst, branch :: branches =>
      (if executeFirst then branch else []) ++
        selectConditionalBranches (!executeFirst) branches

/-- Script remaining after executing the selected branch segments and skipping
    to the matching `OP_ENDIF`. -/
def ConditionalFrame.select (frame : ConditionalFrame)
    (executeFirst : Bool) : Script :=
  selectConditionalBranches executeFirst frame.branches ++ frame.after

/-- Selecting alternating branches never contains more elements than all
    branch segments together. -/
private theorem selectConditionalBranches_length_le_sum
    (executeFirst : Bool) (branches : List Script) :
    (selectConditionalBranches executeFirst branches).length ≤
      (branches.map List.length).sum := by
  induction branches generalizing executeFirst with
  | nil => simp [selectConditionalBranches]
  | cons branch branches ih =>
      cases executeFirst with
      | false =>
          simp [selectConditionalBranches]
          have bound := ih true
          omega
      | true =>
          simp [selectConditionalBranches]
          have bound := ih false
          omega

/-- Number of source elements represented by a conditional scan state. -/
private def conditionalScanSize (currentRev : Script)
    (completedRev : List Script) (script : Script) : Nat :=
  currentRev.length + (completedRev.map List.length).sum + script.length

/-- Scan the tail of one conditional, tracking nested `IF`/`NOTIF` depth.
    Reversed accumulators preserve source order without repeated tail appends. -/
private def splitConditionalAux (depth : Nat) (currentRev : Script)
    (completedRev : List Script) : Script → Option ConditionalFrame
  | [] => none
  | element :: rest =>
      match element with
      | .op .OP_IF | .op .OP_NOTIF =>
          splitConditionalAux (depth + 1) (element :: currentRev) completedRev rest
      | .op .OP_ELSE =>
          match depth with
          | 0 =>
              splitConditionalAux 0 [] (currentRev.reverse :: completedRev) rest
          | _ + 1 =>
              splitConditionalAux depth (element :: currentRev) completedRev rest
      | .op .OP_ENDIF =>
          match depth with
          | 0 =>
              some
                { branches := (currentRev.reverse :: completedRev).reverse
                  after := rest }
          | nestedDepth + 1 =>
              splitConditionalAux nestedDepth (element :: currentRev)
                completedRev rest
      | _ => splitConditionalAux depth (element :: currentRev) completedRev rest

/-- Split the tail following a leading `OP_IF` or `OP_NOTIF` at its unique
    matching `OP_ENDIF`. Returns `none` when that delimiter is missing. -/
def splitConditional (script : Script) : Option ConditionalFrame :=
  splitConditionalAux 0 [] [] script

/-- Scanning a balanced script prefix cannot close or split the surrounding
    conditional. It only adds that prefix, in reverse order, to the current
    branch accumulator. -/
private theorem splitConditionalAux_balanced_prefix
    {body : Script} (balanced : BalancedControlFlow body)
    (depth : Nat) (currentRev : Script) (completedRev : List Script)
    (suffix : Script) :
    splitConditionalAux depth currentRev completedRev (body ++ suffix) =
      splitConditionalAux depth (body.reverse ++ currentRev) completedRev suffix := by
  induction balanced generalizing depth currentRev completedRev suffix with
  | nil => rfl
  | @atom element nonConditional =>
      cases element with
      | pushData data => simp [splitConditionalAux]
      | pushNum value => simp [splitConditionalAux]
      | op opcode =>
          cases opcode <;> simp_all [NonConditional, splitConditionalAux]
  | @append left right _ _ leftIH rightIH =>
      rw [List.append_assoc, leftIH, rightIH]
      simp [List.reverse_append, List.append_assoc]
  | @ifThen nested nestedBalanced nestedIH =>
      simp only [List.cons_append, List.nil_append, List.append_assoc,
        splitConditionalAux]
      rw [nestedIH]
      simp only [splitConditionalAux]
      simp [List.reverse_append, List.append_assoc]
  | @notifThen nested nestedBalanced nestedIH =>
      simp only [List.cons_append, List.nil_append, List.append_assoc,
        splitConditionalAux]
      rw [nestedIH]
      simp only [splitConditionalAux]
      simp [List.reverse_append, List.append_assoc]
  | @ifElse thenBranch elseBranch thenBalanced elseBalanced thenIH elseIH =>
      simp only [List.cons_append, List.nil_append, List.append_assoc,
        splitConditionalAux]
      rw [thenIH]
      simp only [splitConditionalAux]
      rw [elseIH]
      simp only [splitConditionalAux]
      simp [List.reverse_append, List.append_assoc]
  | @notifElse thenBranch elseBranch thenBalanced elseBalanced thenIH elseIH =>
      simp only [List.cons_append, List.nil_append, List.append_assoc,
        splitConditionalAux]
      rw [thenIH]
      simp only [splitConditionalAux]
      rw [elseIH]
      simp only [splitConditionalAux]
      simp [List.reverse_append, List.append_assoc]

/-- A balanced body followed by `OP_ENDIF` is split as one branch, with the
    remainder returned unchanged as the conditional suffix. -/
theorem splitConditional_balanced_ifThen
    {body suffix : Script} (balanced : BalancedControlFlow body) :
    splitConditional (body ++ [.op .OP_ENDIF] ++ suffix) =
      some { branches := [body], after := suffix } := by
  unfold splitConditional
  simp only [List.append_assoc, List.singleton_append]
  rw [splitConditionalAux_balanced_prefix balanced]
  simp [splitConditionalAux]

/-- Two balanced branches separated by `OP_ELSE` and closed by `OP_ENDIF`
    produce exactly those branches and leave the following suffix untouched. -/
theorem splitConditional_balanced_ifElse
    {thenBranch elseBranch suffix : Script}
    (thenBalanced : BalancedControlFlow thenBranch)
    (elseBalanced : BalancedControlFlow elseBranch) :
    splitConditional
        (thenBranch ++ [.op .OP_ELSE] ++ elseBranch ++
          [.op .OP_ENDIF] ++ suffix) =
      some { branches := [thenBranch, elseBranch], after := suffix } := by
  unfold splitConditional
  simp only [List.append_assoc, List.singleton_append]
  rw [splitConditionalAux_balanced_prefix thenBalanced]
  have splitElse :
      splitConditionalAux 0 (thenBranch.reverse ++ []) []
          (.op .OP_ELSE :: elseBranch ++ .op .OP_ENDIF :: suffix) =
        splitConditionalAux 0 [] [thenBranch]
          (elseBranch ++ .op .OP_ENDIF :: suffix) := by
    simp [splitConditionalAux]
  rw [splitElse]
  rw [splitConditionalAux_balanced_prefix elseBalanced]
  simp [splitConditionalAux]

/-- Proof-facing, source-order projection of one open conditional. Nested
    delimiters are retained in selected segments; same-depth ELSE toggles the
    selection, and the matching ENDIF returns the untouched suffix. -/
def selectConditionalTail (depth : Nat) (selected : Bool) : Script → Option Script
  | [] => none
  | element :: rest =>
      let keep := fun tail => if selected then element :: tail else tail
      match element with
      | .op .OP_IF | .op .OP_NOTIF =>
          (selectConditionalTail (depth + 1) selected rest).map keep
      | .op .OP_ELSE =>
          match depth with
          | 0 => selectConditionalTail 0 (!selected) rest
          | _ + 1 => (selectConditionalTail depth selected rest).map keep
      | .op .OP_ENDIF =>
          match depth with
          | 0 => some rest
          | nested + 1 => (selectConditionalTail nested selected rest).map keep
      | _ => (selectConditionalTail depth selected rest).map keep

private def advanceChoice : Nat → Bool → Bool
  | 0, selected => selected
  | count + 1, selected => !(advanceChoice count selected)

private theorem advanceChoice_not (count : Nat) (selected : Bool) :
    advanceChoice count (!selected) = !(advanceChoice count selected) := by
  induction count with
  | zero => rfl
  | succ count ih => simp [advanceChoice, ih]

private theorem selectConditionalBranches_append (selected : Bool)
    (left right : List Script) :
    selectConditionalBranches selected (left ++ right) =
      selectConditionalBranches selected left ++
        selectConditionalBranches (advanceChoice left.length selected) right := by
  induction left generalizing selected with
  | nil => simp [selectConditionalBranches, advanceChoice]
  | cons branch rest ih =>
      simp [selectConditionalBranches, ih, advanceChoice, advanceChoice_not,
        List.append_assoc]

private theorem splitConditionalAux_select
    (script : Script) (depth : Nat) (currentRev : Script)
    (completedRev : List Script) (selected : Bool) :
    (splitConditionalAux depth currentRev completedRev script).map
        (fun frame => frame.select selected) =
      (selectConditionalTail depth (advanceChoice completedRev.length selected) script).map
        (fun tail => selectConditionalBranches selected completedRev.reverse ++
          (if advanceChoice completedRev.length selected then currentRev.reverse else []) ++ tail) := by
  induction script generalizing depth currentRev completedRev selected with
  | nil => simp [splitConditionalAux, selectConditionalTail]
  | cons element rest ih =>
      cases element with
      | pushData data | pushNum data =>
          simp only [splitConditionalAux, selectConditionalTail, ih, Option.map_map,
            List.reverse_cons]
          congr 1
          funext tail
          split <;> simp [List.append_assoc]
      | op opcode =>
          cases opcode <;> cases depth <;>
            simp only [splitConditionalAux, selectConditionalTail, ih, Option.map_map,
              List.reverse_cons]
          all_goals try simp [ConditionalFrame.select, selectConditionalBranches_append,
            selectConditionalBranches, advanceChoice, List.append_assoc]
          all_goals
            congr 1
            funext tail
            split <;> simp [List.append_assoc]

/-- The source-order projection is exactly the existing branch-frame selection,
    including arbitrarily nested conditionals and repeated ELSE segments. -/
theorem selectConditionalTail_eq (script : Script) (selected : Bool) :
    selectConditionalTail 0 selected script =
      (splitConditional script).map (fun frame => frame.select selected) := by
  simpa [splitConditional, advanceChoice, selectConditionalBranches] using
    (splitConditionalAux_select script 0 [] [] selected).symm

/-- Collect same-depth branch segments when a leading conditional has no
    matching `OP_ENDIF`. Nested delimiters remain inside their branch so that
    an active nested conditional is evaluated normally. -/
private def splitUnclosedConditionalAux (depth : Nat) (currentRev : Script)
    (completedRev : List Script) : Script → List Script
  | [] => (currentRev.reverse :: completedRev).reverse
  | element :: rest =>
      match element with
      | .op .OP_IF | .op .OP_NOTIF =>
          splitUnclosedConditionalAux (depth + 1) (element :: currentRev)
            completedRev rest
      | .op .OP_ELSE =>
          match depth with
          | 0 =>
              splitUnclosedConditionalAux 0 []
                (currentRev.reverse :: completedRev) rest
          | _ + 1 =>
              splitUnclosedConditionalAux depth (element :: currentRev)
                completedRev rest
      | .op .OP_ENDIF =>
          match depth with
          | 0 => (currentRev.reverse :: completedRev).reverse
          | nestedDepth + 1 =>
              splitUnclosedConditionalAux nestedDepth (element :: currentRev)
                completedRev rest
      | _ =>
          splitUnclosedConditionalAux depth (element :: currentRev)
            completedRev rest

/-- Active branch code that Bitcoin Core executes before reporting a missing
    outer `OP_ENDIF`. Repeated same-depth ELSE segments alternate as usual. -/
def selectUnclosedConditional (script : Script) (executeFirst : Bool) : Script :=
  selectConditionalBranches executeFirst
    (splitUnclosedConditionalAux 0 [] [] script)

/-- A runtime failure inside an active unclosed branch takes precedence over
    the structural error reported after successful execution reaches EOF. -/
def finishUnclosedConditional : ExecResult → ExecResult
  | .failure error => .failure error
  | .success _ _ => .failure .unbalancedConditional

/-- The unclosed-branch projection only removes source elements. -/
private theorem splitUnclosedConditionalAux_length_le
    (depth : Nat) (currentRev : Script) (completedRev : List Script)
    (script : Script) :
    ((splitUnclosedConditionalAux depth currentRev completedRev script).map
      List.length).sum ≤ conditionalScanSize currentRev completedRev script := by
  induction script generalizing depth currentRev completedRev with
  | nil =>
      simp [splitUnclosedConditionalAux, conditionalScanSize, Nat.add_comm]
  | cons element rest ih =>
      cases element with
      | pushData data =>
          have bound := ih depth (.pushData data :: currentRev) completedRev
          simpa [splitUnclosedConditionalAux, conditionalScanSize,
            Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using bound
      | pushNum value =>
          have bound := ih depth (.pushNum value :: currentRev) completedRev
          simpa [splitUnclosedConditionalAux, conditionalScanSize,
            Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using bound
      | op opcode =>
          cases depth <;> cases opcode <;>
            simp only [splitUnclosedConditionalAux]
          all_goals
            try
              apply Nat.le_trans (ih _ _ _)
              simp [conditionalScanSize, Nat.add_assoc, Nat.add_left_comm,
                Nat.add_comm]
          all_goals
            simp [conditionalScanSize, Nat.add_assoc, Nat.add_left_comm,
              Nat.add_comm]
            omega

/-- Selecting active segments from an unclosed conditional is no longer than
    its original tail. -/
theorem selectUnclosedConditional_length_le (script : Script)
    (executeFirst : Bool) :
    (selectUnclosedConditional script executeFirst).length ≤ script.length := by
  have selected := selectConditionalBranches_length_le_sum executeFirst
    (splitUnclosedConditionalAux 0 [] [] script)
  have scanned := splitUnclosedConditionalAux_length_le 0 [] [] script
  exact Nat.le_trans selected (by simpa [conditionalScanSize] using scanned)

/-- A successful split selects a script strictly smaller than the scan state
    that still contains its matching `OP_ENDIF`. -/
private theorem splitConditionalAux_select_length_lt
    (depth : Nat) (currentRev : Script) (completedRev : List Script)
    (script : Script) (frame : ConditionalFrame) (executeFirst : Bool)
    (hSplit : splitConditionalAux depth currentRev completedRev script =
      some frame) :
    (frame.select executeFirst).length <
      conditionalScanSize currentRev completedRev script := by
  induction script generalizing depth currentRev completedRev frame executeFirst with
  | nil => simp [splitConditionalAux] at hSplit
  | cons element rest ih =>
      cases element with
      | pushData data =>
          simp only [splitConditionalAux] at hSplit
          have smaller := ih depth (.pushData data :: currentRev) completedRev
            frame executeFirst hSplit
          simpa [conditionalScanSize, Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm] using smaller
      | pushNum value =>
          simp only [splitConditionalAux] at hSplit
          have smaller := ih depth (.pushNum value :: currentRev) completedRev
            frame executeFirst hSplit
          simpa [conditionalScanSize, Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm] using smaller
      | op opcode =>
          cases depth <;> cases opcode <;>
            simp only [splitConditionalAux] at hSplit
          all_goals
            try simp only [Nat.zero_add] at hSplit
            try
              exact Nat.lt_of_lt_of_le (ih _ _ _ _ _ hSplit) (by
                simp [conditionalScanSize, Nat.add_assoc, Nat.add_left_comm,
                  Nat.add_comm])
          cases hSplit
          simp only [ConditionalFrame.select, List.length_append,
            conditionalScanSize, List.length_cons]
          have selected := selectConditionalBranches_length_le_sum
            executeFirst ((currentRev.reverse :: completedRev).reverse)
          have allBranches :
              ((((currentRev.reverse :: completedRev).reverse).map
                List.length).sum) =
                currentRev.length + (completedRev.map List.length).sum := by
            simp [Nat.add_comm]
          rw [allBranches] at selected
          omega

/-- A selected branch execution is shorter than the original conditional tail,
    which still contains the matching `OP_ENDIF`. -/
theorem ConditionalFrame.select_length_lt
    {script : Script} {frame : ConditionalFrame}
    (hSplit : splitConditional script = some frame) (executeFirst : Bool) :
    (frame.select executeFirst).length < script.length := by
  have smaller := splitConditionalAux_select_length_lt
    0 [] [] script frame executeFirst hSplit
  simpa [conditionalScanSize] using smaller

/-- The executable splitter cannot assign two different frames to one tail. -/
theorem splitConditional_unique {script : Script} {first second : ConditionalFrame}
    (hFirst : splitConditional script = some first)
    (hSecond : splitConditional script = some second) :
    first = second := by
  rw [hFirst] at hSecond
  cases hSecond
  rfl

/-- Map instructions within each branch and the suffix, retaining branch boundaries. -/
def ConditionalFrame.map (f : ScriptElement → ScriptElement)
    (frame : ConditionalFrame) : ConditionalFrame :=
  { branches := frame.branches.map (List.map f), after := frame.after.map f }

theorem selectConditionalBranches_map (f : ScriptElement → ScriptElement)
    (branches : List Script) (selected : Bool) :
    selectConditionalBranches selected (branches.map (List.map f)) =
      (selectConditionalBranches selected branches).map f := by
  induction branches generalizing selected with
  | nil => rfl
  | cons branch rest ih =>
      cases selected <;> simp [selectConditionalBranches, ih]

theorem ConditionalFrame.select_map (f : ScriptElement → ScriptElement)
    (frame : ConditionalFrame) (selected : Bool) :
    (frame.map f).select selected = (frame.select selected).map f := by
  simp [ConditionalFrame.map, ConditionalFrame.select, selectConditionalBranches_map]

private theorem splitConditionalAux_cons_nonConditional
    (element : ScriptElement) (ordinary : NonConditional element)
    (depth : Nat) (current : Script) (completed : List Script) (rest : Script) :
    splitConditionalAux depth current completed (element :: rest) =
      splitConditionalAux depth (element :: current) completed rest := by
  cases element with
  | pushData | pushNum => rfl
  | op opcode => cases opcode <;> simp_all [NonConditional, splitConditionalAux]

private theorem splitConditionalAux_map (f : ScriptElement → ScriptElement)
    (preserves : ∀ element, f element = element ∨
      (NonConditional element ∧ NonConditional (f element)))
    (script : Script) (depth : Nat) (current : Script) (completed : List Script) :
    splitConditionalAux depth (current.map f) (completed.map (List.map f))
        (script.map f) =
      (splitConditionalAux depth current completed script).map (ConditionalFrame.map f) := by
  induction script generalizing depth current completed with
  | nil => rfl
  | cons element rest ih =>
      rcases preserves element with unchanged | ⟨ordinary, mappedOrdinary⟩
      · cases element with
        | pushData | pushNum => simp [List.map_cons, unchanged, splitConditionalAux, ← ih]
        | op opcode =>
            cases opcode <;> cases depth <;>
              simp [List.map_cons, unchanged, splitConditionalAux, ← ih,
                ConditionalFrame.map, List.map_reverse]
      · simp only [List.map_cons,
          splitConditionalAux_cons_nonConditional _ ordinary,
          splitConditionalAux_cons_nonConditional _ mappedOrdinary, ← ih]

/-- Changing ordinary instructions preserves conditional parsing when every
    conditional delimiter remains unchanged. -/
theorem splitConditional_map (f : ScriptElement → ScriptElement)
    (preserves : ∀ element, f element = element ∨
      (NonConditional element ∧ NonConditional (f element))) (script : Script) :
    splitConditional (script.map f) =
      (splitConditional script).map (ConditionalFrame.map f) := by
  exact splitConditionalAux_map f preserves script 0 [] []

private theorem splitUnclosedConditionalAux_cons_nonConditional
    (element : ScriptElement) (ordinary : NonConditional element)
    (depth : Nat) (current : Script) (completed : List Script) (rest : Script) :
    splitUnclosedConditionalAux depth current completed (element :: rest) =
      splitUnclosedConditionalAux depth (element :: current) completed rest := by
  cases element with
  | pushData | pushNum => rfl
  | op opcode => cases opcode <;> simp_all [NonConditional, splitUnclosedConditionalAux]

private theorem splitUnclosedConditionalAux_map (f : ScriptElement → ScriptElement)
    (preserves : ∀ element, f element = element ∨
      (NonConditional element ∧ NonConditional (f element)))
    (script : Script) (depth : Nat) (current : Script) (completed : List Script) :
    splitUnclosedConditionalAux depth (current.map f) (completed.map (List.map f))
        (script.map f) =
      (splitUnclosedConditionalAux depth current completed script).map (List.map f) := by
  induction script generalizing depth current completed with
  | nil => simp [splitUnclosedConditionalAux, List.map_reverse]
  | cons element rest ih =>
      rcases preserves element with unchanged | ⟨ordinary, mappedOrdinary⟩
      · cases element with
        | pushData | pushNum =>
            simp [List.map_cons, unchanged, splitUnclosedConditionalAux, ← ih]
        | op opcode =>
            cases opcode <;> cases depth <;>
              simp [List.map_cons, unchanged, splitUnclosedConditionalAux, ← ih,
                List.map_reverse]
      · simp only [List.map_cons,
          splitUnclosedConditionalAux_cons_nonConditional _ ordinary,
          splitUnclosedConditionalAux_cons_nonConditional _ mappedOrdinary, ← ih]

theorem selectUnclosedConditional_map (f : ScriptElement → ScriptElement)
    (preserves : ∀ element, f element = element ∨
      (NonConditional element ∧ NonConditional (f element)))
    (script : Script) (selected : Bool) :
    selectUnclosedConditional (script.map f) selected =
      (selectUnclosedConditional script selected).map f := by
  unfold selectUnclosedConditional
  have mapped := splitUnclosedConditionalAux_map f preserves script 0 [] []
  simp only [List.map_nil] at mapped
  rw [mapped, selectConditionalBranches_map]

/-- Once a conditional tail has been split, appending code changes only the
    suffix after its already-matched `OP_ENDIF`. -/
private theorem splitConditionalAux_append_of_some
    (depth : Nat) (currentRev : Script) (completedRev : List Script)
    (script suffix : Script) (frame : ConditionalFrame)
    (hSplit : splitConditionalAux depth currentRev completedRev script =
      some frame) :
    splitConditionalAux depth currentRev completedRev (script ++ suffix) =
      some { frame with after := frame.after ++ suffix } := by
  induction script generalizing depth currentRev completedRev frame with
  | nil => simp [splitConditionalAux] at hSplit
  | cons element rest ih =>
      cases element with
      | pushData data =>
          simp only [splitConditionalAux] at hSplit ⊢
          exact ih _ _ _ _ hSplit
      | pushNum value =>
          simp only [splitConditionalAux] at hSplit ⊢
          exact ih _ _ _ _ hSplit
      | op opcode =>
          cases depth <;> cases opcode <;>
            simp only [splitConditionalAux] at hSplit ⊢
          all_goals
            first
            | exact ih _ _ _ _ hSplit
            | cases hSplit
              rfl

/-- Public append law for the depth-aware conditional splitter. -/
theorem splitConditional_append_of_some
    {script suffix : Script} {frame : ConditionalFrame}
    (hSplit : splitConditional script = some frame) :
    splitConditional (script ++ suffix) =
      some { frame with after := frame.after ++ suffix } := by
  exact splitConditionalAux_append_of_some 0 [] [] script suffix frame hSplit

/-- Selecting from a frame whose suffix was extended is the same as appending
    that suffix after the original selected execution. -/
theorem ConditionalFrame.select_append (frame : ConditionalFrame)
    (executeFirst : Bool) (suffix : Script) :
    ({ frame with after := frame.after ++ suffix }).select executeFirst =
      frame.select executeFirst ++ suffix := by
  simp [ConditionalFrame.select, List.append_assoc]

end LeanMiniscript.Script
