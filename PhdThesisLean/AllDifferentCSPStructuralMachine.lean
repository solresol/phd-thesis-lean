import PhdThesisLean.AllDifferentCSPMachine

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability
open Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

/-!
# Complete domain-section structural machine

This module continues the finite-machine construction for thesis corollary
`cor:all-different-csp`.  Its machine consumes the checked, outer-count-free
domain-row payload from `DomainFieldSection.rowPayloadFinEncoding`.  It keeps
the current variable index and current row count as canonical binary words,
advances the index even across empty rows, and emits the exact tagged domain
occurrence stream required by `DomainFieldSection.outputEncode`.

`completeDomainSectionComputableInPolyTime` composes that indexed-row machine
with the checked outer-count removal pass, starting from the complete counted
domain-section encoding.  The row payload is therefore an internal checked
intermediate rather than a caller-supplied assumption.

`AllDifferentCSPScopeSection` reuses the counted-row input and header-removal
pass for scopes, checks the tagged section output, and specifies the exact
section/header assembly. `AllDifferentCSPScopeMachine` implements and composes
the complete scope branch in polynomial time. `AllDifferentCSPSourceSections`
splits the complete compiler input and applies this domain machine while
preserving all scopes through the checked generic pair-left API. Paired scope
processing and executable header staging,
canonical relabelling, edge deduplication, objective rows, and full compiler
composition remain separate obligations.
-/

/-- Work stacks for the complete exhaustion-delimited domain-section pass. -/
inductive DomainSectionStack
  | input
  | index
  | count
  | work
  | scratch
  | output
  deriving DecidableEq, Fintype

/-- Control phases for the complete domain-section pass.  Boundary/end pairs
remember whether the field just consumed was followed by another delimiter or
by exhaustion of the complete checked payload. -/
inductive DomainSectionLabel
  | start
  | readCount
  | restoreCountBoundary
  | restoreCountEnd
  | decideCountBoundary
  | decideCountEnd
  | beginValue
  | copyIndex
  | copyValue
  | restoreIndexBoundary
  | restoreIndexEnd
  | predBoundary
  | predBoundaryCheck
  | predBoundaryRestore
  | predBoundaryDecide
  | predEnd
  | predEndCheck
  | predEndRestore
  | predEndDecide
  | advanceBoundary
  | advanceBoundaryRestore
  | advanceEnd
  | advanceEndRestore
  | finish
  | clearIndex
  deriving DecidableEq, Fintype

/-- The outer option distinguishes stack exhaustion from an inner delimiter. -/
abbrev DomainSectionState := Option (Option Bool)

private def domainSectionPopped
    (_state : DomainSectionState)
    (symbol : Option (Option Bool)) : DomainSectionState :=
  symbol

private def domainSectionPresent : DomainSectionState → Bool
  | some _ => true
  | none => false

private def domainSectionIsBit : DomainSectionState → Bool
  | some (some _) => true
  | _ => false

private def domainSectionBitTrue : DomainSectionState → Bool
  | some (some true) => true
  | _ => false

private def domainSectionHeld : DomainSectionState → Option Bool
  | some symbol => symbol
  | none => none

private def DomainSectionAlphabet (_stack : DomainSectionStack) : Type :=
  Option Bool

/-- A finite program for every counted domain row.  The checked input decoder
guarantees that row counts and field boundaries are valid; the program still
performs the corresponding binary countdown explicitly. -/
def domainSectionProgram :
    DomainSectionLabel →
      TM2.Stmt DomainSectionAlphabet DomainSectionLabel DomainSectionState
  | .start =>
      .pop .input domainSectionPopped <|
        .branch domainSectionPresent
          (.goto (fun _ => .readCount))
          (.goto (fun _ => .finish))
  | .readCount =>
      .pop .input domainSectionPopped <|
        .branch domainSectionPresent
          (.branch domainSectionIsBit
            (.push .work domainSectionHeld <|
              .goto (fun _ => .readCount))
            (.goto (fun _ => .restoreCountBoundary)))
          (.goto (fun _ => .restoreCountEnd))
  | .restoreCountBoundary =>
      .pop .work domainSectionPopped <|
        .branch domainSectionPresent
          (.push .count domainSectionHeld <|
            .goto (fun _ => .restoreCountBoundary))
          (.goto (fun _ => .decideCountBoundary))
  | .restoreCountEnd =>
      .pop .work domainSectionPopped <|
        .branch domainSectionPresent
          (.push .count domainSectionHeld <|
            .goto (fun _ => .restoreCountEnd))
          (.goto (fun _ => .decideCountEnd))
  | .decideCountBoundary =>
      .pop .count domainSectionPopped <|
        .branch domainSectionPresent
          (.push .count domainSectionHeld <|
            .goto (fun _ => .beginValue))
          (.goto (fun _ => .advanceBoundary))
  | .decideCountEnd =>
      .pop .count domainSectionPopped <|
        .branch domainSectionPresent
          (.goto (fun _ => .finish))
          (.goto (fun _ => .advanceEnd))
  | .beginValue =>
      .push .scratch (fun _ => (none : Option Bool)) <|
        .push .scratch (fun _ => some true) <|
          .push .scratch (fun _ => some true) <|
            .push .scratch (fun _ => (none : Option Bool)) <|
              .push .scratch (fun _ => (none : Option Bool)) <|
                .goto (fun _ => .copyIndex)
  | .copyIndex =>
      .pop .index domainSectionPopped <|
        .branch domainSectionPresent
          (.push .work domainSectionHeld <|
            .push .scratch domainSectionHeld <|
              .goto (fun _ => .copyIndex))
          (.push .scratch (fun _ => (none : Option Bool)) <|
            .goto (fun _ => .copyValue))
  | .copyValue =>
      .pop .input domainSectionPopped <|
        .branch domainSectionPresent
          (.branch domainSectionIsBit
            (.push .scratch domainSectionHeld <|
              .goto (fun _ => .copyValue))
            (.goto (fun _ => .restoreIndexBoundary)))
          (.goto (fun _ => .restoreIndexEnd))
  | .restoreIndexBoundary =>
      .pop .work domainSectionPopped <|
        .branch domainSectionPresent
          (.push .index domainSectionHeld <|
            .goto (fun _ => .restoreIndexBoundary))
          (.goto (fun _ => .predBoundary))
  | .restoreIndexEnd =>
      .pop .work domainSectionPopped <|
        .branch domainSectionPresent
          (.push .index domainSectionHeld <|
            .goto (fun _ => .restoreIndexEnd))
          (.goto (fun _ => .predEnd))
  | .predBoundary =>
      .pop .count domainSectionPopped <|
        .branch domainSectionPresent
          (.branch domainSectionBitTrue
            (.goto (fun _ => .predBoundaryCheck))
            (.push .work (fun _ => some true) <|
              .goto (fun _ => .predBoundary)))
          (.goto (fun _ => .predBoundaryRestore))
  | .predBoundaryCheck =>
      .pop .count domainSectionPopped <|
        .branch domainSectionPresent
          (.push .count domainSectionHeld <|
            .push .count (fun _ => some false) <|
              .goto (fun _ => .predBoundaryRestore))
          (.goto (fun _ => .predBoundaryRestore))
  | .predBoundaryRestore =>
      .pop .work domainSectionPopped <|
        .branch domainSectionPresent
          (.push .count domainSectionHeld <|
            .goto (fun _ => .predBoundaryRestore))
          (.goto (fun _ => .predBoundaryDecide))
  | .predBoundaryDecide =>
      .pop .count domainSectionPopped <|
        .branch domainSectionPresent
          (.push .count domainSectionHeld <|
            .goto (fun _ => .beginValue))
          (.goto (fun _ => .advanceBoundary))
  | .predEnd =>
      .pop .count domainSectionPopped <|
        .branch domainSectionPresent
          (.branch domainSectionBitTrue
            (.goto (fun _ => .predEndCheck))
            (.push .work (fun _ => some true) <|
              .goto (fun _ => .predEnd)))
          (.goto (fun _ => .predEndRestore))
  | .predEndCheck =>
      .pop .count domainSectionPopped <|
        .branch domainSectionPresent
          (.push .count domainSectionHeld <|
            .push .count (fun _ => some false) <|
              .goto (fun _ => .predEndRestore))
          (.goto (fun _ => .predEndRestore))
  | .predEndRestore =>
      .pop .work domainSectionPopped <|
        .branch domainSectionPresent
          (.push .count domainSectionHeld <|
            .goto (fun _ => .predEndRestore))
          (.goto (fun _ => .predEndDecide))
  | .predEndDecide =>
      .pop .count domainSectionPopped <|
        .branch domainSectionPresent
          (.goto (fun _ => .finish))
          (.goto (fun _ => .advanceEnd))
  | .advanceBoundary =>
      .pop .index domainSectionPopped <|
        .branch domainSectionPresent
          (.branch domainSectionBitTrue
            (.push .work (fun _ => some false) <|
              .goto (fun _ => .advanceBoundary))
            (.push .index (fun _ => some true) <|
              .goto (fun _ => .advanceBoundaryRestore)))
          (.push .index (fun _ => some true) <|
            .goto (fun _ => .advanceBoundaryRestore))
  | .advanceBoundaryRestore =>
      .pop .work domainSectionPopped <|
        .branch domainSectionPresent
          (.push .index domainSectionHeld <|
            .goto (fun _ => .advanceBoundaryRestore))
          (.goto (fun _ => .readCount))
  | .advanceEnd =>
      .pop .index domainSectionPopped <|
        .branch domainSectionPresent
          (.branch domainSectionBitTrue
            (.push .work (fun _ => some false) <|
              .goto (fun _ => .advanceEnd))
            (.push .index (fun _ => some true) <|
              .goto (fun _ => .advanceEndRestore)))
          (.push .index (fun _ => some true) <|
            .goto (fun _ => .advanceEndRestore))
  | .advanceEndRestore =>
      .pop .work domainSectionPopped <|
        .branch domainSectionPresent
          (.push .index domainSectionHeld <|
            .goto (fun _ => .advanceEndRestore))
          (.goto (fun _ => .finish))
  | .finish =>
      .pop .scratch domainSectionPopped <|
        .branch domainSectionPresent
          (.push .output domainSectionHeld <|
            .goto (fun _ => .finish))
          (.goto (fun _ => .clearIndex))
  | .clearIndex =>
      .pop .index domainSectionPopped <|
        .branch domainSectionPresent
          (.goto (fun _ => .clearIndex))
          .halt

/-- Concrete six-stack domain-section transducer. -/
def domainSectionComputer : FinTM2 where
  K := DomainSectionStack
  k₀ := .input
  k₁ := .output
  Γ := DomainSectionAlphabet
  Λ := DomainSectionLabel
  main := .start
  σ := DomainSectionState
  initialState := none
  Γk₀Fin := show Fintype (Option Bool) from inferInstance
  m := domainSectionProgram

private def domainSectionStacks
    (input index count work scratch output : List (Option Bool)) :
    (stack : DomainSectionStack) → List (DomainSectionAlphabet stack)
  | .input => input
  | .index => index
  | .count => count
  | .work => work
  | .scratch => scratch
  | .output => output

private def domainSectionCfg
    (label : Option DomainSectionLabel) (state : DomainSectionState)
    (input index count work scratch output : List (Option Bool)) :
    domainSectionComputer.Cfg where
  l := label
  var := state
  stk := domainSectionStacks input index count work scratch output

private def domainSectionEvalsToInTimeOne
    {start finish : domainSectionComputer.Cfg}
    (hstep : domainSectionComputer.step start = some finish) :
    EvalsToInTime domainSectionComputer.step start (some finish) 1 where
  steps := 1
  evals_in_steps := by simpa [Function.iterate_one] using hstep
  steps_le_m := Nat.le_refl 1

private def domainSectionEvalsToInTimeMono
    {start : domainSectionComputer.Cfg}
    {finish : Option domainSectionComputer.Cfg} {small large : ℕ}
    (run : EvalsToInTime domainSectionComputer.step start finish small)
    (h : small ≤ large) :
    EvalsToInTime domainSectionComputer.step start finish large where
  steps := run.steps
  evals_in_steps := run.evals_in_steps
  steps_le_m := run.steps_le_m.trans h

private theorem domainSection_step_start_cons
    (symbol : Option Bool) (input index count work scratch output :
      List (Option Bool)) (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .start) state (symbol :: input) index count
          work scratch output) =
      some (domainSectionCfg (some .readCount) (some symbol) input index count
        work scratch output) := by
  rcases symbol with _ | bit <;>
    simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
      domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
      domainSectionPopped, domainSectionPresent] <;>
    (funext stack; cases stack <;> rfl)

private theorem domainSection_step_start_nil
    (index count work scratch output : List (Option Bool))
    (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .start) state [] index count work scratch
          output) =
      some (domainSectionCfg (some .finish) none [] index count work scratch
        output) := by
  simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
    domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
    domainSectionPopped, domainSectionPresent]

private theorem domainSection_step_readCount_bit
    (bit : Bool) (input index count work scratch output :
      List (Option Bool)) (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .readCount) state (some bit :: input) index
          count work scratch output) =
      some (domainSectionCfg (some .readCount) (some (some bit)) input index
        count (some bit :: work) scratch output) := by
  cases bit <;>
    simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
      domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
      domainSectionPopped, domainSectionPresent, domainSectionIsBit,
      domainSectionHeld, Function.update] <;>
    (funext stack; cases stack <;> rfl)

private theorem domainSection_step_readCount_delimiter
    (input index count work scratch output : List (Option Bool))
    (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .readCount) state (none :: input) index count
          work scratch output) =
      some (domainSectionCfg (some .restoreCountBoundary) (some none) input
        index count work scratch output) := by
  simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
    domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
    domainSectionPopped, domainSectionPresent, domainSectionIsBit]
  funext stack
  cases stack <;> rfl

private theorem domainSection_step_readCount_nil
    (index count work scratch output : List (Option Bool))
    (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .readCount) state [] index count work scratch
          output) =
      some (domainSectionCfg (some .restoreCountEnd) none [] index count work
        scratch output) := by
  simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
    domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
    domainSectionPopped, domainSectionPresent]

private theorem domainSection_step_restoreCountBoundary_cons
    (symbol : Option Bool) (input index count work scratch output :
      List (Option Bool)) (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .restoreCountBoundary) state input index count
          (symbol :: work) scratch output) =
      some (domainSectionCfg (some .restoreCountBoundary) (some symbol) input
        index (symbol :: count) work scratch output) := by
  rcases symbol with _ | bit <;>
    simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
      domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
      domainSectionPopped, domainSectionPresent, domainSectionHeld,
      Function.update] <;>
    (funext stack; cases stack <;> rfl)

private theorem domainSection_step_restoreCountBoundary_nil
    (input index count scratch output : List (Option Bool))
    (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .restoreCountBoundary) state input index count
          [] scratch output) =
      some (domainSectionCfg (some .decideCountBoundary) none input index
        count [] scratch output) := by
  simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
    domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
    domainSectionPopped, domainSectionPresent]

private theorem domainSection_step_restoreCountEnd_cons
    (symbol : Option Bool) (index count work scratch output :
      List (Option Bool)) (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .restoreCountEnd) state [] index count
          (symbol :: work) scratch output) =
      some (domainSectionCfg (some .restoreCountEnd) (some symbol) [] index
        (symbol :: count) work scratch output) := by
  rcases symbol with _ | bit <;>
    simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
      domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
      domainSectionPopped, domainSectionPresent, domainSectionHeld,
      Function.update] <;>
    (funext stack; cases stack <;> rfl)

private theorem domainSection_step_restoreCountEnd_nil
    (index count scratch output : List (Option Bool))
    (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .restoreCountEnd) state [] index count []
          scratch output) =
      some (domainSectionCfg (some .decideCountEnd) none [] index count []
        scratch output) := by
  simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
    domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
    domainSectionPopped, domainSectionPresent]

private theorem domainSection_step_decideCountBoundary_nil
    (input index work scratch output : List (Option Bool))
    (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .decideCountBoundary) state input index [] work
          scratch output) =
      some (domainSectionCfg (some .advanceBoundary) none input index [] work
        scratch output) := by
  simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
    domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
    domainSectionPopped, domainSectionPresent]

private theorem domainSection_step_decideCountBoundary_cons
    (symbol : Option Bool) (count input index work scratch output :
      List (Option Bool)) (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .decideCountBoundary) state input index
          (symbol :: count) work scratch output) =
      some (domainSectionCfg (some .beginValue) (some symbol) input index
        (symbol :: count) work scratch output) := by
  rcases symbol with _ | bit <;>
    simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
      domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
      domainSectionPopped, domainSectionPresent, domainSectionHeld,
      Function.update]

private theorem domainSection_step_decideCountEnd_nil
    (index work scratch output : List (Option Bool))
    (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .decideCountEnd) state [] index [] work scratch
          output) =
      some (domainSectionCfg (some .advanceEnd) none [] index [] work scratch
        output) := by
  simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
    domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
    domainSectionPopped, domainSectionPresent]

private theorem domainSection_step_beginValue
    (input index count work scratch output : List (Option Bool))
    (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .beginValue) state input index count work
          scratch output) =
      some (domainSectionCfg (some .copyIndex) state input index count work
        (none :: none :: some true :: some true :: none :: scratch) output) := by
  simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
    domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
    Function.update]
  funext stack
  cases stack <;> rfl

private theorem domainSection_step_copyIndex_cons
    (symbol : Option Bool) (input index count work scratch output :
      List (Option Bool)) (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .copyIndex) state input (symbol :: index) count
          work scratch output) =
      some (domainSectionCfg (some .copyIndex) (some symbol) input index count
        (symbol :: work) (symbol :: scratch) output) := by
  rcases symbol with _ | bit <;>
    simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
      domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
      domainSectionPopped, domainSectionPresent, domainSectionHeld,
      Function.update] <;>
    (funext stack; cases stack <;> rfl)

private theorem domainSection_step_copyIndex_nil
    (input count work scratch output : List (Option Bool))
    (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .copyIndex) state input [] count work scratch
          output) =
      some (domainSectionCfg (some .copyValue) none input [] count work
        (none :: scratch) output) := by
  simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
    domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
    domainSectionPopped, domainSectionPresent, Function.update]
  funext stack
  cases stack <;> rfl

private theorem domainSection_step_copyValue_bit
    (bit : Bool) (input count work scratch output : List (Option Bool))
    (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .copyValue) state (some bit :: input) [] count
          work scratch output) =
      some (domainSectionCfg (some .copyValue) (some (some bit)) input [] count
        work (some bit :: scratch) output) := by
  cases bit <;>
    simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
      domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
      domainSectionPopped, domainSectionPresent, domainSectionIsBit,
      domainSectionHeld, Function.update] <;>
    (funext stack; cases stack <;> rfl)

private theorem domainSection_step_copyValue_delimiter
    (input count work scratch output : List (Option Bool))
    (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .copyValue) state (none :: input) [] count
          work scratch output) =
      some (domainSectionCfg (some .restoreIndexBoundary) (some none) input []
        count work scratch output) := by
  simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
    domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
    domainSectionPopped, domainSectionPresent, domainSectionIsBit]
  funext stack
  cases stack <;> rfl

private theorem domainSection_step_copyValue_nil
    (count work scratch output : List (Option Bool))
    (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .copyValue) state [] [] count work scratch
          output) =
      some (domainSectionCfg (some .restoreIndexEnd) none [] [] count work
        scratch output) := by
  simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
    domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
    domainSectionPopped, domainSectionPresent]

private theorem domainSection_step_restoreIndexBoundary_cons
    (symbol : Option Bool) (input index count work scratch output :
      List (Option Bool)) (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .restoreIndexBoundary) state input index count
          (symbol :: work) scratch output) =
      some (domainSectionCfg (some .restoreIndexBoundary) (some symbol) input
        (symbol :: index) count work scratch output) := by
  rcases symbol with _ | bit <;>
    simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
      domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
      domainSectionPopped, domainSectionPresent, domainSectionHeld,
      Function.update] <;>
    (funext stack; cases stack <;> rfl)

private theorem domainSection_step_restoreIndexBoundary_nil
    (input index count scratch output : List (Option Bool))
    (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .restoreIndexBoundary) state input index count
          [] scratch output) =
      some (domainSectionCfg (some .predBoundary) none input index count []
        scratch output) := by
  simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
    domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
    domainSectionPopped, domainSectionPresent]

private theorem domainSection_step_restoreIndexEnd_cons
    (symbol : Option Bool) (index count work scratch output :
      List (Option Bool)) (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .restoreIndexEnd) state [] index count
          (symbol :: work) scratch output) =
      some (domainSectionCfg (some .restoreIndexEnd) (some symbol) []
        (symbol :: index) count work scratch output) := by
  rcases symbol with _ | bit <;>
    simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
      domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
      domainSectionPopped, domainSectionPresent, domainSectionHeld,
      Function.update] <;>
    (funext stack; cases stack <;> rfl)

private theorem domainSection_step_restoreIndexEnd_nil
    (index count scratch output : List (Option Bool))
    (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .restoreIndexEnd) state [] index count []
          scratch output) =
      some (domainSectionCfg (some .predEnd) none [] index count [] scratch
        output) := by
  simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
    domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
    domainSectionPopped, domainSectionPresent]

private theorem domainSection_step_predBoundary_false
    (count input index work scratch output : List (Option Bool))
    (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .predBoundary) state input index
          (some false :: count) work scratch output) =
      some (domainSectionCfg (some .predBoundary) (some (some false)) input
        index count (some true :: work) scratch output) := by
  simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
    domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
    domainSectionPopped, domainSectionPresent, domainSectionBitTrue,
    Function.update]
  funext stack
  cases stack <;> rfl

private theorem domainSection_step_predBoundary_true
    (count input index work scratch output : List (Option Bool))
    (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .predBoundary) state input index
          (some true :: count) work scratch output) =
      some (domainSectionCfg (some .predBoundaryCheck) (some (some true))
        input index count work scratch output) := by
  simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
    domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
    domainSectionPopped, domainSectionPresent, domainSectionBitTrue]
  funext stack
  cases stack <;> rfl

private theorem domainSection_step_predBoundary_nil
    (input index work scratch output : List (Option Bool))
    (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .predBoundary) state input index [] work
          scratch output) =
      some (domainSectionCfg (some .predBoundaryRestore) none input index []
        work scratch output) := by
  simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
    domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
    domainSectionPopped, domainSectionPresent]

private theorem domainSection_step_predBoundaryCheck_cons
    (symbol : Option Bool) (count input index work scratch output :
      List (Option Bool)) (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .predBoundaryCheck) state input index
          (symbol :: count) work scratch output) =
      some (domainSectionCfg (some .predBoundaryRestore) (some symbol) input
        index (some false :: symbol :: count) work scratch output) := by
  rcases symbol with _ | bit <;>
    simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
      domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
      domainSectionPopped, domainSectionPresent, domainSectionHeld,
      Function.update] <;>
    (funext stack; cases stack <;> rfl)

private theorem domainSection_step_predBoundaryCheck_nil
    (input index work scratch output : List (Option Bool))
    (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .predBoundaryCheck) state input index [] work
          scratch output) =
      some (domainSectionCfg (some .predBoundaryRestore) none input index []
        work scratch output) := by
  simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
    domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
    domainSectionPopped, domainSectionPresent]

private theorem domainSection_step_predBoundaryRestore_cons
    (symbol : Option Bool) (count input index work scratch output :
      List (Option Bool)) (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .predBoundaryRestore) state input index count
          (symbol :: work) scratch output) =
      some (domainSectionCfg (some .predBoundaryRestore) (some symbol) input
        index (symbol :: count) work scratch output) := by
  rcases symbol with _ | bit <;>
    simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
      domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
      domainSectionPopped, domainSectionPresent, domainSectionHeld,
      Function.update] <;>
    (funext stack; cases stack <;> rfl)

private theorem domainSection_step_predBoundaryRestore_nil
    (count input index scratch output : List (Option Bool))
    (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .predBoundaryRestore) state input index count
          [] scratch output) =
      some (domainSectionCfg (some .predBoundaryDecide) none input index count
        [] scratch output) := by
  simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
    domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
    domainSectionPopped, domainSectionPresent]

private theorem domainSection_step_predBoundaryDecide_nil
    (input index work scratch output : List (Option Bool))
    (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .predBoundaryDecide) state input index [] work
          scratch output) =
      some (domainSectionCfg (some .advanceBoundary) none input index [] work
        scratch output) := by
  simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
    domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
    domainSectionPopped, domainSectionPresent]

private theorem domainSection_step_predBoundaryDecide_cons
    (symbol : Option Bool) (count input index work scratch output :
      List (Option Bool)) (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .predBoundaryDecide) state input index
          (symbol :: count) work scratch output) =
      some (domainSectionCfg (some .beginValue) (some symbol) input index
        (symbol :: count) work scratch output) := by
  rcases symbol with _ | bit <;>
    simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
      domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
      domainSectionPopped, domainSectionPresent, domainSectionHeld,
      Function.update]

private theorem domainSection_step_predEnd_false
    (count index work scratch output : List (Option Bool))
    (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .predEnd) state [] index
          (some false :: count) work scratch output) =
      some (domainSectionCfg (some .predEnd) (some (some false)) [] index
        count (some true :: work) scratch output) := by
  simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
    domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
    domainSectionPopped, domainSectionPresent, domainSectionBitTrue,
    Function.update]
  funext stack
  cases stack <;> rfl

private theorem domainSection_step_predEnd_true
    (count index work scratch output : List (Option Bool))
    (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .predEnd) state [] index
          (some true :: count) work scratch output) =
      some (domainSectionCfg (some .predEndCheck) (some (some true)) [] index
        count work scratch output) := by
  simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
    domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
    domainSectionPopped, domainSectionPresent, domainSectionBitTrue]
  funext stack
  cases stack <;> rfl

private theorem domainSection_step_predEnd_nil
    (index work scratch output : List (Option Bool))
    (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .predEnd) state [] index [] work scratch
          output) =
      some (domainSectionCfg (some .predEndRestore) none [] index [] work
        scratch output) := by
  simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
    domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
    domainSectionPopped, domainSectionPresent]

private theorem domainSection_step_predEndCheck_cons
    (symbol : Option Bool) (count index work scratch output :
      List (Option Bool)) (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .predEndCheck) state [] index
          (symbol :: count) work scratch output) =
      some (domainSectionCfg (some .predEndRestore) (some symbol) [] index
        (some false :: symbol :: count) work scratch output) := by
  rcases symbol with _ | bit <;>
    simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
      domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
      domainSectionPopped, domainSectionPresent, domainSectionHeld,
      Function.update] <;>
    (funext stack; cases stack <;> rfl)

private theorem domainSection_step_predEndCheck_nil
    (index work scratch output : List (Option Bool))
    (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .predEndCheck) state [] index [] work scratch
          output) =
      some (domainSectionCfg (some .predEndRestore) none [] index [] work
        scratch output) := by
  simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
    domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
    domainSectionPopped, domainSectionPresent]

private theorem domainSection_step_predEndRestore_cons
    (symbol : Option Bool) (count index work scratch output :
      List (Option Bool)) (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .predEndRestore) state [] index count
          (symbol :: work) scratch output) =
      some (domainSectionCfg (some .predEndRestore) (some symbol) [] index
        (symbol :: count) work scratch output) := by
  rcases symbol with _ | bit <;>
    simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
      domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
      domainSectionPopped, domainSectionPresent, domainSectionHeld,
      Function.update] <;>
    (funext stack; cases stack <;> rfl)

private theorem domainSection_step_predEndRestore_nil
    (count index scratch output : List (Option Bool))
    (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .predEndRestore) state [] index count []
          scratch output) =
      some (domainSectionCfg (some .predEndDecide) none [] index count []
        scratch output) := by
  simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
    domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
    domainSectionPopped, domainSectionPresent]

private theorem domainSection_step_predEndDecide_nil
    (index work scratch output : List (Option Bool))
    (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .predEndDecide) state [] index [] work scratch
          output) =
      some (domainSectionCfg (some .advanceEnd) none [] index [] work scratch
        output) := by
  simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
    domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
    domainSectionPopped, domainSectionPresent]

private theorem domainSection_step_advanceBoundary_true
    (index input count work scratch output : List (Option Bool))
    (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .advanceBoundary) state input
          (some true :: index) count work scratch output) =
      some (domainSectionCfg (some .advanceBoundary) (some (some true)) input
        index count (some false :: work) scratch output) := by
  simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
    domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
    domainSectionPopped, domainSectionPresent, domainSectionBitTrue,
    Function.update]
  funext stack
  cases stack <;> rfl

private theorem domainSection_step_advanceBoundary_false
    (index input count work scratch output : List (Option Bool))
    (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .advanceBoundary) state input
          (some false :: index) count work scratch output) =
      some (domainSectionCfg (some .advanceBoundaryRestore)
        (some (some false)) input (some true :: index) count work scratch
        output) := by
  simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
    domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
    domainSectionPopped, domainSectionPresent, domainSectionBitTrue,
    Function.update]
  funext stack
  cases stack <;> rfl

private theorem domainSection_step_advanceBoundary_nil
    (input count work scratch output : List (Option Bool))
    (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .advanceBoundary) state input [] count work
          scratch output) =
      some (domainSectionCfg (some .advanceBoundaryRestore) none input
        [some true] count work scratch output) := by
  simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
    domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
    domainSectionPopped, domainSectionPresent, Function.update]
  funext stack
  cases stack <;> rfl

private theorem domainSection_step_advanceBoundaryRestore_cons
    (symbol : Option Bool) (index input count work scratch output :
      List (Option Bool)) (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .advanceBoundaryRestore) state input index
          count (symbol :: work) scratch output) =
      some (domainSectionCfg (some .advanceBoundaryRestore) (some symbol)
        input (symbol :: index) count work scratch output) := by
  rcases symbol with _ | bit <;>
    simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
      domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
      domainSectionPopped, domainSectionPresent, domainSectionHeld,
      Function.update] <;>
    (funext stack; cases stack <;> rfl)

private theorem domainSection_step_advanceBoundaryRestore_nil
    (index input count scratch output : List (Option Bool))
    (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .advanceBoundaryRestore) state input index
          count [] scratch output) =
      some (domainSectionCfg (some .readCount) none input index count []
        scratch output) := by
  simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
    domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
    domainSectionPopped, domainSectionPresent]

private theorem domainSection_step_advanceEnd_true
    (index count work scratch output : List (Option Bool))
    (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .advanceEnd) state [] (some true :: index)
          count work scratch output) =
      some (domainSectionCfg (some .advanceEnd) (some (some true)) [] index
        count (some false :: work) scratch output) := by
  simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
    domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
    domainSectionPopped, domainSectionPresent, domainSectionBitTrue,
    Function.update]
  funext stack
  cases stack <;> rfl

private theorem domainSection_step_advanceEnd_false
    (index count work scratch output : List (Option Bool))
    (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .advanceEnd) state [] (some false :: index)
          count work scratch output) =
      some (domainSectionCfg (some .advanceEndRestore) (some (some false)) []
        (some true :: index) count work scratch output) := by
  simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
    domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
    domainSectionPopped, domainSectionPresent, domainSectionBitTrue,
    Function.update]
  funext stack
  cases stack <;> rfl

private theorem domainSection_step_advanceEnd_nil
    (count work scratch output : List (Option Bool))
    (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .advanceEnd) state [] [] count work scratch
          output) =
      some (domainSectionCfg (some .advanceEndRestore) none [] [some true]
        count work scratch output) := by
  simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
    domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
    domainSectionPopped, domainSectionPresent, Function.update]
  funext stack
  cases stack <;> rfl

private theorem domainSection_step_advanceEndRestore_cons
    (symbol : Option Bool) (index count work scratch output :
      List (Option Bool)) (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .advanceEndRestore) state [] index count
          (symbol :: work) scratch output) =
      some (domainSectionCfg (some .advanceEndRestore) (some symbol) []
        (symbol :: index) count work scratch output) := by
  rcases symbol with _ | bit <;>
    simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
      domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
      domainSectionPopped, domainSectionPresent, domainSectionHeld,
      Function.update] <;>
    (funext stack; cases stack <;> rfl)

private theorem domainSection_step_advanceEndRestore_nil
    (index count scratch output : List (Option Bool))
    (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .advanceEndRestore) state [] index count []
          scratch output) =
      some (domainSectionCfg (some .finish) none [] index count [] scratch
        output) := by
  simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
    domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
    domainSectionPopped, domainSectionPresent]

private theorem domainSection_step_finish_cons
    (symbol : Option Bool) (index count work scratch output :
      List (Option Bool)) (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .finish) state [] index count work
          (symbol :: scratch) output) =
      some (domainSectionCfg (some .finish) (some symbol) [] index count work
        scratch (symbol :: output)) := by
  rcases symbol with _ | bit <;>
    simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
      domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
      domainSectionPopped, domainSectionPresent, domainSectionHeld,
      Function.update] <;>
    (funext stack; cases stack <;> rfl)

private theorem domainSection_step_finish_nil
    (index count work output : List (Option Bool))
    (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .finish) state [] index count work [] output) =
      some (domainSectionCfg (some .clearIndex) none [] index count work []
        output) := by
  simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
    domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
    domainSectionPopped, domainSectionPresent, Function.update]

private theorem domainSection_step_clearIndex_cons
    (symbol : Option Bool) (index count work output : List (Option Bool))
    (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .clearIndex) state [] (symbol :: index) count
          work [] output) =
      some (domainSectionCfg (some .clearIndex) (some symbol) [] index count
        work [] output) := by
  rcases symbol with _ | bit <;>
    simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
      domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
      domainSectionPopped, domainSectionPresent] <;>
    (funext stack; cases stack <;> rfl)

private theorem domainSection_step_clearIndex_nil
    (count work output : List (Option Bool)) (state : DomainSectionState) :
    domainSectionComputer.step
        (domainSectionCfg (some .clearIndex) state [] [] count work [] output) =
      some (domainSectionCfg none none [] [] count work [] output) := by
  simp [domainSectionComputer, FinTM2.step, domainSectionCfg,
    domainSectionProgram, domainSectionStacks, DomainSectionAlphabet,
    domainSectionPopped, domainSectionPresent]

private def domainSection_readCountBoundary_evals
    (bits : List Bool) (tail index count work scratch output :
      List (Option Bool)) (state : DomainSectionState) :
    EvalsToInTime domainSectionComputer.step
      (domainSectionCfg (some .readCount) state
        (bits.map some ++ none :: tail) index count work scratch output)
      (some (domainSectionCfg (some .restoreCountBoundary) (some none) tail
        index count (bits.reverse.map some ++ work) scratch output))
      (bits.length + 1) := by
  induction bits generalizing work state with
  | nil =>
      simpa using domainSectionEvalsToInTimeOne
        (domainSection_step_readCount_delimiter tail index count work scratch
          output state)
  | cons bit bits ih =>
      have hone := domainSectionEvalsToInTimeOne
        (domainSection_step_readCount_bit bit
          (bits.map some ++ none :: tail) index count work scratch output state)
      have hrest := ih (some bit :: work) (some (some bit))
      have hall := EvalsToInTime.trans domainSectionComputer.step
        1 (bits.length + 1)
        (domainSectionCfg (some .readCount) state
          ((bit :: bits).map some ++ none :: tail) index count work scratch
          output)
        (domainSectionCfg (some .readCount) (some (some bit))
          (bits.map some ++ none :: tail) index count (some bit :: work)
          scratch output)
        (some (domainSectionCfg (some .restoreCountBoundary) (some none) tail
          index count ((bit :: bits).reverse.map some ++ work) scratch output))
        (by simpa using hone)
        (by simpa [List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def domainSection_readCountEnd_evals
    (bits : List Bool) (index count work scratch output :
      List (Option Bool)) (state : DomainSectionState) :
    EvalsToInTime domainSectionComputer.step
      (domainSectionCfg (some .readCount) state (bits.map some) index count
        work scratch output)
      (some (domainSectionCfg (some .restoreCountEnd) none [] index count
        (bits.reverse.map some ++ work) scratch output))
      (bits.length + 1) := by
  induction bits generalizing work state with
  | nil =>
      simpa using domainSectionEvalsToInTimeOne
        (domainSection_step_readCount_nil index count work scratch output state)
  | cons bit bits ih =>
      have hone := domainSectionEvalsToInTimeOne
        (domainSection_step_readCount_bit bit (bits.map some) index count work
          scratch output state)
      have hrest := ih (some bit :: work) (some (some bit))
      have hall := EvalsToInTime.trans domainSectionComputer.step
        1 (bits.length + 1)
        (domainSectionCfg (some .readCount) state ((bit :: bits).map some)
          index count work scratch output)
        (domainSectionCfg (some .readCount) (some (some bit)) (bits.map some)
          index count (some bit :: work) scratch output)
        (some (domainSectionCfg (some .restoreCountEnd) none [] index count
          ((bit :: bits).reverse.map some ++ work) scratch output))
        (by simpa using hone)
        (by simpa [List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def domainSection_restoreCountBoundary_evals
    (work input index count scratch output : List (Option Bool))
    (state : DomainSectionState) :
    EvalsToInTime domainSectionComputer.step
      (domainSectionCfg (some .restoreCountBoundary) state input index count
        work scratch output)
      (some (domainSectionCfg (some .decideCountBoundary) none input index
        (work.reverse ++ count) [] scratch output))
      (work.length + 1) := by
  induction work generalizing count state with
  | nil =>
      simpa using domainSectionEvalsToInTimeOne
        (domainSection_step_restoreCountBoundary_nil input index count scratch
          output state)
  | cons symbol work ih =>
      have hone := domainSectionEvalsToInTimeOne
        (domainSection_step_restoreCountBoundary_cons symbol input index count
          work scratch output state)
      have hrest := ih (symbol :: count) (some symbol)
      have hall := EvalsToInTime.trans domainSectionComputer.step
        1 (work.length + 1)
        (domainSectionCfg (some .restoreCountBoundary) state input index count
          (symbol :: work) scratch output)
        (domainSectionCfg (some .restoreCountBoundary) (some symbol) input
          index (symbol :: count) work scratch output)
        (some (domainSectionCfg (some .decideCountBoundary) none input index
          ((symbol :: work).reverse ++ count) [] scratch output))
        (by simpa using hone)
        (by simpa [List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def domainSection_restoreCountEnd_evals
    (work index count scratch output : List (Option Bool))
    (state : DomainSectionState) :
    EvalsToInTime domainSectionComputer.step
      (domainSectionCfg (some .restoreCountEnd) state [] index count work
        scratch output)
      (some (domainSectionCfg (some .decideCountEnd) none [] index
        (work.reverse ++ count) [] scratch output))
      (work.length + 1) := by
  induction work generalizing count state with
  | nil =>
      simpa using domainSectionEvalsToInTimeOne
        (domainSection_step_restoreCountEnd_nil index count scratch output
          state)
  | cons symbol work ih =>
      have hone := domainSectionEvalsToInTimeOne
        (domainSection_step_restoreCountEnd_cons symbol index count work
          scratch output state)
      have hrest := ih (symbol :: count) (some symbol)
      have hall := EvalsToInTime.trans domainSectionComputer.step
        1 (work.length + 1)
        (domainSectionCfg (some .restoreCountEnd) state [] index count
          (symbol :: work) scratch output)
        (domainSectionCfg (some .restoreCountEnd) (some symbol) [] index
          (symbol :: count) work scratch output)
        (some (domainSectionCfg (some .decideCountEnd) none [] index
          ((symbol :: work).reverse ++ count) [] scratch output))
        (by simpa using hone)
        (by simpa [List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def domainSection_copyIndex_evals
    (index input count work scratch output : List (Option Bool))
    (state : DomainSectionState) :
    EvalsToInTime domainSectionComputer.step
      (domainSectionCfg (some .copyIndex) state input index count work scratch
        output)
      (some (domainSectionCfg (some .copyValue) none input [] count
        (index.reverse ++ work) (none :: index.reverse ++ scratch) output))
      (index.length + 1) := by
  induction index generalizing work scratch state with
  | nil =>
      simpa using domainSectionEvalsToInTimeOne
        (domainSection_step_copyIndex_nil input count work scratch output state)
  | cons symbol index ih =>
      have hone := domainSectionEvalsToInTimeOne
        (domainSection_step_copyIndex_cons symbol input index count work scratch
          output state)
      have hrest := ih (symbol :: work) (symbol :: scratch) (some symbol)
      have hall := EvalsToInTime.trans domainSectionComputer.step
        1 (index.length + 1)
        (domainSectionCfg (some .copyIndex) state input (symbol :: index)
          count work scratch output)
        (domainSectionCfg (some .copyIndex) (some symbol) input index count
          (symbol :: work) (symbol :: scratch) output)
        (some (domainSectionCfg (some .copyValue) none input [] count
          ((symbol :: index).reverse ++ work)
          (none :: (symbol :: index).reverse ++ scratch) output))
        (by simpa using hone)
        (by simpa [List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def domainSection_copyValueBoundary_evals
    (bits : List Bool) (tail count work scratch output :
      List (Option Bool)) (state : DomainSectionState) :
    EvalsToInTime domainSectionComputer.step
      (domainSectionCfg (some .copyValue) state
        (bits.map some ++ none :: tail) [] count work scratch output)
      (some (domainSectionCfg (some .restoreIndexBoundary) (some none) tail []
        count work (bits.reverse.map some ++ scratch) output))
      (bits.length + 1) := by
  induction bits generalizing scratch state with
  | nil =>
      simpa using domainSectionEvalsToInTimeOne
        (domainSection_step_copyValue_delimiter tail count work scratch output
          state)
  | cons bit bits ih =>
      have hone := domainSectionEvalsToInTimeOne
        (domainSection_step_copyValue_bit bit (bits.map some ++ none :: tail)
          count work scratch output state)
      have hrest := ih (some bit :: scratch) (some (some bit))
      have hall := EvalsToInTime.trans domainSectionComputer.step
        1 (bits.length + 1)
        (domainSectionCfg (some .copyValue) state
          ((bit :: bits).map some ++ none :: tail) [] count work scratch output)
        (domainSectionCfg (some .copyValue) (some (some bit))
          (bits.map some ++ none :: tail) [] count work (some bit :: scratch)
          output)
        (some (domainSectionCfg (some .restoreIndexBoundary) (some none) tail
          [] count work ((bit :: bits).reverse.map some ++ scratch) output))
        (by simpa using hone)
        (by simpa [List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def domainSection_copyValueEnd_evals
    (bits : List Bool) (count work scratch output : List (Option Bool))
    (state : DomainSectionState) :
    EvalsToInTime domainSectionComputer.step
      (domainSectionCfg (some .copyValue) state (bits.map some) [] count work
        scratch output)
      (some (domainSectionCfg (some .restoreIndexEnd) none [] [] count work
        (bits.reverse.map some ++ scratch) output))
      (bits.length + 1) := by
  induction bits generalizing scratch state with
  | nil =>
      simpa using domainSectionEvalsToInTimeOne
        (domainSection_step_copyValue_nil count work scratch output state)
  | cons bit bits ih =>
      have hone := domainSectionEvalsToInTimeOne
        (domainSection_step_copyValue_bit bit (bits.map some) count work
          scratch output state)
      have hrest := ih (some bit :: scratch) (some (some bit))
      have hall := EvalsToInTime.trans domainSectionComputer.step
        1 (bits.length + 1)
        (domainSectionCfg (some .copyValue) state ((bit :: bits).map some) []
          count work scratch output)
        (domainSectionCfg (some .copyValue) (some (some bit)) (bits.map some)
          [] count work (some bit :: scratch) output)
        (some (domainSectionCfg (some .restoreIndexEnd) none [] [] count work
          ((bit :: bits).reverse.map some ++ scratch) output))
        (by simpa using hone)
        (by simpa [List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def domainSection_restoreIndexBoundary_evals
    (work input index count scratch output : List (Option Bool))
    (state : DomainSectionState) :
    EvalsToInTime domainSectionComputer.step
      (domainSectionCfg (some .restoreIndexBoundary) state input index count
        work scratch output)
      (some (domainSectionCfg (some .predBoundary) none input
        (work.reverse ++ index) count [] scratch output))
      (work.length + 1) := by
  induction work generalizing index state with
  | nil =>
      simpa using domainSectionEvalsToInTimeOne
        (domainSection_step_restoreIndexBoundary_nil input index count scratch
          output state)
  | cons symbol work ih =>
      have hone := domainSectionEvalsToInTimeOne
        (domainSection_step_restoreIndexBoundary_cons symbol input index count
          work scratch output state)
      have hrest := ih (symbol :: index) (some symbol)
      have hall := EvalsToInTime.trans domainSectionComputer.step
        1 (work.length + 1)
        (domainSectionCfg (some .restoreIndexBoundary) state input index count
          (symbol :: work) scratch output)
        (domainSectionCfg (some .restoreIndexBoundary) (some symbol) input
          (symbol :: index) count work scratch output)
        (some (domainSectionCfg (some .predBoundary) none input
          ((symbol :: work).reverse ++ index) count [] scratch output))
        (by simpa using hone)
        (by simpa [List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def domainSection_restoreIndexEnd_evals
    (work index count scratch output : List (Option Bool))
    (state : DomainSectionState) :
    EvalsToInTime domainSectionComputer.step
      (domainSectionCfg (some .restoreIndexEnd) state [] index count work
        scratch output)
      (some (domainSectionCfg (some .predEnd) none []
        (work.reverse ++ index) count [] scratch output))
      (work.length + 1) := by
  induction work generalizing index state with
  | nil =>
      simpa using domainSectionEvalsToInTimeOne
        (domainSection_step_restoreIndexEnd_nil index count scratch output
          state)
  | cons symbol work ih =>
      have hone := domainSectionEvalsToInTimeOne
        (domainSection_step_restoreIndexEnd_cons symbol index count work
          scratch output state)
      have hrest := ih (symbol :: index) (some symbol)
      have hall := EvalsToInTime.trans domainSectionComputer.step
        1 (work.length + 1)
        (domainSectionCfg (some .restoreIndexEnd) state [] index count
          (symbol :: work) scratch output)
        (domainSectionCfg (some .restoreIndexEnd) (some symbol) []
          (symbol :: index) count work scratch output)
        (some (domainSectionCfg (some .predEnd) none []
          ((symbol :: work).reverse ++ index) count [] scratch output))
        (by simpa using hone)
        (by simpa [List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def domainSection_predBoundaryRestore_evals
    (work input index count scratch output : List (Option Bool))
    (state : DomainSectionState) :
    EvalsToInTime domainSectionComputer.step
      (domainSectionCfg (some .predBoundaryRestore) state input index count
        work scratch output)
      (some (domainSectionCfg (some .predBoundaryDecide) none input index
        (work.reverse ++ count) [] scratch output))
      (work.length + 1) := by
  induction work generalizing count state with
  | nil =>
      simpa using domainSectionEvalsToInTimeOne
        (domainSection_step_predBoundaryRestore_nil count input index scratch
          output state)
  | cons symbol work ih =>
      have hone := domainSectionEvalsToInTimeOne
        (domainSection_step_predBoundaryRestore_cons symbol count input index
          work scratch output state)
      have hrest := ih (symbol :: count) (some symbol)
      have hall := EvalsToInTime.trans domainSectionComputer.step
        1 (work.length + 1)
        (domainSectionCfg (some .predBoundaryRestore) state input index count
          (symbol :: work) scratch output)
        (domainSectionCfg (some .predBoundaryRestore) (some symbol) input index
          (symbol :: count) work scratch output)
        (some (domainSectionCfg (some .predBoundaryDecide) none input index
          ((symbol :: work).reverse ++ count) [] scratch output))
        (by simpa using hone)
        (by simpa [List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def domainSection_predEndRestore_evals
    (work index count scratch output : List (Option Bool))
    (state : DomainSectionState) :
    EvalsToInTime domainSectionComputer.step
      (domainSectionCfg (some .predEndRestore) state [] index count work
        scratch output)
      (some (domainSectionCfg (some .predEndDecide) none [] index
        (work.reverse ++ count) [] scratch output))
      (work.length + 1) := by
  induction work generalizing count state with
  | nil =>
      simpa using domainSectionEvalsToInTimeOne
        (domainSection_step_predEndRestore_nil count index scratch output state)
  | cons symbol work ih =>
      have hone := domainSectionEvalsToInTimeOne
        (domainSection_step_predEndRestore_cons symbol count index work scratch
          output state)
      have hrest := ih (symbol :: count) (some symbol)
      have hall := EvalsToInTime.trans domainSectionComputer.step
        1 (work.length + 1)
        (domainSectionCfg (some .predEndRestore) state [] index count
          (symbol :: work) scratch output)
        (domainSectionCfg (some .predEndRestore) (some symbol) [] index
          (symbol :: count) work scratch output)
        (some (domainSectionCfg (some .predEndDecide) none [] index
          ((symbol :: work).reverse ++ count) [] scratch output))
        (by simpa using hone)
        (by simpa [List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def domainSection_predBoundary_evals
    (bits acc : List Bool) (input index scratch output : List (Option Bool))
    (state : DomainSectionState) :
    EvalsToInTime domainSectionComputer.step
      (domainSectionCfg (some .predBoundary) state input index (bits.map some)
        (acc.map some) scratch output)
      (some (domainSectionCfg (some .predBoundaryDecide) none input index
        ((acc.reverse ++ binaryPredBits bits).map some) [] scratch output))
      (2 * bits.length + acc.length + 2) := by
  induction bits generalizing acc state with
  | nil =>
      have hone := domainSectionEvalsToInTimeOne
        (domainSection_step_predBoundary_nil input index (acc.map some) scratch
          output state)
      have hrestore := domainSection_predBoundaryRestore_evals
        (acc.map some) input index [] scratch output none
      have hall := EvalsToInTime.trans domainSectionComputer.step
        1 (acc.length + 1)
        (domainSectionCfg (some .predBoundary) state input index []
          (acc.map some) scratch output)
        (domainSectionCfg (some .predBoundaryRestore) none input index []
          (acc.map some) scratch output)
        (some (domainSectionCfg (some .predBoundaryDecide) none input index
          (acc.reverse.map some) [] scratch output))
        (by simpa using hone)
        (by simpa [List.map_reverse] using hrestore)
      simpa [binaryPredBits, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using hall
  | cons bit bits ih =>
      cases bit with
      | false =>
          have hone := domainSectionEvalsToInTimeOne
            (domainSection_step_predBoundary_false (bits.map some) input index
              (acc.map some) scratch output state)
          have hrest := ih (true :: acc) (some (some false))
          have hall := EvalsToInTime.trans domainSectionComputer.step
            1 (2 * bits.length + (true :: acc).length + 2)
            (domainSectionCfg (some .predBoundary) state input index
              ((false :: bits).map some) (acc.map some) scratch output)
            (domainSectionCfg (some .predBoundary) (some (some false)) input
              index (bits.map some) ((true :: acc).map some) scratch output)
            (some (domainSectionCfg (some .predBoundaryDecide) none input index
              (((true :: acc).reverse ++ binaryPredBits bits).map some) []
              scratch output))
            (by exact hone) hrest
          have htime :
              2 * bits.length + (true :: acc).length + 2 + 1 =
                2 * (false :: bits).length + acc.length + 2 := by
            simp
            omega
          rw [htime] at hall
          simpa only [binaryPredBits, List.reverse_cons, List.map_cons,
            List.map_append, List.map_reverse, List.append_assoc] using hall
      | true =>
          have hfirst := domainSectionEvalsToInTimeOne
            (domainSection_step_predBoundary_true (bits.map some) input index
              (acc.map some) scratch output state)
          cases bits with
          | nil =>
              have hcheck := domainSectionEvalsToInTimeOne
                (domainSection_step_predBoundaryCheck_nil input index
                  (acc.map some) scratch output (some (some true)))
              have hprefix := EvalsToInTime.trans domainSectionComputer.step
                1 1
                (domainSectionCfg (some .predBoundary) state input index
                  [some true] (acc.map some) scratch output)
                (domainSectionCfg (some .predBoundaryCheck)
                  (some (some true)) input index [] (acc.map some) scratch
                  output)
                (some (domainSectionCfg (some .predBoundaryRestore) none input
                  index [] (acc.map some) scratch output))
                (by simpa using hfirst) (by simpa using hcheck)
              have hrestore := domainSection_predBoundaryRestore_evals
                (acc.map some) input index [] scratch output none
              have hall := EvalsToInTime.trans domainSectionComputer.step
                2 (acc.length + 1)
                (domainSectionCfg (some .predBoundary) state input index
                  [some true] (acc.map some) scratch output)
                (domainSectionCfg (some .predBoundaryRestore) none input index
                  [] (acc.map some) scratch output)
                (some (domainSectionCfg (some .predBoundaryDecide) none input
                  index (acc.reverse.map some) [] scratch output))
                (by simpa using hprefix)
                (by simpa [List.map_reverse] using hrestore)
              simpa only [List.map_cons, List.map_nil, binaryPredBits,
                List.append_nil] using
                  domainSectionEvalsToInTimeMono hall (by simp; omega)
          | cons next rest =>
              have hcheck := domainSectionEvalsToInTimeOne
                (domainSection_step_predBoundaryCheck_cons (some next)
                  (rest.map some)
                  input index (acc.map some) scratch output
                  (some (some true)))
              have hprefix := EvalsToInTime.trans domainSectionComputer.step
                1 1
                (domainSectionCfg (some .predBoundary) state input index
                  ((true :: next :: rest).map some) (acc.map some) scratch
                  output)
                (domainSectionCfg (some .predBoundaryCheck)
                  (some (some true)) input index ((next :: rest).map some)
                  (acc.map some) scratch output)
                (some (domainSectionCfg (some .predBoundaryRestore)
                  (some (some next)) input index
                  ((false :: next :: rest).map some) (acc.map some) scratch
                  output))
                (by exact hfirst) (by exact hcheck)
              have hrestore := domainSection_predBoundaryRestore_evals
                (acc.map some) input index ((false :: next :: rest).map some)
                scratch output (some (some next))
              have hall := EvalsToInTime.trans domainSectionComputer.step
                2 (acc.length + 1)
                (domainSectionCfg (some .predBoundary) state input index
                  ((true :: next :: rest).map some) (acc.map some) scratch
                  output)
                (domainSectionCfg (some .predBoundaryRestore)
                  (some (some next)) input index
                  ((false :: next :: rest).map some) (acc.map some) scratch
                  output)
                (some (domainSectionCfg (some .predBoundaryDecide) none input
                  index
                  ((acc.reverse ++ false :: next :: rest).map some) []
                  scratch output))
                (by simpa using hprefix)
                (by simpa [List.map_reverse, List.map_append] using hrestore)
              simpa only [List.map_cons, binaryPredBits] using
                domainSectionEvalsToInTimeMono hall (by simp; omega)

private def domainSection_predEnd_evals
    (bits acc : List Bool) (index scratch output : List (Option Bool))
    (state : DomainSectionState) :
    EvalsToInTime domainSectionComputer.step
      (domainSectionCfg (some .predEnd) state [] index (bits.map some)
        (acc.map some) scratch output)
      (some (domainSectionCfg (some .predEndDecide) none [] index
        ((acc.reverse ++ binaryPredBits bits).map some) [] scratch output))
      (2 * bits.length + acc.length + 2) := by
  induction bits generalizing acc state with
  | nil =>
      have hone := domainSectionEvalsToInTimeOne
        (domainSection_step_predEnd_nil index (acc.map some) scratch output
          state)
      have hrestore := domainSection_predEndRestore_evals
        (acc.map some) index [] scratch output none
      have hall := EvalsToInTime.trans domainSectionComputer.step
        1 (acc.length + 1)
        (domainSectionCfg (some .predEnd) state [] index [] (acc.map some)
          scratch output)
        (domainSectionCfg (some .predEndRestore) none [] index []
          (acc.map some) scratch output)
        (some (domainSectionCfg (some .predEndDecide) none [] index
          (acc.reverse.map some) [] scratch output))
        (by simpa using hone)
        (by simpa [List.map_reverse] using hrestore)
      simpa [binaryPredBits, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using hall
  | cons bit bits ih =>
      cases bit with
      | false =>
          have hone := domainSectionEvalsToInTimeOne
            (domainSection_step_predEnd_false (bits.map some) index
              (acc.map some) scratch
              output state)
          have hrest := ih (true :: acc) (some (some false))
          have hall := EvalsToInTime.trans domainSectionComputer.step
            1 (2 * bits.length + (true :: acc).length + 2)
            (domainSectionCfg (some .predEnd) state [] index
              ((false :: bits).map some) (acc.map some) scratch output)
            (domainSectionCfg (some .predEnd) (some (some false)) [] index
              (bits.map some) ((true :: acc).map some) scratch output)
            (some (domainSectionCfg (some .predEndDecide) none [] index
              (((true :: acc).reverse ++ binaryPredBits bits).map some) []
              scratch output))
            (by exact hone) hrest
          have htime :
              2 * bits.length + (true :: acc).length + 2 + 1 =
                2 * (false :: bits).length + acc.length + 2 := by
            simp
            omega
          rw [htime] at hall
          simpa only [binaryPredBits, List.reverse_cons, List.map_cons,
            List.map_append, List.map_reverse, List.append_assoc] using hall
      | true =>
          have hfirst := domainSectionEvalsToInTimeOne
            (domainSection_step_predEnd_true (bits.map some) index
              (acc.map some) scratch
              output state)
          cases bits with
          | nil =>
              have hcheck := domainSectionEvalsToInTimeOne
                (domainSection_step_predEndCheck_nil index (acc.map some)
                  scratch output (some (some true)))
              have hprefix := EvalsToInTime.trans domainSectionComputer.step
                1 1
                (domainSectionCfg (some .predEnd) state [] index [some true]
                  (acc.map some) scratch output)
                (domainSectionCfg (some .predEndCheck) (some (some true)) []
                  index [] (acc.map some) scratch output)
                (some (domainSectionCfg (some .predEndRestore) none [] index
                  [] (acc.map some) scratch output))
                (by simpa using hfirst) (by simpa using hcheck)
              have hrestore := domainSection_predEndRestore_evals
                (acc.map some) index [] scratch output none
              have hall := EvalsToInTime.trans domainSectionComputer.step
                2 (acc.length + 1)
                (domainSectionCfg (some .predEnd) state [] index [some true]
                  (acc.map some) scratch output)
                (domainSectionCfg (some .predEndRestore) none [] index []
                  (acc.map some) scratch output)
                (some (domainSectionCfg (some .predEndDecide) none [] index
                  (acc.reverse.map some) [] scratch output))
                (by simpa using hprefix)
                (by simpa [List.map_reverse] using hrestore)
              simpa only [List.map_cons, List.map_nil, binaryPredBits,
                List.append_nil] using
                  domainSectionEvalsToInTimeMono hall (by simp; omega)
          | cons next rest =>
              have hcheck := domainSectionEvalsToInTimeOne
                (domainSection_step_predEndCheck_cons (some next)
                  (rest.map some) index (acc.map some) scratch output
                  (some (some true)))
              have hprefix := EvalsToInTime.trans domainSectionComputer.step
                1 1
                (domainSectionCfg (some .predEnd) state [] index
                  ((true :: next :: rest).map some) (acc.map some) scratch
                  output)
                (domainSectionCfg (some .predEndCheck) (some (some true)) []
                  index ((next :: rest).map some) (acc.map some) scratch output)
                (some (domainSectionCfg (some .predEndRestore)
                  (some (some next)) [] index
                  ((false :: next :: rest).map some) (acc.map some) scratch
                  output))
                (by exact hfirst) (by exact hcheck)
              have hrestore := domainSection_predEndRestore_evals
                (acc.map some) index ((false :: next :: rest).map some)
                scratch output (some (some next))
              have hall := EvalsToInTime.trans domainSectionComputer.step
                2 (acc.length + 1)
                (domainSectionCfg (some .predEnd) state [] index
                  ((true :: next :: rest).map some) (acc.map some) scratch
                  output)
                (domainSectionCfg (some .predEndRestore)
                  (some (some next)) [] index
                  ((false :: next :: rest).map some) (acc.map some) scratch
                  output)
                (some (domainSectionCfg (some .predEndDecide) none [] index
                  ((acc.reverse ++ false :: next :: rest).map some) [] scratch
                  output))
                (by simpa using hprefix)
                (by simpa [List.map_reverse, List.map_append] using hrestore)
              simpa only [List.map_cons, binaryPredBits] using
                domainSectionEvalsToInTimeMono hall (by simp; omega)

private def domainSection_advanceBoundaryRestore_evals
    (work input index count scratch output : List (Option Bool))
    (state : DomainSectionState) :
    EvalsToInTime domainSectionComputer.step
      (domainSectionCfg (some .advanceBoundaryRestore) state input index count
        work scratch output)
      (some (domainSectionCfg (some .readCount) none input
        (work.reverse ++ index) count [] scratch output))
      (work.length + 1) := by
  induction work generalizing index state with
  | nil =>
      simpa using domainSectionEvalsToInTimeOne
        (domainSection_step_advanceBoundaryRestore_nil index input count
          scratch output state)
  | cons symbol work ih =>
      have hone := domainSectionEvalsToInTimeOne
        (domainSection_step_advanceBoundaryRestore_cons symbol index input
          count work scratch output state)
      have hrest := ih (symbol :: index) (some symbol)
      have hall := EvalsToInTime.trans domainSectionComputer.step
        1 (work.length + 1)
        (domainSectionCfg (some .advanceBoundaryRestore) state input index
          count (symbol :: work) scratch output)
        (domainSectionCfg (some .advanceBoundaryRestore) (some symbol) input
          (symbol :: index) count work scratch output)
        (some (domainSectionCfg (some .readCount) none input
          ((symbol :: work).reverse ++ index) count [] scratch output))
        (by simpa using hone)
        (by simpa [List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def domainSection_advanceEndRestore_evals
    (work index count scratch output : List (Option Bool))
    (state : DomainSectionState) :
    EvalsToInTime domainSectionComputer.step
      (domainSectionCfg (some .advanceEndRestore) state [] index count work
        scratch output)
      (some (domainSectionCfg (some .finish) none []
        (work.reverse ++ index) count [] scratch output))
      (work.length + 1) := by
  induction work generalizing index state with
  | nil =>
      simpa using domainSectionEvalsToInTimeOne
        (domainSection_step_advanceEndRestore_nil index count scratch output
          state)
  | cons symbol work ih =>
      have hone := domainSectionEvalsToInTimeOne
        (domainSection_step_advanceEndRestore_cons symbol index count work
          scratch output state)
      have hrest := ih (symbol :: index) (some symbol)
      have hall := EvalsToInTime.trans domainSectionComputer.step
        1 (work.length + 1)
        (domainSectionCfg (some .advanceEndRestore) state [] index count
          (symbol :: work) scratch output)
        (domainSectionCfg (some .advanceEndRestore) (some symbol) []
          (symbol :: index) count work scratch output)
        (some (domainSectionCfg (some .finish) none []
          ((symbol :: work).reverse ++ index) count [] scratch output))
        (by simpa using hone)
        (by simpa [List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def domainSection_advanceBoundary_evals
    (bits acc : List Bool) (input count scratch output : List (Option Bool))
    (state : DomainSectionState) :
    EvalsToInTime domainSectionComputer.step
      (domainSectionCfg (some .advanceBoundary) state input (bits.map some)
        count (acc.map some) scratch output)
      (some (domainSectionCfg (some .readCount) none input
        ((acc.reverse ++ binarySuccBits bits).map some) count [] scratch output))
      (2 * bits.length + acc.length + 2) := by
  induction bits generalizing acc state with
  | nil =>
      have hone := domainSectionEvalsToInTimeOne
        (domainSection_step_advanceBoundary_nil input count (acc.map some)
          scratch output state)
      have hrestore := domainSection_advanceBoundaryRestore_evals
        (acc.map some) input [some true] count scratch output none
      have hall := EvalsToInTime.trans domainSectionComputer.step
        1 (acc.length + 1)
        (domainSectionCfg (some .advanceBoundary) state input [] count
          (acc.map some) scratch output)
        (domainSectionCfg (some .advanceBoundaryRestore) none input
          [some true] count (acc.map some) scratch output)
        (some (domainSectionCfg (some .readCount) none input
          ((acc.reverse ++ [true]).map some) count [] scratch output))
        (by simpa using hone)
        (by simpa [List.map_reverse, List.map_append] using hrestore)
      simpa [binarySuccBits, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using hall
  | cons bit bits ih =>
      cases bit with
      | false =>
          have hone := domainSectionEvalsToInTimeOne
            (domainSection_step_advanceBoundary_false (bits.map some) input
              count (acc.map some) scratch output state)
          have hrestore := domainSection_advanceBoundaryRestore_evals
            (acc.map some) input (some true :: bits.map some) count scratch
            output (some (some false))
          have hall := EvalsToInTime.trans domainSectionComputer.step
            1 (acc.length + 1)
            (domainSectionCfg (some .advanceBoundary) state input
              ((false :: bits).map some) count (acc.map some) scratch output)
            (domainSectionCfg (some .advanceBoundaryRestore)
              (some (some false)) input (some true :: bits.map some) count
              (acc.map some) scratch output)
            (some (domainSectionCfg (some .readCount) none input
              ((acc.reverse ++ true :: bits).map some) count [] scratch output))
            (by exact hone)
            (by simpa [List.map_reverse, List.map_append] using hrestore)
          simpa only [List.map_cons, binarySuccBits] using
            domainSectionEvalsToInTimeMono hall (by simp)
      | true =>
          have hone := domainSectionEvalsToInTimeOne
            (domainSection_step_advanceBoundary_true (bits.map some) input
              count (acc.map some) scratch output state)
          have hrest := ih (false :: acc) (some (some true))
          have hall := EvalsToInTime.trans domainSectionComputer.step
            1 (2 * bits.length + (false :: acc).length + 2)
            (domainSectionCfg (some .advanceBoundary) state input
              ((true :: bits).map some) count (acc.map some) scratch output)
            (domainSectionCfg (some .advanceBoundary) (some (some true)) input
              (bits.map some) count ((false :: acc).map some) scratch output)
            (some (domainSectionCfg (some .readCount) none input
              (((false :: acc).reverse ++ binarySuccBits bits).map some)
              count [] scratch output))
            (by exact hone) hrest
          have htime :
              2 * bits.length + (false :: acc).length + 2 + 1 =
                2 * (true :: bits).length + acc.length + 2 := by
            simp
            omega
          rw [htime] at hall
          simpa only [binarySuccBits, List.reverse_cons, List.map_cons,
            List.map_append, List.map_reverse, List.append_assoc] using hall

private def domainSection_advanceEnd_evals
    (bits acc : List Bool) (count scratch output : List (Option Bool))
    (state : DomainSectionState) :
    EvalsToInTime domainSectionComputer.step
      (domainSectionCfg (some .advanceEnd) state [] (bits.map some) count
        (acc.map some) scratch output)
      (some (domainSectionCfg (some .finish) none []
        ((acc.reverse ++ binarySuccBits bits).map some) count [] scratch output))
      (2 * bits.length + acc.length + 2) := by
  induction bits generalizing acc state with
  | nil =>
      have hone := domainSectionEvalsToInTimeOne
        (domainSection_step_advanceEnd_nil count (acc.map some) scratch output
          state)
      have hrestore := domainSection_advanceEndRestore_evals
        (acc.map some) [some true] count scratch output none
      have hall := EvalsToInTime.trans domainSectionComputer.step
        1 (acc.length + 1)
        (domainSectionCfg (some .advanceEnd) state [] [] count (acc.map some)
          scratch output)
        (domainSectionCfg (some .advanceEndRestore) none [] [some true] count
          (acc.map some) scratch output)
        (some (domainSectionCfg (some .finish) none []
          ((acc.reverse ++ [true]).map some) count [] scratch output))
        (by simpa using hone)
        (by simpa [List.map_reverse, List.map_append] using hrestore)
      simpa [binarySuccBits, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using hall
  | cons bit bits ih =>
      cases bit with
      | false =>
          have hone := domainSectionEvalsToInTimeOne
            (domainSection_step_advanceEnd_false (bits.map some) count
              (acc.map some) scratch output state)
          have hrestore := domainSection_advanceEndRestore_evals
            (acc.map some) (some true :: bits.map some) count scratch output
            (some (some false))
          have hall := EvalsToInTime.trans domainSectionComputer.step
            1 (acc.length + 1)
            (domainSectionCfg (some .advanceEnd) state []
              ((false :: bits).map some) count (acc.map some) scratch output)
            (domainSectionCfg (some .advanceEndRestore) (some (some false)) []
              (some true :: bits.map some) count (acc.map some) scratch output)
            (some (domainSectionCfg (some .finish) none []
              ((acc.reverse ++ true :: bits).map some) count [] scratch output))
            (by exact hone)
            (by simpa [List.map_reverse, List.map_append] using hrestore)
          simpa only [List.map_cons, binarySuccBits] using
            domainSectionEvalsToInTimeMono hall (by simp)
      | true =>
          have hone := domainSectionEvalsToInTimeOne
            (domainSection_step_advanceEnd_true (bits.map some) count
              (acc.map some) scratch output state)
          have hrest := ih (false :: acc) (some (some true))
          have hall := EvalsToInTime.trans domainSectionComputer.step
            1 (2 * bits.length + (false :: acc).length + 2)
            (domainSectionCfg (some .advanceEnd) state []
              ((true :: bits).map some) count (acc.map some) scratch output)
            (domainSectionCfg (some .advanceEnd) (some (some true)) []
              (bits.map some) count ((false :: acc).map some) scratch output)
            (some (domainSectionCfg (some .finish) none []
              (((false :: acc).reverse ++ binarySuccBits bits).map some) count
              [] scratch output))
            (by exact hone) hrest
          have htime :
              2 * bits.length + (false :: acc).length + 2 + 1 =
                2 * (true :: bits).length + acc.length + 2 := by
            simp
            omega
          rw [htime] at hall
          simpa only [binarySuccBits, List.reverse_cons, List.map_cons,
            List.map_append, List.map_reverse, List.append_assoc] using hall

private def domainSection_finish_evals
    (scratch output index : List (Option Bool)) (state : DomainSectionState) :
    EvalsToInTime domainSectionComputer.step
      (domainSectionCfg (some .finish) state [] index [] [] scratch output)
      (some (domainSectionCfg (some .clearIndex) none [] index [] [] []
        (scratch.reverse ++ output)))
      (scratch.length + 1) := by
  induction scratch generalizing output state with
  | nil =>
      simpa using domainSectionEvalsToInTimeOne
        (domainSection_step_finish_nil index [] [] output state)
  | cons symbol scratch ih =>
      have hone := domainSectionEvalsToInTimeOne
        (domainSection_step_finish_cons symbol index [] [] scratch output state)
      have hrest := ih (symbol :: output) (some symbol)
      have hall := EvalsToInTime.trans domainSectionComputer.step
        1 (scratch.length + 1)
        (domainSectionCfg (some .finish) state [] index [] []
          (symbol :: scratch) output)
        (domainSectionCfg (some .finish) (some symbol) [] index [] [] scratch
          (symbol :: output))
        (some (domainSectionCfg (some .clearIndex) none [] index [] [] []
          ((symbol :: scratch).reverse ++ output)))
        (by simpa using hone)
        (by simpa [List.reverse_cons, List.append_assoc] using hrest)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def domainSection_clearIndex_evals
    (index output : List (Option Bool)) (state : DomainSectionState) :
    EvalsToInTime domainSectionComputer.step
      (domainSectionCfg (some .clearIndex) state [] index [] [] [] output)
      (some (domainSectionCfg none none [] [] [] [] [] output))
      (index.length + 1) := by
  induction index generalizing state with
  | nil =>
      simpa using domainSectionEvalsToInTimeOne
        (domainSection_step_clearIndex_nil [] [] output state)
  | cons symbol index ih =>
      have hone := domainSectionEvalsToInTimeOne
        (domainSection_step_clearIndex_cons symbol index [] [] output state)
      have hrest := ih (some symbol)
      exact EvalsToInTime.trans domainSectionComputer.step
        1 (index.length + 1)
        (domainSectionCfg (some .clearIndex) state [] (symbol :: index) [] []
          [] output)
        (domainSectionCfg (some .clearIndex) (some symbol) [] index [] [] []
          output)
        (some (domainSectionCfg none none [] [] [] [] [] output))
        (by simpa using hone) hrest

private theorem domainSection_block_reverse_append
    (index value : ℕ) (scratch : List (Option Bool)) :
    (DomainOccurrenceFieldBlock.outputEncode (index, value)).reverse ++
        scratch =
      (encodeNat value).reverse.map some ++
        none :: (encodeNat index).reverse.map some ++
          none :: none :: some true :: some true :: none :: scratch := by
  rw [DomainOccurrenceFieldBlock.outputEncode_eq_prefix]
  simp [DomainOccurrenceFieldBlock.inputEncode,
    DomainOccurrenceFieldBlock.headerPrefix, SourceOrderRawFields.encode,
    List.reverse_append, List.map_reverse, List.append_assoc]

private theorem domainSection_occurrences_cons_reverse_append
    (index value : ℕ) (values : List ℕ)
    (scratch : List (Option Bool)) :
    (DomainFieldRow.outputEncode
        (DomainFieldRow.occurrences (index, value :: values))).reverse ++
        scratch =
      (DomainFieldRow.outputEncode
        (DomainFieldRow.occurrences (index, values))).reverse ++
        (DomainOccurrenceFieldBlock.outputEncode (index, value)).reverse ++
          scratch := by
  simp [DomainFieldRow.outputEncode, DomainFieldRow.occurrences,
    List.reverse_append, List.append_assoc]

private def domainSection_valueBoundary_evals
    (index value : ℕ) (tail : List (Option Bool))
    (count scratch output : List (Option Bool)) (state : DomainSectionState) :
    EvalsToInTime domainSectionComputer.step
      (domainSectionCfg (some .beginValue) state
        ((encodeNat value).map some ++ none :: tail)
        ((encodeNat index).map some) count [] scratch output)
      (some (domainSectionCfg (some .predBoundary) none tail
        ((encodeNat index).map some) count []
        ((DomainOccurrenceFieldBlock.outputEncode
          (index, value)).reverse ++ scratch) output))
      (2 * (encodeNat index).length + (encodeNat value).length + 4) := by
  let prefixScratch : List (Option Bool) :=
    none :: none :: some true :: some true :: none :: scratch
  have hbegin := domainSectionEvalsToInTimeOne
    (domainSection_step_beginValue
      ((encodeNat value).map some ++ none :: tail)
      ((encodeNat index).map some) count [] scratch output state)
  have hindex := domainSection_copyIndex_evals
    ((encodeNat index).map some)
    ((encodeNat value).map some ++ none :: tail) count [] prefixScratch output
    state
  have hfirst := EvalsToInTime.trans domainSectionComputer.step
    1 ((encodeNat index).length + 1)
    (domainSectionCfg (some .beginValue) state
      ((encodeNat value).map some ++ none :: tail)
      ((encodeNat index).map some) count [] scratch output)
    (domainSectionCfg (some .copyIndex) state
      ((encodeNat value).map some ++ none :: tail)
      ((encodeNat index).map some) count [] prefixScratch output)
    (some (domainSectionCfg (some .copyValue) none
      ((encodeNat value).map some ++ none :: tail) [] count
      ((encodeNat index).reverse.map some)
      (none :: (encodeNat index).reverse.map some ++ prefixScratch) output))
    (by simpa [prefixScratch] using hbegin)
    (by simpa [prefixScratch, List.map_reverse] using hindex)
  have hvalue := domainSection_copyValueBoundary_evals
    (encodeNat value) tail count ((encodeNat index).reverse.map some)
    (none :: (encodeNat index).reverse.map some ++ prefixScratch) output none
  have hthroughValue := EvalsToInTime.trans domainSectionComputer.step
    ((encodeNat index).length + 2) ((encodeNat value).length + 1)
    (domainSectionCfg (some .beginValue) state
      ((encodeNat value).map some ++ none :: tail)
      ((encodeNat index).map some) count [] scratch output)
    (domainSectionCfg (some .copyValue) none
      ((encodeNat value).map some ++ none :: tail) [] count
      ((encodeNat index).reverse.map some)
      (none :: (encodeNat index).reverse.map some ++ prefixScratch) output)
    (some (domainSectionCfg (some .restoreIndexBoundary) (some none) tail []
      count ((encodeNat index).reverse.map some)
      ((encodeNat value).reverse.map some ++
        none :: (encodeNat index).reverse.map some ++ prefixScratch) output))
    (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfirst)
    (by simpa using hvalue)
  have hrestore := domainSection_restoreIndexBoundary_evals
    ((encodeNat index).reverse.map some) tail [] count
    ((encodeNat value).reverse.map some ++
      none :: (encodeNat index).reverse.map some ++ prefixScratch) output
    (some none)
  have hall := EvalsToInTime.trans domainSectionComputer.step
    ((encodeNat value).length + 1 + ((encodeNat index).length + 2))
    ((encodeNat index).length + 1)
    (domainSectionCfg (some .beginValue) state
      ((encodeNat value).map some ++ none :: tail)
      ((encodeNat index).map some) count [] scratch output)
    (domainSectionCfg (some .restoreIndexBoundary) (some none) tail [] count
      ((encodeNat index).reverse.map some)
      ((encodeNat value).reverse.map some ++
        none :: (encodeNat index).reverse.map some ++ prefixScratch) output)
    (some (domainSectionCfg (some .predBoundary) none tail
      ((encodeNat index).map some) count []
      ((encodeNat value).reverse.map some ++
        none :: (encodeNat index).reverse.map some ++ prefixScratch) output))
    (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hthroughValue)
    (by simpa [List.map_reverse] using hrestore)
  have htime :
      (encodeNat index).length + 1 +
          ((encodeNat value).length + 1 + ((encodeNat index).length + 2)) =
        2 * (encodeNat index).length + (encodeNat value).length + 4 := by
    omega
  rw [htime] at hall
  rw [domainSection_block_reverse_append index value scratch]
  simpa [prefixScratch, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using hall

private def domainSection_valueEnd_evals
    (index value : ℕ) (count scratch output : List (Option Bool))
    (state : DomainSectionState) :
    EvalsToInTime domainSectionComputer.step
      (domainSectionCfg (some .beginValue) state
        ((encodeNat value).map some) ((encodeNat index).map some) count []
        scratch output)
      (some (domainSectionCfg (some .predEnd) none []
        ((encodeNat index).map some) count []
        ((DomainOccurrenceFieldBlock.outputEncode
          (index, value)).reverse ++ scratch) output))
      (2 * (encodeNat index).length + (encodeNat value).length + 4) := by
  let prefixScratch : List (Option Bool) :=
    none :: none :: some true :: some true :: none :: scratch
  have hbegin := domainSectionEvalsToInTimeOne
    (domainSection_step_beginValue ((encodeNat value).map some)
      ((encodeNat index).map some) count [] scratch output state)
  have hindex := domainSection_copyIndex_evals
    ((encodeNat index).map some) ((encodeNat value).map some) count []
    prefixScratch output state
  have hfirst := EvalsToInTime.trans domainSectionComputer.step
    1 ((encodeNat index).length + 1)
    (domainSectionCfg (some .beginValue) state ((encodeNat value).map some)
      ((encodeNat index).map some) count [] scratch output)
    (domainSectionCfg (some .copyIndex) state ((encodeNat value).map some)
      ((encodeNat index).map some) count [] prefixScratch output)
    (some (domainSectionCfg (some .copyValue) none
      ((encodeNat value).map some) [] count
      ((encodeNat index).reverse.map some)
      (none :: (encodeNat index).reverse.map some ++ prefixScratch) output))
    (by simpa [prefixScratch] using hbegin)
    (by simpa [prefixScratch, List.map_reverse] using hindex)
  have hvalue := domainSection_copyValueEnd_evals
    (encodeNat value) count ((encodeNat index).reverse.map some)
    (none :: (encodeNat index).reverse.map some ++ prefixScratch) output none
  have hthroughValue := EvalsToInTime.trans domainSectionComputer.step
    ((encodeNat index).length + 2) ((encodeNat value).length + 1)
    (domainSectionCfg (some .beginValue) state ((encodeNat value).map some)
      ((encodeNat index).map some) count [] scratch output)
    (domainSectionCfg (some .copyValue) none ((encodeNat value).map some) []
      count ((encodeNat index).reverse.map some)
      (none :: (encodeNat index).reverse.map some ++ prefixScratch) output)
    (some (domainSectionCfg (some .restoreIndexEnd) none [] [] count
      ((encodeNat index).reverse.map some)
      ((encodeNat value).reverse.map some ++
        none :: (encodeNat index).reverse.map some ++ prefixScratch) output))
    (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfirst)
    (by simpa using hvalue)
  have hrestore := domainSection_restoreIndexEnd_evals
    ((encodeNat index).reverse.map some) [] count
    ((encodeNat value).reverse.map some ++
      none :: (encodeNat index).reverse.map some ++ prefixScratch) output none
  have hall := EvalsToInTime.trans domainSectionComputer.step
    ((encodeNat value).length + 1 + ((encodeNat index).length + 2))
    ((encodeNat index).length + 1)
    (domainSectionCfg (some .beginValue) state ((encodeNat value).map some)
      ((encodeNat index).map some) count [] scratch output)
    (domainSectionCfg (some .restoreIndexEnd) none [] [] count
      ((encodeNat index).reverse.map some)
      ((encodeNat value).reverse.map some ++
        none :: (encodeNat index).reverse.map some ++ prefixScratch) output)
    (some (domainSectionCfg (some .predEnd) none []
      ((encodeNat index).map some) count []
      ((encodeNat value).reverse.map some ++
        none :: (encodeNat index).reverse.map some ++ prefixScratch) output))
    (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hthroughValue)
    (by simpa [List.map_reverse] using hrestore)
  have htime :
      (encodeNat index).length + 1 +
          ((encodeNat value).length + 1 + ((encodeNat index).length + 2)) =
        2 * (encodeNat index).length + (encodeNat value).length + 4 := by
    omega
  rw [htime] at hall
  rw [domainSection_block_reverse_append index value scratch]
  simpa [prefixScratch, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using hall

/-- Source bits for one or more row values after the first value delimiter has
already been consumed, with a final delimiter before the following row. -/
private def domainSectionBoundaryValues : List ℕ → List (Option Bool) →
    List (Option Bool)
  | [], after => after
  | value :: values, after =>
      (encodeNat value).map some ++ none ::
        domainSectionBoundaryValues values after

/-- Source bits for the final nonempty row after its first value delimiter has
already been consumed. -/
private def domainSectionEndValues : List ℕ → List (Option Bool)
  | [] => []
  | value :: values =>
      (encodeNat value).map some ++
        match values with
        | [] => []
        | _ :: _ => none :: domainSectionEndValues values

private def domainSectionValueWork (index value : ℕ) : ℕ :=
  2 * (encodeNat index).length + (encodeNat value).length + 4

private def domainSectionPredWork (count : ℕ) : ℕ :=
  2 * (encodeNat count).length + 3

private def domainSectionSuccWork (index : ℕ) : ℕ :=
  2 * (encodeNat index).length + 2

/-- Exact compositional budget for a nonempty row followed by another row. -/
private def domainSectionValuesBoundaryTime (index : ℕ) : List ℕ → ℕ
  | [] => 0
  | value :: [] =>
      domainSectionValueWork index value + domainSectionPredWork 1 +
        domainSectionSuccWork index
  | value :: next :: values =>
      domainSectionValueWork index value +
        domainSectionPredWork (value :: next :: values).length +
          domainSectionValuesBoundaryTime index (next :: values)

/-- Exact compositional budget for the final nonempty row. -/
private def domainSectionValuesEndTime (index : ℕ) : List ℕ → ℕ
  | [] => 0
  | value :: [] =>
      domainSectionValueWork index value + domainSectionPredWork 1 +
        domainSectionSuccWork index
  | value :: next :: values =>
      domainSectionValueWork index value +
        domainSectionPredWork (value :: next :: values).length +
          domainSectionValuesEndTime index (next :: values)

private theorem encodeNat_succ_ne_nil (n : ℕ) :
    encodeNat (n + 1) ≠ [] := by
  intro h
  have hdecode := congrArg decodeNat h
  have hzero : decodeNat [] = 0 := by rfl
  have : n + 1 = 0 := by simpa [hzero] using hdecode
  omega

private theorem encodeNat_zero : encodeNat 0 = [] := by
  unfold encodeNat
  change encodeNum (Num.ofNat' 0) = []
  rw [Num.ofNat'_zero]
  rfl

private def domainSection_valuesBoundary_evals
    (index value : ℕ) (values : List ℕ) (after : List (Option Bool))
    (scratch output : List (Option Bool)) (state : DomainSectionState) :
    EvalsToInTime domainSectionComputer.step
      (domainSectionCfg (some .beginValue) state
        (domainSectionBoundaryValues (value :: values) after)
        ((encodeNat index).map some)
        ((encodeNat (value :: values).length).map some) [] scratch output)
      (some (domainSectionCfg (some .readCount) none after
        ((encodeNat (index + 1)).map some) [] []
        ((DomainFieldRow.outputEncode
          (DomainFieldRow.occurrences
            (index, value :: values))).reverse ++ scratch) output))
      (domainSectionValuesBoundaryTime index (value :: values)) := by
  cases values with
  | nil =>
      have hvalue := domainSection_valueBoundary_evals index value after
        ((encodeNat 1).map some) scratch output state
      have hpred := domainSection_predBoundary_evals
        (encodeNat 1) [] after ((encodeNat index).map some)
        ((DomainOccurrenceFieldBlock.outputEncode
          (index, value)).reverse ++ scratch) output none
      have hthroughPred := EvalsToInTime.trans domainSectionComputer.step
        (domainSectionValueWork index value)
        (2 * (encodeNat 1).length + 2)
        (domainSectionCfg (some .beginValue) state
          (domainSectionBoundaryValues [value] after)
          ((encodeNat index).map some) ((encodeNat 1).map some) [] scratch
          output)
        (domainSectionCfg (some .predBoundary) none after
          ((encodeNat index).map some) ((encodeNat 1).map some) []
          ((DomainOccurrenceFieldBlock.outputEncode
            (index, value)).reverse ++ scratch) output)
        (some (domainSectionCfg (some .predBoundaryDecide) none after
          ((encodeNat index).map some) [] []
          ((DomainOccurrenceFieldBlock.outputEncode
            (index, value)).reverse ++ scratch) output))
        (by simpa [domainSectionBoundaryValues, domainSectionValueWork] using
          hvalue)
        (by simpa [encodeNat_zero] using hpred)
      have hdecide := domainSectionEvalsToInTimeOne
        (domainSection_step_predBoundaryDecide_nil after
          ((encodeNat index).map some) []
          ((DomainOccurrenceFieldBlock.outputEncode
            (index, value)).reverse ++ scratch) output none)
      have hthroughDecide := EvalsToInTime.trans domainSectionComputer.step
        (2 * (encodeNat 1).length + 2 + domainSectionValueWork index value) 1
        (domainSectionCfg (some .beginValue) state
          (domainSectionBoundaryValues [value] after)
          ((encodeNat index).map some) ((encodeNat 1).map some) [] scratch
          output)
        (domainSectionCfg (some .predBoundaryDecide) none after
          ((encodeNat index).map some) [] []
          ((DomainOccurrenceFieldBlock.outputEncode
            (index, value)).reverse ++ scratch) output)
        (some (domainSectionCfg (some .advanceBoundary) none after
          ((encodeNat index).map some) [] []
          ((DomainOccurrenceFieldBlock.outputEncode
            (index, value)).reverse ++ scratch) output))
        (by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hthroughPred)
        (by simpa using hdecide)
      have hsucc := domainSection_advanceBoundary_evals
        (encodeNat index) [] after []
        ((DomainOccurrenceFieldBlock.outputEncode
          (index, value)).reverse ++ scratch) output none
      have hall := EvalsToInTime.trans domainSectionComputer.step
        (2 * (encodeNat 1).length + 3 + domainSectionValueWork index value)
        (domainSectionSuccWork index)
        (domainSectionCfg (some .beginValue) state
          (domainSectionBoundaryValues [value] after)
          ((encodeNat index).map some) ((encodeNat 1).map some) [] scratch
          output)
        (domainSectionCfg (some .advanceBoundary) none after
          ((encodeNat index).map some) [] []
          ((DomainOccurrenceFieldBlock.outputEncode
            (index, value)).reverse ++ scratch) output)
        (some (domainSectionCfg (some .readCount) none after
          ((encodeNat (index + 1)).map some) [] []
          ((DomainOccurrenceFieldBlock.outputEncode
            (index, value)).reverse ++ scratch) output))
        (by
          have htime :
              1 + (2 * (encodeNat 1).length + 2 +
                domainSectionValueWork index value) =
                2 * (encodeNat 1).length + 3 +
                  domainSectionValueWork index value := by
            omega
          rw [htime] at hthroughDecide
          exact hthroughDecide)
        (by
          simpa [domainSectionSuccWork, binarySuccBits_encodeNat] using hsucc)
      simpa [domainSectionValuesBoundaryTime, domainSectionPredWork,
        DomainFieldRow.outputEncode, DomainFieldRow.occurrences,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall
  | cons next values =>
      let restInput := domainSectionBoundaryValues (next :: values) after
      have hvalue := domainSection_valueBoundary_evals index value restInput
        ((encodeNat (value :: next :: values).length).map some) scratch output
        state
      have hpred := domainSection_predBoundary_evals
        (encodeNat (value :: next :: values).length) [] restInput
        ((encodeNat index).map some)
        ((DomainOccurrenceFieldBlock.outputEncode
          (index, value)).reverse ++ scratch) output none
      have hthroughPred := EvalsToInTime.trans domainSectionComputer.step
        (domainSectionValueWork index value)
        (2 * (encodeNat (value :: next :: values).length).length + 2)
        (domainSectionCfg (some .beginValue) state
          (domainSectionBoundaryValues (value :: next :: values) after)
          ((encodeNat index).map some)
          ((encodeNat (value :: next :: values).length).map some) [] scratch
          output)
        (domainSectionCfg (some .predBoundary) none restInput
          ((encodeNat index).map some)
          ((encodeNat (value :: next :: values).length).map some) []
          ((DomainOccurrenceFieldBlock.outputEncode
            (index, value)).reverse ++ scratch) output)
        (some (domainSectionCfg (some .predBoundaryDecide) none restInput
          ((encodeNat index).map some)
          ((encodeNat (next :: values).length).map some) []
          ((DomainOccurrenceFieldBlock.outputEncode
            (index, value)).reverse ++ scratch) output))
        (by simpa [domainSectionBoundaryValues, restInput,
          domainSectionValueWork] using hvalue)
        (by simpa [binaryPredBits_encodeNat] using hpred)
      have hnonempty := encodeNat_succ_ne_nil values.length
      cases hbits : encodeNat (next :: values).length with
      | nil =>
          exfalso
          apply hnonempty
          simpa using hbits
      | cons bit bits =>
          have hdecide := domainSectionEvalsToInTimeOne
            (domainSection_step_predBoundaryDecide_cons (some bit)
              (bits.map some) restInput ((encodeNat index).map some) []
              ((DomainOccurrenceFieldBlock.outputEncode
                (index, value)).reverse ++ scratch) output none)
          have hthroughDecide := EvalsToInTime.trans
            domainSectionComputer.step
            (2 * (encodeNat (value :: next :: values).length).length + 2 +
              domainSectionValueWork index value) 1
            (domainSectionCfg (some .beginValue) state
              (domainSectionBoundaryValues (value :: next :: values) after)
              ((encodeNat index).map some)
              ((encodeNat (value :: next :: values).length).map some) []
              scratch output)
            (domainSectionCfg (some .predBoundaryDecide) none restInput
              ((encodeNat index).map some)
              ((encodeNat (next :: values).length).map some) []
              ((DomainOccurrenceFieldBlock.outputEncode
                (index, value)).reverse ++ scratch) output)
            (some (domainSectionCfg (some .beginValue) (some (some bit))
              restInput ((encodeNat index).map some)
              ((encodeNat (next :: values).length).map some) []
              ((DomainOccurrenceFieldBlock.outputEncode
                (index, value)).reverse ++ scratch) output))
            (by
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                hthroughPred)
            (by
              rw [hbits]
              exact hdecide)
          have hrest := domainSection_valuesBoundary_evals index next values
            after
            ((DomainOccurrenceFieldBlock.outputEncode
              (index, value)).reverse ++ scratch) output (some (some bit))
          have hall := EvalsToInTime.trans domainSectionComputer.step
            (2 * (encodeNat (value :: next :: values).length).length + 3 +
              domainSectionValueWork index value)
            (domainSectionValuesBoundaryTime index (next :: values))
            (domainSectionCfg (some .beginValue) state
              (domainSectionBoundaryValues (value :: next :: values) after)
              ((encodeNat index).map some)
              ((encodeNat (value :: next :: values).length).map some) []
              scratch output)
            (domainSectionCfg (some .beginValue) (some (some bit)) restInput
              ((encodeNat index).map some)
              ((encodeNat (next :: values).length).map some) []
              ((DomainOccurrenceFieldBlock.outputEncode
                (index, value)).reverse ++ scratch) output)
            (some (domainSectionCfg (some .readCount) none after
              ((encodeNat (index + 1)).map some) [] []
              ((DomainFieldRow.outputEncode
                (DomainFieldRow.occurrences
                  (index, value :: next :: values))).reverse ++ scratch)
              output))
            (by
              have htime :
                  1 +
                      (2 *
                          (encodeNat
                            (value :: next :: values).length).length +
                        2 + domainSectionValueWork index value) =
                    2 *
                        (encodeNat (value :: next :: values).length).length +
                      3 + domainSectionValueWork index value := by
                omega
              rw [htime] at hthroughDecide
              exact hthroughDecide)
            (by
              rw [domainSection_occurrences_cons_reverse_append]
              simpa [restInput, List.append_assoc] using hrest)
          simpa [domainSectionValuesBoundaryTime, domainSectionPredWork,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

private def domainSection_valuesEnd_evals
    (index value : ℕ) (values : List ℕ)
    (scratch output : List (Option Bool)) (state : DomainSectionState) :
    EvalsToInTime domainSectionComputer.step
      (domainSectionCfg (some .beginValue) state
        (domainSectionEndValues (value :: values))
        ((encodeNat index).map some)
        ((encodeNat (value :: values).length).map some) [] scratch output)
      (some (domainSectionCfg (some .finish) none []
        ((encodeNat (index + 1)).map some) [] []
        ((DomainFieldRow.outputEncode
          (DomainFieldRow.occurrences
            (index, value :: values))).reverse ++ scratch) output))
      (domainSectionValuesEndTime index (value :: values)) := by
  cases values with
  | nil =>
      have hvalue := domainSection_valueEnd_evals index value
        ((encodeNat 1).map some) scratch output state
      have hpred := domainSection_predEnd_evals
        (encodeNat 1) [] ((encodeNat index).map some)
        ((DomainOccurrenceFieldBlock.outputEncode
          (index, value)).reverse ++ scratch) output none
      have hthroughPred := EvalsToInTime.trans domainSectionComputer.step
        (domainSectionValueWork index value)
        (2 * (encodeNat 1).length + 2)
        (domainSectionCfg (some .beginValue) state
          (domainSectionEndValues [value])
          ((encodeNat index).map some) ((encodeNat 1).map some) [] scratch
          output)
        (domainSectionCfg (some .predEnd) none []
          ((encodeNat index).map some) ((encodeNat 1).map some) []
          ((DomainOccurrenceFieldBlock.outputEncode
            (index, value)).reverse ++ scratch) output)
        (some (domainSectionCfg (some .predEndDecide) none []
          ((encodeNat index).map some) [] []
          ((DomainOccurrenceFieldBlock.outputEncode
            (index, value)).reverse ++ scratch) output))
        (by simpa [domainSectionEndValues, domainSectionValueWork] using hvalue)
        (by simpa [encodeNat_zero] using hpred)
      have hdecide := domainSectionEvalsToInTimeOne
        (domainSection_step_predEndDecide_nil ((encodeNat index).map some) []
          ((DomainOccurrenceFieldBlock.outputEncode
            (index, value)).reverse ++ scratch) output none)
      have hthroughDecide := EvalsToInTime.trans domainSectionComputer.step
        (2 * (encodeNat 1).length + 2 + domainSectionValueWork index value) 1
        (domainSectionCfg (some .beginValue) state
          (domainSectionEndValues [value])
          ((encodeNat index).map some) ((encodeNat 1).map some) [] scratch
          output)
        (domainSectionCfg (some .predEndDecide) none []
          ((encodeNat index).map some) [] []
          ((DomainOccurrenceFieldBlock.outputEncode
            (index, value)).reverse ++ scratch) output)
        (some (domainSectionCfg (some .advanceEnd) none []
          ((encodeNat index).map some) [] []
          ((DomainOccurrenceFieldBlock.outputEncode
            (index, value)).reverse ++ scratch) output))
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hthroughPred)
        (by simpa using hdecide)
      have hsucc := domainSection_advanceEnd_evals
        (encodeNat index) [] []
        ((DomainOccurrenceFieldBlock.outputEncode
          (index, value)).reverse ++ scratch) output none
      have hall := EvalsToInTime.trans domainSectionComputer.step
        (2 * (encodeNat 1).length + 3 + domainSectionValueWork index value)
        (domainSectionSuccWork index)
        (domainSectionCfg (some .beginValue) state
          (domainSectionEndValues [value])
          ((encodeNat index).map some) ((encodeNat 1).map some) [] scratch
          output)
        (domainSectionCfg (some .advanceEnd) none []
          ((encodeNat index).map some) [] []
          ((DomainOccurrenceFieldBlock.outputEncode
            (index, value)).reverse ++ scratch) output)
        (some (domainSectionCfg (some .finish) none []
          ((encodeNat (index + 1)).map some) [] []
          ((DomainOccurrenceFieldBlock.outputEncode
            (index, value)).reverse ++ scratch) output))
        (by
          have htime :
              1 + (2 * (encodeNat 1).length + 2 +
                domainSectionValueWork index value) =
                2 * (encodeNat 1).length + 3 +
                  domainSectionValueWork index value := by
            omega
          rw [htime] at hthroughDecide
          exact hthroughDecide)
        (by simpa [domainSectionSuccWork, binarySuccBits_encodeNat] using
          hsucc)
      simpa [domainSectionValuesEndTime, domainSectionPredWork,
        DomainFieldRow.outputEncode, DomainFieldRow.occurrences,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall
  | cons next values =>
      let restInput := domainSectionEndValues (next :: values)
      have hvalue := domainSection_valueBoundary_evals index value restInput
        ((encodeNat (value :: next :: values).length).map some) scratch output
        state
      have hpred := domainSection_predBoundary_evals
        (encodeNat (value :: next :: values).length) [] restInput
        ((encodeNat index).map some)
        ((DomainOccurrenceFieldBlock.outputEncode
          (index, value)).reverse ++ scratch) output none
      have hthroughPred := EvalsToInTime.trans domainSectionComputer.step
        (domainSectionValueWork index value)
        (2 * (encodeNat (value :: next :: values).length).length + 2)
        (domainSectionCfg (some .beginValue) state
          (domainSectionEndValues (value :: next :: values))
          ((encodeNat index).map some)
          ((encodeNat (value :: next :: values).length).map some) [] scratch
          output)
        (domainSectionCfg (some .predBoundary) none restInput
          ((encodeNat index).map some)
          ((encodeNat (value :: next :: values).length).map some) []
          ((DomainOccurrenceFieldBlock.outputEncode
            (index, value)).reverse ++ scratch) output)
        (some (domainSectionCfg (some .predBoundaryDecide) none restInput
          ((encodeNat index).map some)
          ((encodeNat (next :: values).length).map some) []
          ((DomainOccurrenceFieldBlock.outputEncode
            (index, value)).reverse ++ scratch) output))
        (by simpa [domainSectionEndValues, restInput, domainSectionValueWork]
          using hvalue)
        (by simpa [binaryPredBits_encodeNat] using hpred)
      have hnonempty := encodeNat_succ_ne_nil values.length
      cases hbits : encodeNat (next :: values).length with
      | nil =>
          exfalso
          apply hnonempty
          simpa using hbits
      | cons bit bits =>
          have hdecide := domainSectionEvalsToInTimeOne
            (domainSection_step_predBoundaryDecide_cons (some bit)
              (bits.map some) restInput ((encodeNat index).map some) []
              ((DomainOccurrenceFieldBlock.outputEncode
                (index, value)).reverse ++ scratch) output none)
          have hthroughDecide := EvalsToInTime.trans
            domainSectionComputer.step
            (2 * (encodeNat (value :: next :: values).length).length + 2 +
              domainSectionValueWork index value) 1
            (domainSectionCfg (some .beginValue) state
              (domainSectionEndValues (value :: next :: values))
              ((encodeNat index).map some)
              ((encodeNat (value :: next :: values).length).map some) []
              scratch output)
            (domainSectionCfg (some .predBoundaryDecide) none restInput
              ((encodeNat index).map some)
              ((encodeNat (next :: values).length).map some) []
              ((DomainOccurrenceFieldBlock.outputEncode
                (index, value)).reverse ++ scratch) output)
            (some (domainSectionCfg (some .beginValue) (some (some bit))
              restInput ((encodeNat index).map some)
              ((encodeNat (next :: values).length).map some) []
              ((DomainOccurrenceFieldBlock.outputEncode
                (index, value)).reverse ++ scratch) output))
            (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              hthroughPred)
            (by rw [hbits]; exact hdecide)
          have hrest := domainSection_valuesEnd_evals index next values
            ((DomainOccurrenceFieldBlock.outputEncode
              (index, value)).reverse ++ scratch) output (some (some bit))
          have hall := EvalsToInTime.trans domainSectionComputer.step
            (2 * (encodeNat (value :: next :: values).length).length + 3 +
              domainSectionValueWork index value)
            (domainSectionValuesEndTime index (next :: values))
            (domainSectionCfg (some .beginValue) state
              (domainSectionEndValues (value :: next :: values))
              ((encodeNat index).map some)
              ((encodeNat (value :: next :: values).length).map some) []
              scratch output)
            (domainSectionCfg (some .beginValue) (some (some bit)) restInput
              ((encodeNat index).map some)
              ((encodeNat (next :: values).length).map some) []
              ((DomainOccurrenceFieldBlock.outputEncode
                (index, value)).reverse ++ scratch) output)
            (some (domainSectionCfg (some .finish) none []
              ((encodeNat (index + 1)).map some) [] []
              ((DomainFieldRow.outputEncode
                (DomainFieldRow.occurrences
                  (index, value :: next :: values))).reverse ++ scratch)
              output))
            (by
              have htime :
                  1 +
                      (2 *
                          (encodeNat
                            (value :: next :: values).length).length +
                        2 + domainSectionValueWork index value) =
                    2 *
                        (encodeNat (value :: next :: values).length).length +
                      3 + domainSectionValueWork index value := by
                omega
              rw [htime] at hthroughDecide
              exact hthroughDecide)
            (by
              rw [domainSection_occurrences_cons_reverse_append]
              simpa [restInput, List.append_assoc] using hrest)
          simpa [domainSectionValuesEndTime, domainSectionPredWork,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

/-! ## Whole domain-section execution -/

/-- Remaining source bits once the delimiter before the current row count has
been consumed. -/
private def domainSectionRowsInput : List (List ℕ) → List (Option Bool)
  | [] => []
  | domain :: domains =>
      (encodeNat domain.length).map some ++
        match domain with
        | [] =>
            match domains with
            | [] => []
            | _ :: _ => none :: domainSectionRowsInput domains
        | value :: values =>
            none ::
              match domains with
              | [] => domainSectionEndValues (value :: values)
              | _ :: _ =>
                  domainSectionBoundaryValues (value :: values)
                    (domainSectionRowsInput domains)

private theorem domainSectionEndValues_eq
    (value : ℕ) (values : List ℕ) :
    none :: domainSectionEndValues (value :: values) =
      SourceOrderRawFields.encode (value :: values) := by
  induction values generalizing value with
  | nil => simp [domainSectionEndValues, SourceOrderRawFields.encode]
  | cons next values ih =>
      rw [domainSectionEndValues]
      rw [SourceOrderRawFields.encode]
      simp only [List.flatMap_cons, List.cons_append]
      rw [ih next]
      simp [SourceOrderRawFields.encode]

private theorem domainSectionBoundaryValues_eq
    (value : ℕ) (values : List ℕ) (after : List (Option Bool)) :
    none :: domainSectionBoundaryValues (value :: values) after =
      SourceOrderRawFields.encode (value :: values) ++ none :: after := by
  induction values generalizing value with
  | nil => simp [domainSectionBoundaryValues, SourceOrderRawFields.encode]
  | cons next values ih =>
      rw [domainSectionBoundaryValues]
      rw [SourceOrderRawFields.encode]
      simp only [List.flatMap_cons, List.cons_append]
      rw [ih next]
      simp [SourceOrderRawFields.encode, List.append_assoc]

private theorem domainSectionRowsInput_eq
    (domain : List ℕ) (domains : List (List ℕ)) :
    none :: domainSectionRowsInput (domain :: domains) =
      SourceOrderRawFields.encode
        (DomainFieldSection.rowFields (domain :: domains)) := by
  induction domains generalizing domain with
  | nil =>
      cases domain with
      | nil =>
          simp [domainSectionRowsInput, DomainFieldSection.rowFields,
            SourceOrderRawFields.encode, encodeNat_zero]
      | cons value values =>
          rw [domainSectionRowsInput]
          rw [domainSectionEndValues_eq]
          simp [DomainFieldSection.rowFields, SourceOrderRawFields.encode]
  | cons next domains ih =>
      cases domain with
      | nil =>
          rw [domainSectionRowsInput]
          simp only [List.length_nil]
          rw [encodeNat_zero]
          simp only [List.map_nil, List.nil_append]
          rw [ih next]
          simp [DomainFieldSection.rowFields, SourceOrderRawFields.encode]
          exact encodeNat_zero
      | cons value values =>
          rw [domainSectionRowsInput]
          rw [domainSectionBoundaryValues_eq]
          rw [ih next]
          simp [DomainFieldSection.rowFields, SourceOrderRawFields.encode,
            List.append_assoc]

/-- Domain-occurrence output starting at an arbitrary current index. -/
private def domainSectionOutputFrom (index : ℕ)
    (domains : List (List ℕ)) : List (Option Bool) :=
  DomainFieldRow.outputEncode
    (RuntimeStructuralView.indexedDomainOccurrencesFrom index domains)

private theorem domainSectionOutputFrom_cons
    (index : ℕ) (domain : List ℕ) (domains : List (List ℕ)) :
    domainSectionOutputFrom index (domain :: domains) =
      DomainFieldRow.outputEncode (DomainFieldRow.occurrences (index, domain)) ++
        domainSectionOutputFrom (index + 1) domains := by
  simp [domainSectionOutputFrom,
    RuntimeStructuralView.indexedDomainOccurrencesFrom,
    DomainFieldRow.outputEncode, DomainFieldRow.occurrences,
    List.flatMap_append, List.flatMap_map]

private theorem domainSectionOutputFrom_cons_reverse_append
    (index : ℕ) (domain : List ℕ) (domains : List (List ℕ))
    (scratch : List (Option Bool)) :
    (domainSectionOutputFrom index (domain :: domains)).reverse ++ scratch =
      (domainSectionOutputFrom (index + 1) domains).reverse ++
        (DomainFieldRow.outputEncode
          (DomainFieldRow.occurrences (index, domain))).reverse ++ scratch := by
  rw [domainSectionOutputFrom_cons, List.reverse_append]

private def domainSectionRowsTime (index : ℕ) : List (List ℕ) → ℕ
  | [] => 0
  | domain :: [] =>
      2 * (encodeNat domain.length).length + 3 +
        match domain with
        | [] => domainSectionSuccWork index
        | value :: values =>
            domainSectionValuesEndTime index (value :: values)
  | domain :: next :: domains =>
      2 * (encodeNat domain.length).length + 3 +
        (match domain with
          | [] => domainSectionSuccWork index
          | value :: values =>
              domainSectionValuesBoundaryTime index (value :: values)) +
        domainSectionRowsTime (index + 1) (next :: domains)

private def domainSection_countBoundary_evals
    (bits : List Bool) (input index scratch output : List (Option Bool))
    (state : DomainSectionState) :
    EvalsToInTime domainSectionComputer.step
      (domainSectionCfg (some .readCount) state
        (bits.map some ++ none :: input) index [] [] scratch output)
      (some (domainSectionCfg (some .decideCountBoundary) none input index
        (bits.map some) [] scratch output))
      (2 * bits.length + 2) := by
  have hread := domainSection_readCountBoundary_evals bits input index [] []
    scratch output state
  have hrestore := domainSection_restoreCountBoundary_evals
    (bits.reverse.map some) input index [] scratch output (some none)
  have hall := EvalsToInTime.trans domainSectionComputer.step
    (bits.length + 1) (bits.length + 1)
    (domainSectionCfg (some .readCount) state
      (bits.map some ++ none :: input) index [] [] scratch output)
    (domainSectionCfg (some .restoreCountBoundary) (some none) input index []
      (bits.reverse.map some) scratch output)
    (some (domainSectionCfg (some .decideCountBoundary) none input index
      (bits.map some) [] scratch output))
    (by simpa using hread) (by simpa [List.map_reverse] using hrestore)
  have htime : bits.length + 1 + (bits.length + 1) =
      2 * bits.length + 2 := by omega
  rw [htime] at hall
  exact hall

private def domainSection_countEnd_evals
    (bits : List Bool) (index scratch output : List (Option Bool))
    (state : DomainSectionState) :
    EvalsToInTime domainSectionComputer.step
      (domainSectionCfg (some .readCount) state (bits.map some) index [] []
        scratch output)
      (some (domainSectionCfg (some .decideCountEnd) none [] index
        (bits.map some) [] scratch output))
      (2 * bits.length + 2) := by
  have hread := domainSection_readCountEnd_evals bits index [] [] scratch output
    state
  have hrestore := domainSection_restoreCountEnd_evals
    (bits.reverse.map some) index [] scratch output none
  have hall := EvalsToInTime.trans domainSectionComputer.step
    (bits.length + 1) (bits.length + 1)
    (domainSectionCfg (some .readCount) state (bits.map some) index [] []
      scratch output)
    (domainSectionCfg (some .restoreCountEnd) none [] index []
      (bits.reverse.map some) scratch output)
    (some (domainSectionCfg (some .decideCountEnd) none [] index
      (bits.map some) [] scratch output))
    (by simpa using hread) (by simpa [List.map_reverse] using hrestore)
  have htime : bits.length + 1 + (bits.length + 1) =
      2 * bits.length + 2 := by omega
  rw [htime] at hall
  exact hall

private def domainSection_rows_evals
    (index : ℕ) (domain : List ℕ) (domains : List (List ℕ))
    (scratch output : List (Option Bool)) (state : DomainSectionState) :
    EvalsToInTime domainSectionComputer.step
      (domainSectionCfg (some .readCount) state
        (domainSectionRowsInput (domain :: domains))
        ((encodeNat index).map some) [] [] scratch output)
      (some (domainSectionCfg (some .finish) none []
        ((encodeNat (index + (domain :: domains).length)).map some) [] []
        ((domainSectionOutputFrom index (domain :: domains)).reverse ++ scratch)
        output))
      (domainSectionRowsTime index (domain :: domains)) := by
  induction domains generalizing index domain scratch state with
  | nil =>
      cases domain with
      | nil =>
          have hcount := domainSection_countEnd_evals (encodeNat 0)
            ((encodeNat index).map some) scratch output state
          have hdecide := domainSectionEvalsToInTimeOne
            (domainSection_step_decideCountEnd_nil
              ((encodeNat index).map some) [] scratch output none)
          have hfirst := EvalsToInTime.trans domainSectionComputer.step
            (2 * (encodeNat 0).length + 2) 1
            (domainSectionCfg (some .readCount) state
              (domainSectionRowsInput [[]]) ((encodeNat index).map some) [] []
              scratch output)
            (domainSectionCfg (some .decideCountEnd) none []
              ((encodeNat index).map some) [] [] scratch output)
            (some (domainSectionCfg (some .advanceEnd) none []
              ((encodeNat index).map some) [] [] scratch output))
            (by simpa [domainSectionRowsInput, encodeNat_zero] using hcount)
            (by simpa using hdecide)
          have hsucc := domainSection_advanceEnd_evals
            (encodeNat index) [] [] scratch output none
          have hall := EvalsToInTime.trans domainSectionComputer.step
            (2 * (encodeNat 0).length + 3) (domainSectionSuccWork index)
            (domainSectionCfg (some .readCount) state
              (domainSectionRowsInput [[]]) ((encodeNat index).map some) [] []
              scratch output)
            (domainSectionCfg (some .advanceEnd) none []
              ((encodeNat index).map some) [] [] scratch output)
            (some (domainSectionCfg (some .finish) none []
              ((encodeNat (index + 1)).map some) [] [] scratch output))
            (by
              have htime : 1 + (2 * (encodeNat 0).length + 2) =
                  2 * (encodeNat 0).length + 3 := by omega
              rw [htime] at hfirst
              exact hfirst)
            (by simpa [domainSectionSuccWork, binarySuccBits_encodeNat] using
              hsucc)
          have htime :
              domainSectionSuccWork index +
                  (2 * (encodeNat 0).length + 3) =
                2 * (encodeNat 0).length + 3 +
                  domainSectionSuccWork index := by omega
          rw [htime] at hall
          simpa [domainSectionRowsTime, domainSectionOutputFrom,
            RuntimeStructuralView.indexedDomainOccurrencesFrom,
            DomainFieldRow.outputEncode, domainSectionSuccWork]
            using hall
      | cons value values =>
          have hcount := domainSection_countBoundary_evals
            (encodeNat (value :: values).length)
            (domainSectionEndValues (value :: values))
            ((encodeNat index).map some) scratch output state
          have hnonempty := encodeNat_succ_ne_nil values.length
          cases hbits : encodeNat (value :: values).length with
          | nil =>
              exfalso
              apply hnonempty
              simpa using hbits
          | cons bit bits =>
              have hdecide := domainSectionEvalsToInTimeOne
                (domainSection_step_decideCountBoundary_cons (some bit)
                  (bits.map some) (domainSectionEndValues (value :: values))
                  ((encodeNat index).map some) [] scratch output none)
              have hfirst := EvalsToInTime.trans domainSectionComputer.step
                (2 * (encodeNat (value :: values).length).length + 2) 1
                (domainSectionCfg (some .readCount) state
                  (domainSectionRowsInput [value :: values])
                  ((encodeNat index).map some) [] [] scratch output)
                (domainSectionCfg (some .decideCountBoundary) none
                  (domainSectionEndValues (value :: values))
                  ((encodeNat index).map some)
                  ((encodeNat (value :: values).length).map some) [] scratch
                  output)
                (some (domainSectionCfg (some .beginValue) (some (some bit))
                  (domainSectionEndValues (value :: values))
                  ((encodeNat index).map some)
                  ((encodeNat (value :: values).length).map some) [] scratch
                  output))
                (by simpa [domainSectionRowsInput] using hcount)
                (by rw [hbits]; exact hdecide)
              have hvalues := domainSection_valuesEnd_evals index value values
                scratch output (some (some bit))
              have hall := EvalsToInTime.trans domainSectionComputer.step
                (2 * (encodeNat (value :: values).length).length + 3)
                (domainSectionValuesEndTime index (value :: values))
                (domainSectionCfg (some .readCount) state
                  (domainSectionRowsInput [value :: values])
                  ((encodeNat index).map some) [] [] scratch output)
                (domainSectionCfg (some .beginValue) (some (some bit))
                  (domainSectionEndValues (value :: values))
                  ((encodeNat index).map some)
                  ((encodeNat (value :: values).length).map some) [] scratch
                  output)
                (some (domainSectionCfg (some .finish) none []
                  ((encodeNat (index + 1)).map some) [] []
                  ((DomainFieldRow.outputEncode
                    (DomainFieldRow.occurrences
                      (index, value :: values))).reverse ++ scratch) output))
                (by
                  have htime :
                      1 +
                          (2 *
                              (encodeNat (value :: values).length).length +
                            2) =
                        2 * (encodeNat (value :: values).length).length + 3 := by
                    omega
                  rw [htime] at hfirst
                  exact hfirst)
                hvalues
              have htime :
                  domainSectionValuesEndTime index (value :: values) +
                      (2 * (encodeNat (value :: values).length).length + 3) =
                    2 * (encodeNat (value :: values).length).length + 3 +
                      domainSectionValuesEndTime index (value :: values) := by
                omega
              rw [htime] at hall
              simpa [domainSectionRowsTime, domainSectionOutputFrom,
                RuntimeStructuralView.indexedDomainOccurrencesFrom]
                using hall
  | cons next domains ih =>
      have hrest := ih (index := index + 1) (domain := next)
      cases domain with
      | nil =>
          have hcount := domainSection_countBoundary_evals (encodeNat 0)
            (domainSectionRowsInput (next :: domains))
            ((encodeNat index).map some) scratch output state
          have hdecide := domainSectionEvalsToInTimeOne
            (domainSection_step_decideCountBoundary_nil
              (domainSectionRowsInput (next :: domains))
              ((encodeNat index).map some) [] scratch output none)
          have hfirst := EvalsToInTime.trans domainSectionComputer.step
            (2 * (encodeNat 0).length + 2) 1
            (domainSectionCfg (some .readCount) state
              (domainSectionRowsInput ([] :: next :: domains))
              ((encodeNat index).map some) [] [] scratch output)
            (domainSectionCfg (some .decideCountBoundary) none
              (domainSectionRowsInput (next :: domains))
              ((encodeNat index).map some) [] [] scratch output)
            (some (domainSectionCfg (some .advanceBoundary) none
              (domainSectionRowsInput (next :: domains))
              ((encodeNat index).map some) [] [] scratch output))
            (by simpa [domainSectionRowsInput, encodeNat_zero] using hcount)
            (by simpa using hdecide)
          have hsucc := domainSection_advanceBoundary_evals
            (encodeNat index) [] (domainSectionRowsInput (next :: domains)) []
            scratch output none
          have hrow := EvalsToInTime.trans domainSectionComputer.step
            (2 * (encodeNat 0).length + 3) (domainSectionSuccWork index)
            (domainSectionCfg (some .readCount) state
              (domainSectionRowsInput ([] :: next :: domains))
              ((encodeNat index).map some) [] [] scratch output)
            (domainSectionCfg (some .advanceBoundary) none
              (domainSectionRowsInput (next :: domains))
              ((encodeNat index).map some) [] [] scratch output)
            (some (domainSectionCfg (some .readCount) none
              (domainSectionRowsInput (next :: domains))
              ((encodeNat (index + 1)).map some) [] [] scratch output))
            (by
              have htime : 1 + (2 * (encodeNat 0).length + 2) =
                  2 * (encodeNat 0).length + 3 := by omega
              rw [htime] at hfirst
              exact hfirst)
            (by simpa [domainSectionSuccWork, binarySuccBits_encodeNat] using
              hsucc)
          have hall := EvalsToInTime.trans domainSectionComputer.step
            (domainSectionSuccWork index +
              (2 * (encodeNat 0).length + 3))
            (domainSectionRowsTime (index + 1) (next :: domains))
            (domainSectionCfg (some .readCount) state
              (domainSectionRowsInput ([] :: next :: domains))
              ((encodeNat index).map some) [] [] scratch output)
            (domainSectionCfg (some .readCount) none
              (domainSectionRowsInput (next :: domains))
              ((encodeNat (index + 1)).map some) [] [] scratch output)
            (some (domainSectionCfg (some .finish) none []
              ((encodeNat (index + ([] :: next :: domains).length)).map some)
              [] []
              ((domainSectionOutputFrom index
                ([] :: next :: domains)).reverse ++ scratch) output))
            (by
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrow)
            (by
              have hend : index + 1 + (next :: domains).length =
                  index + ([] :: next :: domains).length := by
                simp only [List.length_cons]
                omega
              have htail := hrest (scratch := scratch) (state := none)
              rw [hend] at htail
              rw [domainSectionOutputFrom_cons_reverse_append]
              simp [DomainFieldRow.outputEncode, DomainFieldRow.occurrences]
              exact htail)
          simpa [domainSectionRowsTime, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using hall
      | cons value values =>
          have hcount := domainSection_countBoundary_evals
            (encodeNat (value :: values).length)
            (domainSectionBoundaryValues (value :: values)
              (domainSectionRowsInput (next :: domains)))
            ((encodeNat index).map some) scratch output state
          have hnonempty := encodeNat_succ_ne_nil values.length
          cases hbits : encodeNat (value :: values).length with
          | nil =>
              exfalso
              apply hnonempty
              simpa using hbits
          | cons bit bits =>
              have hdecide := domainSectionEvalsToInTimeOne
                (domainSection_step_decideCountBoundary_cons (some bit)
                  (bits.map some)
                  (domainSectionBoundaryValues (value :: values)
                    (domainSectionRowsInput (next :: domains)))
                  ((encodeNat index).map some) [] scratch output none)
              have hfirst := EvalsToInTime.trans domainSectionComputer.step
                (2 * (encodeNat (value :: values).length).length + 2) 1
                (domainSectionCfg (some .readCount) state
                  (domainSectionRowsInput
                    ((value :: values) :: next :: domains))
                  ((encodeNat index).map some) [] [] scratch output)
                (domainSectionCfg (some .decideCountBoundary) none
                  (domainSectionBoundaryValues (value :: values)
                    (domainSectionRowsInput (next :: domains)))
                  ((encodeNat index).map some)
                  ((encodeNat (value :: values).length).map some) [] scratch
                  output)
                (some (domainSectionCfg (some .beginValue) (some (some bit))
                  (domainSectionBoundaryValues (value :: values)
                    (domainSectionRowsInput (next :: domains)))
                  ((encodeNat index).map some)
                  ((encodeNat (value :: values).length).map some) [] scratch
                  output))
                (by simpa [domainSectionRowsInput] using hcount)
                (by rw [hbits]; exact hdecide)
              have hvalues := domainSection_valuesBoundary_evals index value
                values (domainSectionRowsInput (next :: domains)) scratch
                output (some (some bit))
              have hrow := EvalsToInTime.trans domainSectionComputer.step
                (2 * (encodeNat (value :: values).length).length + 3)
                (domainSectionValuesBoundaryTime index (value :: values))
                (domainSectionCfg (some .readCount) state
                  (domainSectionRowsInput
                    ((value :: values) :: next :: domains))
                  ((encodeNat index).map some) [] [] scratch output)
                (domainSectionCfg (some .beginValue) (some (some bit))
                  (domainSectionBoundaryValues (value :: values)
                    (domainSectionRowsInput (next :: domains)))
                  ((encodeNat index).map some)
                  ((encodeNat (value :: values).length).map some) [] scratch
                  output)
                (some (domainSectionCfg (some .readCount) none
                  (domainSectionRowsInput (next :: domains))
                  ((encodeNat (index + 1)).map some) [] []
                  ((DomainFieldRow.outputEncode
                    (DomainFieldRow.occurrences
                      (index, value :: values))).reverse ++ scratch) output))
                (by
                  have htime :
                      1 +
                          (2 *
                              (encodeNat (value :: values).length).length +
                            2) =
                        2 * (encodeNat (value :: values).length).length + 3 := by
                    omega
                  rw [htime] at hfirst
                  exact hfirst)
                hvalues
              have hall := EvalsToInTime.trans domainSectionComputer.step
                (domainSectionValuesBoundaryTime index (value :: values) +
                  (2 * (encodeNat (value :: values).length).length + 3))
                (domainSectionRowsTime (index + 1) (next :: domains))
                (domainSectionCfg (some .readCount) state
                  (domainSectionRowsInput
                    ((value :: values) :: next :: domains))
                  ((encodeNat index).map some) [] [] scratch output)
                (domainSectionCfg (some .readCount) none
                  (domainSectionRowsInput (next :: domains))
                  ((encodeNat (index + 1)).map some) [] []
                  ((DomainFieldRow.outputEncode
                    (DomainFieldRow.occurrences
                      (index, value :: values))).reverse ++ scratch) output)
                (some (domainSectionCfg (some .finish) none []
                  ((encodeNat
                    (index + ((value :: values) :: next :: domains).length)).map
                      some) [] []
                  ((domainSectionOutputFrom index
                    ((value :: values) :: next :: domains)).reverse ++ scratch)
                  output))
                (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                  using hrow)
                (by
                  have hend : index + 1 + (next :: domains).length =
                      index + ((value :: values) :: next :: domains).length := by
                    simp only [List.length_cons]
                    omega
                  have htail := hrest
                    (scratch :=
                      (DomainFieldRow.outputEncode
                        (DomainFieldRow.occurrences
                          (index, value :: values))).reverse ++ scratch)
                    (state := none)
                  rw [hend] at htail
                  rw [domainSectionOutputFrom_cons_reverse_append]
                  simpa [List.append_assoc] using htail)
              simpa [domainSectionRowsTime, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using hall

private theorem domainSection_initList_eq_cfg
    (input : List (Option Bool)) :
    initList domainSectionComputer input =
      domainSectionCfg (some .start) none input [] [] [] [] [] := by
  unfold initList domainSectionCfg
  congr
  funext stack
  cases stack <;> rfl

private theorem domainSection_haltList_eq_cfg
    (output : List (Option Bool)) :
    haltList domainSectionComputer output =
      domainSectionCfg none none [] [] [] [] [] output := by
  unfold haltList domainSectionCfg
  congr
  funext stack
  cases stack <;> rfl

private theorem domainSectionOutputFrom_zero
    (domains : List (List ℕ)) :
    domainSectionOutputFrom 0 domains = DomainFieldSection.outputEncode domains :=
  rfl

private def domainSection_run_evals (domains : List (List ℕ)) :
    EvalsToInTime domainSectionComputer.step
      (domainSectionCfg (some .start) none
        (DomainFieldSection.rowPayloadEncode domains) [] [] [] [] [])
      (some (domainSectionCfg none none [] [] [] [] []
        (DomainFieldSection.outputEncode domains)))
      (match domains with
        | [] => 3
        | _ :: _ =>
            domainSectionRowsTime 0 domains +
              (DomainFieldSection.outputEncode domains).length +
                (encodeNat domains.length).length + 3) := by
  cases domains with
  | nil =>
      have hstart := domainSectionEvalsToInTimeOne
        (domainSection_step_start_nil [] [] [] [] [] none)
      have hfinish := domainSection_finish_evals [] [] [] none
      have hfirst := EvalsToInTime.trans domainSectionComputer.step
        1 1
        (domainSectionCfg (some .start) none
          (DomainFieldSection.rowPayloadEncode []) [] [] [] [] [])
        (domainSectionCfg (some .finish) none [] [] [] [] [] [])
        (some (domainSectionCfg (some .clearIndex) none [] [] [] [] [] []))
        (by simpa [DomainFieldSection.rowPayloadEncode,
          DomainFieldSection.rowFields, SourceOrderRawFields.encode] using
            hstart)
        (by simpa using hfinish)
      have hclear := domainSection_clearIndex_evals [] [] none
      have hall := EvalsToInTime.trans domainSectionComputer.step
        2 1
        (domainSectionCfg (some .start) none
          (DomainFieldSection.rowPayloadEncode []) [] [] [] [] [])
        (domainSectionCfg (some .clearIndex) none [] [] [] [] [] [])
        (some (domainSectionCfg none none [] [] [] [] [] []))
        (by simpa using hfirst) (by simpa using hclear)
      simpa [DomainFieldSection.outputEncode, domainSectionOutputFrom,
        RuntimeStructuralView.indexedDomainOccurrences,
        RuntimeStructuralView.indexedDomainOccurrencesFrom,
        DomainFieldRow.outputEncode] using hall
  | cons domain domains =>
      have hinput : DomainFieldSection.rowPayloadEncode (domain :: domains) =
          none :: domainSectionRowsInput (domain :: domains) := by
        rw [DomainFieldSection.rowPayloadEncode,
          domainSectionRowsInput_eq domain domains]
      have hstart := domainSectionEvalsToInTimeOne
        (domainSection_step_start_cons none
          (domainSectionRowsInput (domain :: domains)) [] [] [] [] [] none)
      have hrows := domainSection_rows_evals 0 domain domains [] [] (some none)
      have hfirst := EvalsToInTime.trans domainSectionComputer.step
        1 (domainSectionRowsTime 0 (domain :: domains))
        (domainSectionCfg (some .start) none
          (DomainFieldSection.rowPayloadEncode (domain :: domains))
          [] [] [] [] [])
        (domainSectionCfg (some .readCount) (some none)
          (domainSectionRowsInput (domain :: domains)) [] [] [] [] [])
        (some (domainSectionCfg (some .finish) none []
          ((encodeNat (domain :: domains).length).map some) [] []
          ((DomainFieldSection.outputEncode
            (domain :: domains)).reverse) []))
        (by simpa [hinput] using hstart)
        (by simpa [domainSectionOutputFrom_zero, encodeNat_zero] using hrows)
      have hfinish := domainSection_finish_evals
        (DomainFieldSection.outputEncode (domain :: domains)).reverse []
        ((encodeNat (domain :: domains).length).map some) none
      have hthroughFinish := EvalsToInTime.trans domainSectionComputer.step
        (domainSectionRowsTime 0 (domain :: domains) + 1)
        ((DomainFieldSection.outputEncode (domain :: domains)).length + 1)
        (domainSectionCfg (some .start) none
          (DomainFieldSection.rowPayloadEncode (domain :: domains))
          [] [] [] [] [])
        (domainSectionCfg (some .finish) none []
          ((encodeNat (domain :: domains).length).map some) [] []
          ((DomainFieldSection.outputEncode (domain :: domains)).reverse) [])
        (some (domainSectionCfg (some .clearIndex) none []
          ((encodeNat (domain :: domains).length).map some) [] [] []
          (DomainFieldSection.outputEncode (domain :: domains))))
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfirst)
        (by simpa [List.reverse_reverse] using hfinish)
      have hclear := domainSection_clearIndex_evals
        ((encodeNat (domain :: domains).length).map some)
        (DomainFieldSection.outputEncode (domain :: domains)) none
      have hall := EvalsToInTime.trans domainSectionComputer.step
        ((DomainFieldSection.outputEncode (domain :: domains)).length + 1 +
          (domainSectionRowsTime 0 (domain :: domains) + 1))
        ((encodeNat (domain :: domains).length).length + 1)
        (domainSectionCfg (some .start) none
          (DomainFieldSection.rowPayloadEncode (domain :: domains))
          [] [] [] [] [])
        (domainSectionCfg (some .clearIndex) none []
          ((encodeNat (domain :: domains).length).map some) [] [] []
          (DomainFieldSection.outputEncode (domain :: domains)))
        (some (domainSectionCfg none none [] [] [] [] []
          (DomainFieldSection.outputEncode (domain :: domains))))
        (by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hthroughFinish)
        (by simpa using hclear)
      have htime :
          (encodeNat (domain :: domains).length).length + 1 +
              ((DomainFieldSection.outputEncode
                    (domain :: domains)).length + 1 +
                (domainSectionRowsTime 0 (domain :: domains) + 1)) =
            domainSectionRowsTime 0 (domain :: domains) +
              (DomainFieldSection.outputEncode (domain :: domains)).length +
                (encodeNat (domain :: domains).length).length + 3 := by
        omega
      rw [htime] at hall
      simpa using hall

/-! ## Bit-level polynomial bound -/

private def domainSectionValueBits (values : List ℕ) : ℕ :=
  (values.map fun value => (encodeNat value).length).sum

private theorem domainSectionValuesEndTime_eq_boundary
    (index : ℕ) (values : List ℕ) :
    domainSectionValuesEndTime index values =
      domainSectionValuesBoundaryTime index values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      cases values with
      | nil => rfl
      | cons next values =>
          simp only [domainSectionValuesEndTime,
            domainSectionValuesBoundaryTime]
          rw [ih]

private theorem domainSectionValuesBoundaryTime_le
    (index : ℕ) (values : List ℕ) :
    domainSectionValuesBoundaryTime index values ≤
      values.length * (2 * index + 7) + 2 * values.length ^ 2 +
        domainSectionValueBits values + 2 * index + 2 := by
  induction values with
  | nil => simp [domainSectionValuesBoundaryTime]
  | cons value values ih =>
      cases values with
      | nil =>
          have hi := BinaryNatLists.encodeNat_length_le index
          have hc := BinaryNatLists.encodeNat_length_le 1
          simp only [domainSectionValuesBoundaryTime, domainSectionValueWork,
            domainSectionPredWork, domainSectionSuccWork,
            domainSectionValueBits, List.map_cons, List.sum_cons,
            List.length_cons, List.length_nil, Nat.zero_add,
            Nat.one_mul, Nat.one_pow]
          omega
      | cons next values =>
          have hi := BinaryNatLists.encodeNat_length_le index
          have hc' := BinaryNatLists.encodeNat_length_le
            (values.length + 1 + 1)
          have htail := ih
          simp only [domainSectionValuesBoundaryTime, domainSectionValueWork,
            domainSectionPredWork, domainSectionValueBits, List.map_cons,
            List.sum_cons, List.length_cons] at htail ⊢
          clear ih
          rw [show (values.length + 1 + 1) * (2 * index + 7) =
            (values.length + 1) * (2 * index + 7) +
              (2 * index + 7) by ring]
          rw [show 2 * (values.length + 1 + 1) ^ 2 =
            2 * (values.length + 1) ^ 2 + 4 * values.length + 6 by ring]
          omega

private theorem domainSectionValuesEndTime_le
    (index : ℕ) (values : List ℕ) :
    domainSectionValuesEndTime index values ≤
      values.length * (2 * index + 7) + 2 * values.length ^ 2 +
        domainSectionValueBits values + 2 * index + 2 := by
  rw [domainSectionValuesEndTime_eq_boundary]
  exact domainSectionValuesBoundaryTime_le index values

private def domainSectionRowSize (domain : List ℕ) : ℕ :=
  (SourceOrderRawFields.encode (domain.length :: domain)).length

private theorem domainSectionRowSize_eq (domain : List ℕ) :
    domainSectionRowSize domain =
      (encodeNat domain.length).length + domain.length +
        domainSectionValueBits domain + 1 := by
  simp [domainSectionRowSize, SourceOrderRawFields.encode,
    domainSectionValueBits]
  omega

private def domainSectionRowTime (index : ℕ) (domain : List ℕ) : ℕ :=
  2 * (encodeNat domain.length).length + 3 +
    match domain with
    | [] => domainSectionSuccWork index
    | value :: values =>
        domainSectionValuesBoundaryTime index (value :: values)

private theorem domainSectionRowTime_le (index : ℕ) (domain : List ℕ) :
    domainSectionRowTime index domain ≤
      20 * (index + domainSectionRowSize domain + 1) ^ 2 := by
  cases domain with
  | nil =>
      have hi := BinaryNatLists.encodeNat_length_le index
      simp only [domainSectionRowTime, domainSectionRowSize_eq,
        domainSectionValueBits, List.map_nil, List.sum_nil, List.length_nil,
        encodeNat_zero, domainSectionSuccWork, Nat.zero_add]
      nlinarith [sq_nonneg index]
  | cons value values =>
      have hvalues := domainSectionValuesBoundaryTime_le index
        (value :: values)
      have hcount := BinaryNatLists.encodeNat_length_le
        (value :: values).length
      have hi := BinaryNatLists.encodeNat_length_le index
      have hlen : (value :: values).length ≤
          domainSectionRowSize (value :: values) := by
        rw [domainSectionRowSize_eq]
        omega
      have hbits : domainSectionValueBits (value :: values) ≤
          domainSectionRowSize (value :: values) := by
        rw [domainSectionRowSize_eq]
        omega
      simp only [domainSectionRowTime]
      nlinarith [sq_nonneg
        (index + domainSectionRowSize (value :: values) + 1)]

private theorem domainSectionRowPayload_length_cons
    (domain : List ℕ) (domains : List (List ℕ)) :
    (DomainFieldSection.rowPayloadEncode (domain :: domains)).length =
      domainSectionRowSize domain +
        (DomainFieldSection.rowPayloadEncode domains).length := by
  simp [DomainFieldSection.rowPayloadEncode, DomainFieldSection.rowFields,
    SourceOrderRawFields.encode, domainSectionRowSize]
  omega

private theorem domainSectionRowsTime_cons
    (index : ℕ) (domain : List ℕ) (domains : List (List ℕ)) :
    domainSectionRowsTime index (domain :: domains) =
      domainSectionRowTime index domain +
        domainSectionRowsTime (index + 1) domains := by
  cases domains <;> cases domain <;>
    simp [domainSectionRowsTime, domainSectionRowTime,
      domainSectionValuesEndTime_eq_boundary]

private theorem domainSectionRowsTime_le
    (index : ℕ) (domains : List (List ℕ)) :
    domainSectionRowsTime index domains ≤
      20 * domains.length *
        (index + domains.length +
          (DomainFieldSection.rowPayloadEncode domains).length + 1) ^ 2 := by
  induction domains generalizing index with
  | nil => simp [domainSectionRowsTime]
  | cons domain domains ih =>
      rw [domainSectionRowsTime_cons]
      let payloadSize :=
        (DomainFieldSection.rowPayloadEncode (domain :: domains)).length
      let scale := index + (domain :: domains).length + payloadSize + 1
      have hrowSize : domainSectionRowSize domain ≤ payloadSize := by
        simp only [payloadSize]
        rw [domainSectionRowPayload_length_cons]
        omega
      have hrowArg : index + domainSectionRowSize domain + 1 ≤ scale := by
        simp only [scale, List.length_cons]
        omega
      have hrowSquare := Nat.pow_le_pow_left hrowArg 2
      have hrow := domainSectionRowTime_le index domain
      have hrow' : domainSectionRowTime index domain ≤ 20 * scale ^ 2 :=
        hrow.trans (Nat.mul_le_mul_left 20 hrowSquare)
      have htail := ih (index + 1)
      have htailPayload :
          (DomainFieldSection.rowPayloadEncode domains).length ≤ payloadSize := by
        simp only [payloadSize]
        rw [domainSectionRowPayload_length_cons]
        omega
      have htailArg :
          index + 1 + domains.length +
                (DomainFieldSection.rowPayloadEncode domains).length + 1 ≤
            scale := by
        simp only [scale, List.length_cons]
        omega
      have htailSquare := Nat.pow_le_pow_left htailArg 2
      have htail' : domainSectionRowsTime (index + 1) domains ≤
          20 * domains.length * scale ^ 2 :=
        htail.trans (Nat.mul_le_mul_left (20 * domains.length) htailSquare)
      calc
        domainSectionRowTime index domain +
              domainSectionRowsTime (index + 1) domains ≤
            20 * scale ^ 2 + 20 * domains.length * scale ^ 2 :=
          Nat.add_le_add hrow' htail'
        _ = 20 * (domain :: domains).length * scale ^ 2 := by
          simp only [List.length_cons]
          ring

private def domainSectionEntryCount (domains : List (List ℕ)) : ℕ :=
  (domains.map List.length).sum

private def domainSectionPayloadValueBits
    (domains : List (List ℕ)) : ℕ :=
  (domains.map domainSectionValueBits).sum

private theorem domainSectionOutputFrom_length_le
    (index : ℕ) (domains : List (List ℕ)) :
    (domainSectionOutputFrom index domains).length ≤
      domainSectionEntryCount domains * (index + domains.length + 6) +
        domainSectionPayloadValueBits domains := by
  induction domains generalizing index with
  | nil =>
      simp [domainSectionOutputFrom, domainSectionEntryCount,
        domainSectionPayloadValueBits,
        RuntimeStructuralView.indexedDomainOccurrencesFrom,
        DomainFieldRow.outputEncode]
  | cons domain domains ih =>
      rw [domainSectionOutputFrom_cons, List.length_append,
        DomainFieldRow.outputEncode_occurrences_length]
      have hindex := BinaryNatLists.encodeNat_length_le index
      have htail := ih (index + 1)
      simp only [domainSectionEntryCount, domainSectionPayloadValueBits,
        List.map_cons, List.sum_cons, List.length_cons] at htail ⊢
      have hfactor : index + 1 + domains.length + 6 =
          index + (domains.length + 1) + 6 := by omega
      rw [hfactor] at htail
      have hrowFactor : (encodeNat index).length + 6 ≤
          index + (domains.length + 1) + 6 := by omega
      have hrow := Nat.mul_le_mul_left domain.length hrowFactor
      calc
        domain.length * ((encodeNat index).length + 6) +
              domainSectionValueBits domain +
              (domainSectionOutputFrom (index + 1) domains).length ≤
            domain.length * (index + (domains.length + 1) + 6) +
                domainSectionValueBits domain +
              (domainSectionEntryCount domains *
                  (index + (domains.length + 1) + 6) +
                domainSectionPayloadValueBits domains) :=
          Nat.add_le_add
            (Nat.add_le_add_right hrow (domainSectionValueBits domain)) htail
        _ = (domain.length + domainSectionEntryCount domains) *
                (index + (domains.length + 1) + 6) +
              (domainSectionValueBits domain +
                domainSectionPayloadValueBits domains) := by ring

private theorem domainSection_length_le_payload
    (domains : List (List ℕ)) :
    domains.length ≤
      (DomainFieldSection.rowPayloadEncode domains).length := by
  induction domains with
  | nil => simp [DomainFieldSection.rowPayloadEncode,
      DomainFieldSection.rowFields, SourceOrderRawFields.encode]
  | cons domain domains ih =>
      rw [List.length_cons, domainSectionRowPayload_length_cons]
      have hrow : 1 ≤ domainSectionRowSize domain := by
        rw [domainSectionRowSize_eq]
        omega
      omega

private theorem domainSectionEntryCount_le_payload
    (domains : List (List ℕ)) :
    domainSectionEntryCount domains ≤
      (DomainFieldSection.rowPayloadEncode domains).length := by
  induction domains with
  | nil => simp [domainSectionEntryCount, DomainFieldSection.rowPayloadEncode,
      DomainFieldSection.rowFields, SourceOrderRawFields.encode]
  | cons domain domains ih =>
      rw [domainSectionRowPayload_length_cons]
      simp only [domainSectionEntryCount] at ih
      simp only [domainSectionEntryCount, List.map_cons, List.sum_cons]
      have hrow : domain.length ≤ domainSectionRowSize domain := by
        rw [domainSectionRowSize_eq]
        omega
      omega

private theorem domainSectionPayloadValueBits_le_payload
    (domains : List (List ℕ)) :
    domainSectionPayloadValueBits domains ≤
      (DomainFieldSection.rowPayloadEncode domains).length := by
  induction domains with
  | nil => simp [domainSectionPayloadValueBits,
      DomainFieldSection.rowPayloadEncode, DomainFieldSection.rowFields,
      SourceOrderRawFields.encode]
  | cons domain domains ih =>
      rw [domainSectionRowPayload_length_cons]
      simp only [domainSectionPayloadValueBits] at ih
      simp only [domainSectionPayloadValueBits, List.map_cons, List.sum_cons]
      have hrow : domainSectionValueBits domain ≤
          domainSectionRowSize domain := by
        rw [domainSectionRowSize_eq]
        omega
      omega

private theorem domainSectionOutput_length_le_payload
    (domains : List (List ℕ)) :
    (DomainFieldSection.outputEncode domains).length ≤
      (DomainFieldSection.rowPayloadEncode domains).length *
          ((DomainFieldSection.rowPayloadEncode domains).length + 6) +
        (DomainFieldSection.rowPayloadEncode domains).length := by
  have hout := domainSectionOutputFrom_length_le 0 domains
  rw [domainSectionOutputFrom_zero] at hout
  have hentries := domainSectionEntryCount_le_payload domains
  have hbits := domainSectionPayloadValueBits_le_payload domains
  have hlength := domainSection_length_le_payload domains
  have hfactor : 0 + domains.length + 6 ≤
      (DomainFieldSection.rowPayloadEncode domains).length + 6 := by omega
  have hproduct := Nat.mul_le_mul hentries hfactor
  omega

private theorem domainSectionRowsTime_zero_le_payload
    (domains : List (List ℕ)) :
    domainSectionRowsTime 0 domains ≤
      80 * ((DomainFieldSection.rowPayloadEncode domains).length + 1) ^ 3 := by
  have hrows := domainSectionRowsTime_le 0 domains
  let payloadSize :=
    (DomainFieldSection.rowPayloadEncode domains).length
  have hlength : domains.length ≤ payloadSize := by
    simpa only [payloadSize] using domainSection_length_le_payload domains
  have harg : 0 + domains.length + payloadSize + 1 ≤
      2 * (payloadSize + 1) := by omega
  have hsquare := Nat.pow_le_pow_left harg 2
  have hproduct := Nat.mul_le_mul hlength hsquare
  have hscaled := Nat.mul_le_mul_left 20 hproduct
  have hcubic : payloadSize * (payloadSize + 1) ^ 2 ≤
      (payloadSize + 1) ^ 3 := by
    have hsucc := Nat.mul_le_mul_right ((payloadSize + 1) ^ 2)
      (Nat.le_succ payloadSize)
    simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      hsucc
  calc
    domainSectionRowsTime 0 domains ≤
        20 * domains.length * (0 + domains.length + payloadSize + 1) ^ 2 :=
      hrows
    _ ≤ 20 * payloadSize * (2 * (payloadSize + 1)) ^ 2 := by
      simpa [Nat.mul_assoc] using hscaled
    _ = 80 * (payloadSize * (payloadSize + 1) ^ 2) := by ring
    _ ≤ 80 * (payloadSize + 1) ^ 3 :=
      Nat.mul_le_mul_left 80 hcubic

private theorem domainSectionRunTime_le (domains : List (List ℕ)) :
    (match domains with
      | [] => 3
      | _ :: _ =>
          domainSectionRowsTime 0 domains +
            (DomainFieldSection.outputEncode domains).length +
              (encodeNat domains.length).length + 3) ≤
      100 * ((DomainFieldSection.rowPayloadEncode domains).length + 1) ^ 3 := by
  cases domains with
  | nil =>
      simp [DomainFieldSection.rowPayloadEncode, DomainFieldSection.rowFields,
        SourceOrderRawFields.encode]
  | cons domain domains =>
      let payloadSize :=
        (DomainFieldSection.rowPayloadEncode (domain :: domains)).length
      have hrows : domainSectionRowsTime 0 (domain :: domains) ≤
          80 * (payloadSize + 1) ^ 3 := by
        simpa only [payloadSize] using
          domainSectionRowsTime_zero_le_payload (domain :: domains)
      have houtput := domainSectionOutput_length_le_payload (domain :: domains)
      have hlength := domainSection_length_le_payload (domain :: domains)
      have hindex := BinaryNatLists.encodeNat_length_le
        (domain :: domains).length
      have houtput' :
          (DomainFieldSection.outputEncode (domain :: domains)).length ≤
            8 * (payloadSize + 1) ^ 2 := by
        simp only [payloadSize] at houtput ⊢
        nlinarith [sq_nonneg payloadSize]
      have hindex' : (encodeNat (domain :: domains).length).length ≤
          payloadSize := by
        simp only [payloadSize] at hlength ⊢
        omega
      have hone : 1 ≤ (payloadSize + 1) ^ 2 := by
        nlinarith [sq_nonneg payloadSize]
      have hpayloadSquare : payloadSize ≤ (payloadSize + 1) ^ 2 := by
        nlinarith [sq_nonneg payloadSize]
      have hrest :
          (DomainFieldSection.outputEncode (domain :: domains)).length +
                (encodeNat (domain :: domains).length).length + 3 ≤
            12 * (payloadSize + 1) ^ 2 := by
        omega
      have hquadCubic : 12 * (payloadSize + 1) ^ 2 ≤
          12 * (payloadSize + 1) ^ 3 := by
        have hmono := Nat.mul_le_mul_right ((payloadSize + 1) ^ 2)
          (show 1 ≤ payloadSize + 1 by omega)
        have hpower : (payloadSize + 1) ^ 2 ≤
            (payloadSize + 1) ^ 3 := by
          simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
            using hmono
        exact Nat.mul_le_mul_left 12 hpower
      have hrest' :
          (DomainFieldSection.outputEncode (domain :: domains)).length +
                (encodeNat (domain :: domains).length).length + 3 ≤
            12 * (payloadSize + 1) ^ 3 :=
        hrest.trans hquadCubic
      simp only
      simpa only [payloadSize] using
        (show domainSectionRowsTime 0 (domain :: domains) +
              (DomainFieldSection.outputEncode (domain :: domains)).length +
                (encodeNat (domain :: domains).length).length + 3 ≤
            100 * (payloadSize + 1) ^ 3 by omega)

/-- The complete domain-section machine emits the exact indexed occurrence
stream in cubic time in the checked row-payload bit length. -/
def domainSection_outputsInTime (domains : List (List ℕ)) :
    TM2OutputsInTime domainSectionComputer
      (DomainFieldSection.rowPayloadEncode domains)
      (some (DomainFieldSection.outputEncode domains))
      (100 * ((DomainFieldSection.rowPayloadEncode domains).length + 1) ^ 3) := by
  have hrun := domainSection_run_evals domains
  have hmono := domainSectionEvalsToInTimeMono hrun
    (domainSectionRunTime_le domains)
  rw [TM2OutputsInTime, domainSection_initList_eq_cfg]
  simp only [Option.map_some]
  rw [domainSection_haltList_eq_cfg]
  exact hmono

/-- A bit-level polynomial-time witness for traversing every checked domain
row, attaching its canonical zero-based variable index, and emitting every
tagged `(variable, value)` occurrence. -/
noncomputable def domainSectionComputableInPolyTime :
    @TM2ComputableInPolyTime (List (List ℕ)) (List (ℕ × ℕ))
      DomainFieldSection.rowPayloadFinEncoding DomainFieldRow.outputFinEncoding
      RuntimeStructuralView.indexedDomainOccurrences where
  tm := domainSectionComputer
  inputAlphabet := Equiv.refl (Option Bool)
  outputAlphabet := Equiv.refl (Option Bool)
  time := 100 * (Polynomial.X + 1) ^ 3
  outputsFun domains := by
    simpa [DomainFieldSection.rowPayloadFinEncoding,
      DomainFieldRow.outputFinEncoding, DomainFieldSection.outputEncode,
      Equiv.refl, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_pow, Polynomial.eval_natCast, Polynomial.eval_one,
      Polynomial.eval_X] using domainSection_outputsInTime domains

private noncomputable def completeDomainSectionComposition :
    @TM2ComputableInPolyTime (List (List ℕ)) (List (ℕ × ℕ))
      DomainFieldSection.inputFinEncoding DomainFieldRow.outputFinEncoding
      (RuntimeStructuralView.indexedDomainOccurrences ∘ id) :=
  compositionComputableInPolyTime
    DomainFieldSection.inputFinEncoding
    DomainFieldSection.rowPayloadFinEncoding
    DomainFieldRow.outputFinEncoding id
    RuntimeStructuralView.indexedDomainOccurrences
    domainRowPayloadStructuredComputableInPolyTime
    domainSectionComputableInPolyTime

/-- A genuine polynomial-time machine from the complete counted domain
section to the exact tagged occurrence stream.  This sequentially composes
the checked outer-count removal pass with the exhaustion-delimited indexed-row
driver, so the intermediate row payload is no longer a caller-supplied
assumption. -/
noncomputable def completeDomainSectionComputableInPolyTime :
    @TM2ComputableInPolyTime (List (List ℕ)) (List (ℕ × ℕ))
      DomainFieldSection.inputFinEncoding DomainFieldRow.outputFinEncoding
      RuntimeStructuralView.indexedDomainOccurrences := by
  let composed := completeDomainSectionComposition
  exact { composed with
    outputsFun := fun domains => by
      simpa [Function.comp_def] using composed.outputsFun domains }

#print axioms domainSection_outputsInTime
#print axioms domainSectionComputableInPolyTime
#print axioms completeDomainSectionComputableInPolyTime


end PhdThesisLean.AllDifferentCSPMachine
