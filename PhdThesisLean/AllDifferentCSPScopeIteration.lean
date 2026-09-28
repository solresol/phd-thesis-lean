import PhdThesisLean.AllDifferentCSPScopeAccumulator

/-!
# One complete scope iteration with an explicit Boolean accumulator

Compose extraction, endpoint copying, same-scope membership testing and OR
accumulation. Each iteration consumes one complete counted scope, including
empty scopes, without losing either endpoint or any later scope. The finite
repeated dispatcher and its total runtime remain separate obligations.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

namespace ScopeIteration

abbrev Input := Bool × ScopeExtraction.Input
abbrev Output := ScopeAccumulator.Output

def inputFinEncoding : FinEncoding Input :=
  LeanNPHardness.PairEncoding.finEncoding finEncodingBoolBool ScopeExtraction.inputFinEncoding

abbrev outputFinEncoding := ScopeAccumulator.outputFinEncoding

/-- A nonempty loop state is already the exact iteration wire; no head/tail
split or re-encoding is supplied to the machine from outside. -/
theorem nonempty_encode (answer : Bool) (endpoints : ℕ × ℕ)
    (scope : List ℕ) (scopes : List (List ℕ)) :
    outputFinEncoding.encode (answer, endpoints, scope :: scopes) =
      inputFinEncoding.encode (answer, endpoints, scope, scopes) := rfl

def step (input : Input) : Output := ScopeAccumulator.update (input.1, ScopeTest.evaluate input.2)

theorem endpoints_preserved (input : Input) : (step input).2.1 = input.2.1 := rfl
theorem remaining_scopes (input : Input) : (step input).2.2 = input.2.2.2 := rfl

/-- The accumulated result together with the remaining question is invariant. -/
theorem adjacent_invariant (input : Input) :
    ((step input).1 || PrimalEdgeEnumeration.adjacent (step input).2.2
      (step input).2.1.1 (step input).2.1.2) =
    (input.1 || PrimalEdgeEnumeration.adjacent (input.2.2.1 :: input.2.2.2)
      input.2.1.1 input.2.1.2) := by
  rw [ScopeTest.adjacent_step input.2]
  simp only [step, ScopeAccumulator.update, Bool.or_assoc]

/-- The complete counted head is removed; the Boolean accumulator stays one cell. -/
theorem output_length_balance (input : Input) :
    (outputFinEncoding.encode (step input)).length +
        (ScopeFieldBlock.inputFinEncoding.encode input.2.2.1).length =
      (inputFinEncoding.encode input).length := by
  have test := ScopeTest.output_length_balance input.2
  have accumulated := ScopeAccumulator.output_length_balance
    (input.1, ScopeTest.evaluate input.2)
  simp only [ScopeAccumulator.inputFinEncoding, inputFinEncoding,
    LeanNPHardness.PairEncoding.finEncoding_encode_length] at accumulated ⊢
  have bit : (finEncodingBoolBool.encode input.1).length = 1 := by
    simp [finEncodingBoolBool, encodeBool]
  dsimp only [outputFinEncoding, ScopeAccumulator.outputFinEncoding,
    ScopeTest.inputFinEncoding, step] at test accumulated ⊢
  omega

/-- A counted empty scope still has a delimiter, so every iteration progresses. -/
theorem output_length_lt (input : Input) :
    (outputFinEncoding.encode (step input)).length <
      (inputFinEncoding.encode input).length := by
  have h := output_length_balance input
  have count := ScopePayload.input_length input.2.2.1
  omega

/-- Executable specification of the future repeated dispatcher. -/
def finish (endpoints : ℕ × ℕ) : List (List ℕ) → Bool → Bool
  | [], answer => answer
  | scope :: scopes, answer => finish endpoints scopes (step (answer, endpoints, scope, scopes)).1

theorem finish_eq (endpoints : ℕ × ℕ) (scopes : List (List ℕ)) (answer : Bool) :
    finish endpoints scopes answer =
      (answer || PrimalEdgeEnumeration.adjacent scopes endpoints.1 endpoints.2) := by
  induction scopes generalizing answer with
  | nil => simp [finish, PrimalEdgeEnumeration.adjacent]
  | cons scope scopes ih =>
      rw [finish, ih]
      exact adjacent_invariant (answer, endpoints, scope, scopes)

/-- Starting with no match computes the exact existential co-occurrence predicate.
This is semantic correspondence, not yet a repeated-machine runtime theorem. -/
theorem finish_false_eq_adjacent (endpoints : ℕ × ℕ) (scopes : List (List ℕ)) :
    finish endpoints scopes false = PrimalEdgeEnumeration.adjacent scopes endpoints.1 endpoints.2 := by
  simpa using finish_eq endpoints scopes false

example : finish (0, 1) [[], [0], [], [1]] false = false := by decide
example : finish (0, 1) [[], [0], [1, 0, 1], []] false = true := by decide
example : finish (0, 1) [[], []] true = true := by decide
example : finish (0, 0) [] false = false := rfl

end ScopeIteration

/-- Every operation in one full iteration is charged to the actual encoded
input, including preservation of the old Boolean result through scope testing. -/
noncomputable def scopeIterationComputableInPolyTime :
    @TM2ComputableInPolyTime ScopeIteration.Input ScopeIteration.Output
      ScopeIteration.inputFinEncoding ScopeIteration.outputFinEncoding ScopeIteration.step := by
  let tested := LeanNPHardness.MachineAdapters.pairRightComputableInPolyTime
    finEncodingBoolBool ScopeTest.inputFinEncoding ScopeTest.outputFinEncoding
    ScopeTest.evaluate scopeTestComputableInPolyTime
  let composed := compositionComputableInPolyTime _ _ _ _ _
    tested scopeAccumulatorComputableInPolyTime
  exact composed

#print axioms ScopeIteration.nonempty_encode
#print axioms ScopeIteration.adjacent_invariant
#print axioms ScopeIteration.output_length_balance
#print axioms ScopeIteration.output_length_lt
#print axioms ScopeIteration.finish_false_eq_adjacent
#print axioms scopeIterationComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
