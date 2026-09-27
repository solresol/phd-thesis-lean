import PhdThesisLean.AllDifferentCSPScopeSection

/-!
# Expose the entries of one counted scope

Reuse the pinned counted-row header-removal machine. Its existing public
correctness theorem concerns whole sections of rows; here the same program
is checked on one scope, whose payload is an arbitrary list of natural fields.
No machine or binary arithmetic implementation is duplicated.
-/

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachinePrimitives

namespace ScopePayload

abbrev Stack := CountedRowPayloadStack
abbrev Label := CountedRowPayloadLabel
abbrev State := CountedRowPayloadState
abbrev computer := countedRowPayloadComputer

private def stackContents (input scratch output : List (Option Bool)) :
    (k : Stack) → List (computer.Γ k)
  | .input => input | .scratch => scratch | .output => output

private def cfg (label : Option Label) (state : State)
    (input scratch output : List (Option Bool)) : computer.Cfg :=
  ⟨label, state, stackContents input scratch output⟩

private abbrev Run (a b : computer.Cfg) (time : ℕ) :=
  EvalsToInTime computer.step a (some b) time

private def one {a b : computer.Cfg} (h : computer.step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using h,
    steps_le_m := le_rfl }

private def seq {a b c : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using EvalsToInTime.trans computer.step m n a b (some c) h h'

-- Definitional reduction uses the imported program, including its private
-- finite-state helpers; no implementation details are copied here.
local macro "payload_step" : tactic => `(tactic|
  (apply congrArg some
   change (⟨_, _, _⟩ : computer.Cfg) = ⟨_, _, _⟩
   congr 1 <;> first | rfl | (funext k; cases k <;> rfl)))

private def stash_run (input scratch output : List (Option Bool)) (state : State) :
    Run (cfg (some .stash) state input scratch output)
      (cfg (some .restore) none [] (input.reverse ++ scratch) output)
      (input.length + 1) := by
  induction input generalizing scratch state with
  | nil => exact one (by payload_step)
  | cons cell input ih =>
      have h : Run (cfg (some .stash) state (cell :: input) scratch output)
          (cfg (some .stash) (some cell) input (cell :: scratch) output) 1 :=
        one (by payload_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq h (ih (cell :: scratch) (some cell))

private def restore_run (scratch output : List (Option Bool)) (state : State) :
    Run (cfg (some .restore) state [] scratch output)
      (cfg none none [] [] (scratch.reverse ++ output)) (scratch.length + 1) := by
  induction scratch generalizing output state with
  | nil => exact one (by payload_step)
  | cons cell scratch ih =>
      have h : Run (cfg (some .restore) state [] (cell :: scratch) output)
          (cfg (some .restore) (some cell) [] scratch (cell :: output)) 1 :=
        one (by payload_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq h (ih (cell :: output) (some cell))

private def skip_run (bits : List Bool) (fields : List ℕ) (state : State) :
    Run (cfg (some .skipCount) state
        (bits.map some ++ SourceOrderRawFields.encode fields) [] [])
      (cfg (some .restore) none [] (SourceOrderRawFields.encode fields).reverse [])
      (bits.length + (SourceOrderRawFields.encode fields).length + 1) := by
  induction bits generalizing state with
  | nil =>
      cases fields with
      | nil => exact one (by payload_step)
      | cons value fields =>
          let tail := (encodeNat value).map some ++ SourceOrderRawFields.encode fields
          have h : Run (cfg (some .skipCount) state (none :: tail) [] [])
              (cfg (some .stash) (some none) tail [none] []) 1 := one (by payload_step)
          simpa [SourceOrderRawFields.encode, tail, List.reverse_cons,
            List.reverse_append, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
            Nat.add_assoc] using seq h (stash_run tail [none] [] (some none))
  | cons bit bits ih =>
      have h : Run (cfg (some .skipCount) state
          ((bit :: bits).map some ++ SourceOrderRawFields.encode fields) [] [])
          (cfg (some .skipCount) (some (some bit))
            (bits.map some ++ SourceOrderRawFields.encode fields) [] []) 1 :=
        one (by payload_step)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        seq h (ih (some (some bit)))

private def run (scope : List ℕ) :
    Run (cfg (some .start) none (ScopeFieldBlock.inputEncode scope) [] [])
      (cfg none none [] [] (SourceOrderRawFields.encode scope))
      ((encodeNat scope.length).length + 2 * (SourceOrderRawFields.encode scope).length + 3) := by
  have hstart : Run
      (cfg (some .start) none
        (none :: (encodeNat scope.length).map some ++ SourceOrderRawFields.encode scope) [] [])
      (cfg (some .skipCount) (some none)
        ((encodeNat scope.length).map some ++ SourceOrderRawFields.encode scope) [] []) 1 :=
    one (by payload_step)
  have hskip := skip_run (encodeNat scope.length) scope (some none)
  have hrestore := restore_run (SourceOrderRawFields.encode scope).reverse [] none
  convert seq (seq hstart hskip) hrestore using 1 <;>
    simp [SourceOrderRawFields.encode]
  omega

/-- The removed field is charged exactly, including its delimiter. -/
theorem input_length (scope : List ℕ) :
    (ScopeFieldBlock.inputFinEncoding.encode scope).length =
      (encodeNat scope.length).length + (SourceOrderRawFields.encode scope).length + 1 := by
  simp [ScopeFieldBlock.inputFinEncoding, ScopeFieldBlock.inputEncode,
    SourceOrderRawFields.encode, Nat.add_comm, Nat.add_left_comm]

private theorem init_eq (input : List (Option Bool)) :
    initList computer input = cfg (some .start) none input [] [] := by
  change (⟨_, _, _⟩ : computer.Cfg) = ⟨_, _, _⟩
  congr 1
  funext k
  cases k <;> rfl

private theorem halt_eq (output : List (Option Bool)) :
    haltList computer output = cfg none none [] [] output := by
  change (⟨_, _, _⟩ : computer.Cfg) = ⟨_, _, _⟩
  congr 1
  funext k
  cases k <;> rfl

end ScopePayload

/-- Remove one scope's checked count using the existing finite machine,
including empty scopes, in at most `2s+1` steps for complete input length `s`. -/
def scopePayload_outputsInTime (scope : List ℕ) :
    TM2OutputsInTime ScopePayload.computer
      (ScopeFieldBlock.inputFinEncoding.encode scope)
      (some (SourceOrderRawFields.finEncoding.encode scope))
      (2 * (ScopeFieldBlock.inputFinEncoding.encode scope).length + 1) := by
  rw [TM2OutputsInTime, ScopePayload.init_eq]
  simp only [Option.map_some]
  rw [ScopePayload.halt_eq]
  let h := ScopePayload.run scope
  exact { h with steps_le_m := h.steps_le_m.trans (by
    rw [ScopePayload.input_length]
    omega) }

noncomputable def scopePayloadComputableInPolyTime :
    @TM2ComputableInPolyTime (List ℕ) (List ℕ)
      ScopeFieldBlock.inputFinEncoding SourceOrderRawFields.finEncoding id where
  tm := ScopePayload.computer
  inputAlphabet := Equiv.refl (Option Bool)
  outputAlphabet := Equiv.refl (Option Bool)
  time := 2 * Polynomial.X + 1
  outputsFun scope := by
    simpa [Equiv.refl, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_natCast, Polynomial.eval_one, Polynomial.eval_X] using
      scopePayload_outputsInTime scope

#print axioms ScopePayload.input_length
#print axioms scopePayload_outputsInTime
#print axioms scopePayloadComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
