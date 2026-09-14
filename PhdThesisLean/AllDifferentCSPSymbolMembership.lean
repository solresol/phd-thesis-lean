import PhdThesisLean.AllDifferentCSPSymbolMachine
import LeanNPHardness.PreservingBinaryEqualityMachine

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

/-!
# Membership in the extracted domain-symbol stream

The input is a checked pair of a canonical binary query and the existing
source-order symbol fields. Loading reverses both binary words, so the
upstream query-preserving equality kernel can compare them without a separate
reversal pass. Each candidate is consumed; the query is restored for the next
comparison. The final Boolean is membership, including empty and repeated
symbol lists. Deduplication and rank counting are later passes.
-/

namespace DomainSymbolMembership

abbrev Input := ℕ × List ℕ

def finEncoding : FinEncoding Input :=
  LeanNPHardness.PairEncoding.finEncoding finEncodingNatBool SourceOrderRawFields.finEncoding

def contains (input : Input) : Bool := decide (input.1 ∈ input.2)

end DomainSymbolMembership

namespace SymbolMembershipMachine

open LeanNPHardness.MachinePrimitives

abbrev Wire := Sum Bool (Option Bool)
abbrev Stack := Option PreservingBinaryEquality.Stack
abbrev Alphabet : Stack → Type
  | none => Wire | some _ => Bool

inductive Label
  | query | candidate | compare (label : PreservingBinaryEquality.Label) | checked | clear
  deriving DecidableEq, Fintype

structure State where
  core : PreservingBinaryEquality.State
  found : Bool
  last : Bool
  cell : Option Wire
  deriving DecidableEq, Fintype

def initialState : State := ⟨PreservingBinaryEquality.initialState, false, false, none⟩

private def observe (state : State) (cell : Option Wire) : State := { state with cell := cell }
private def queryBit (state : State) : Option Bool := state.cell.bind fun cell => cell.getLeft?
private def candidateBit (state : State) : Option Bool :=
  state.cell.bind fun cell => cell.getRight?.join
private def outcome (state : State) (bit : Option Bool) : State :=
  { state with found := state.found || bit.getD false }
private def clearBit (state : State) (bit : Option Bool) : State :=
  { state with core := { state.core with left := bit } }

/-- Embed the imported comparison statements; their halt returns to the
membership loop and all parser state and input cells are preserved. -/
def lift : TM2.Stmt PreservingBinaryEquality.Alphabet PreservingBinaryEquality.Label PreservingBinaryEquality.State → TM2.Stmt Alphabet Label State
  | .push k write next => .push (some k) (fun state => write state.core) (lift next)
  | .peek k read next => .peek (some k)
      (fun state bit => { state with core := read state.core bit }) (lift next)
  | .pop k read next => .pop (some k)
      (fun state bit => { state with core := read state.core bit }) (lift next)
  | .load update next => .load (fun state => { state with core := update state.core }) (lift next)
  | .branch test yes no => .branch (fun state => test state.core) (lift yes) (lift no)
  | .goto next => .goto (fun state => .compare (next state.core))
  | .halt => .goto (fun _ => .checked)

def program : Label → TM2.Stmt Alphabet Label State
  | .query => .pop none observe <| .branch (fun state => (queryBit state).isSome)
      (.push (some .query) (fun state => (queryBit state).getD false) <| .goto (fun _ => .query))
      (.branch (fun state => state.cell.isSome)
        (.goto (fun _ => .candidate)) (.goto (fun _ => .clear)))
  | .candidate => .pop none observe <| .branch (fun state => (candidateBit state).isSome)
      (.push (some .candidate) (fun state => (candidateBit state).getD false) <|
        .goto (fun _ => .candidate))
      (.load (fun state => { state with last := state.cell.isNone }) <|
        .goto (fun _ => .compare .scan))
  | .compare label => lift (PreservingBinaryEquality.program label)
  | .checked => .pop (some .output) outcome <| .branch (fun state => state.last)
      (.goto (fun _ => .clear)) (.goto (fun _ => .candidate))
  | .clear => .pop (some .query) clearBit <| .branch (fun state => state.core.left.isSome)
      (.goto (fun _ => .clear))
      (.push (some .output) (fun state => state.found) <| .load (fun _ => initialState) .halt)

def computer : FinTM2 where
  K := Stack
  k₀ := none
  k₁ := some .output
  Γ := Alphabet
  Λ := Label
  main := .query
  σ := State
  initialState := initialState
  Γk₀Fin := inferInstance
  m := program

private def stackContents (input : List Wire) (contents : PreservingBinaryEquality.Stack → List Bool) :
    (k : Stack) → List (Alphabet k)
  | none => input | some k => contents k

private def embed (input : List Wire) (state : State) (config : PreservingBinaryEquality.computer.Cfg) : computer.Cfg :=
  ⟨some (config.l.elim .checked .compare), { state with core := config.var },
    stackContents input config.stk⟩

private theorem stacks_update (input : List Wire) (contents : PreservingBinaryEquality.Stack → List Bool)
    (k : PreservingBinaryEquality.Stack) (value : List Bool) :
    stackContents input (Function.update contents k value) =
      Function.update (stackContents input contents) (some k) value := by
  funext index
  cases index with
  | none => simp [stackContents]
  | some index =>
      by_cases h : index = k
      · subst index; simp [stackContents]
      · simp [stackContents, Function.update, h]

private theorem lift_stepAux (stmt : TM2.Stmt PreservingBinaryEquality.Alphabet PreservingBinaryEquality.Label PreservingBinaryEquality.State)
    (input : List Wire) (state : State) (contents : PreservingBinaryEquality.Stack → List Bool) :
    TM2.stepAux (lift stmt) state (stackContents input contents) =
      embed input state (TM2.stepAux stmt state.core contents) := by
  induction stmt generalizing state contents with
  | push k write next ih =>
      simp only [lift, TM2.stepAux, stackContents]
      rw [← stacks_update]
      exact ih _ _
  | peek k read next ih =>
      simpa only [lift, TM2.stepAux, stackContents, embed] using
        ih { state with core := read state.core (contents k).head? } contents
  | pop k read next ih =>
      simp only [lift, TM2.stepAux, stackContents]
      rw [← stacks_update]
      simpa only [embed] using ih { state with core := read state.core (contents k).head? }
        (Function.update contents k (contents k).tail)
  | load update next ih =>
      simpa only [lift, TM2.stepAux, embed] using ih { state with core := update state.core } contents
  | branch test yes no iy ino =>
      cases h : test state.core <;> simp only [lift, TM2.stepAux, h, cond_false, cond_true]
      · exact ino _ _
      · exact iy _ _
  | goto next => rfl
  | halt => rfl

private theorem compare_step (input : List Wire) (state : State) (config : PreservingBinaryEquality.computer.Cfg)
    (h : config.l ≠ none) :
    computer.step (embed input state config) = (PreservingBinaryEquality.computer.step config).map (embed input state) := by
  rcases config with ⟨label, core, contents⟩
  cases label with
  | none => simp at h
  | some label =>
      simp only [computer, FinTM2.step, embed, program, Option.elim_some,
        PreservingBinaryEquality.computer, TM2.step, Option.map_some]
      congr 1
      simpa only [embed] using lift_stepAux (PreservingBinaryEquality.program label) input
        { state with core := core } contents

private theorem compare_iterate (n : ℕ) (input : List Wire) (state : State)
    (start finish : PreservingBinaryEquality.computer.Cfg)
    (h : (fun c => c.bind PreservingBinaryEquality.computer.step)^[n] (some start) = some finish) :
    (fun c => c.bind computer.step)^[n] (some (embed input state start)) =
      some (embed input state finish) := by
  induction n generalizing start with
  | zero => simpa using congrArg (Option.map (embed input state)) h
  | succ n ih =>
      have hn : (fun c => c.bind PreservingBinaryEquality.computer.step)^[n] none = none := by
        exact Function.iterate_fixed (by rfl) n
      rw [Function.iterate_succ_apply] at h ⊢
      change (fun c => c.bind PreservingBinaryEquality.computer.step)^[n]
        (PreservingBinaryEquality.computer.step start) = some finish at h
      change (fun c => c.bind computer.step)^[n]
        (computer.step (embed input state start)) = _
      have hl : start.l ≠ none := by
        intro hl
        have hs : PreservingBinaryEquality.computer.step start = none := by
          rcases start with ⟨label, core, contents⟩
          change label = none at hl
          subst label
          rfl
        rw [hs, hn] at h
        contradiction
      rw [compare_step input state start hl]
      cases hs : PreservingBinaryEquality.computer.step start with
      | none => rw [hs, hn] at h; contradiction
      | some mid =>
          simp only [Option.map_some]
          exact ih mid (by rw [hs] at h; exact h)

private def cfg (label : Option Label) (state : State) (input : List Wire)
    (query candidate scratch output : List Bool) : computer.Cfg :=
  ⟨label, state, stackContents input (PreservingBinaryEquality.stackContents query candidate scratch output)⟩

private abbrev Run (a b : computer.Cfg) (time : ℕ) := EvalsToInTime computer.step a (some b) time
private def one {a b : computer.Cfg} (h : computer.step a = some b) : Run a b 1 :=
  { steps := 1, evals_in_steps := by simpa [Function.iterate_one] using h, steps_le_m := le_rfl }
private def seq {a b c : computer.Cfg} {m n : ℕ}
    (h : Run a b m) (h' : Run b c n) : Run a c (m + n) := by
  simpa [Nat.add_comm] using EvalsToInTime.trans computer.step m n a b (some c) h h'

/-- The imported kernel is reused at the exact loaded-word boundary. -/
private def compare_run (input : List Wire) (state : State) (query candidate : List Bool) :
    Run (cfg (some (.compare .scan)) { state with core := PreservingBinaryEquality.initialState }
        input query candidate [] [])
      (cfg (some .checked) { state with core := PreservingBinaryEquality.initialState }
        input query [] [] [decide (query = candidate)])
      (2 * query.length + candidate.length + 2) where
  steps := max query.length candidate.length + query.length + 2
  evals_in_steps := by
    simpa only [embed, cfg, PreservingBinaryEquality.cfg, Option.elim_some, Option.elim_none] using
      compare_iterate _ input state _ _ (PreservingBinaryEquality.whole_list query candidate [])
  steps_le_m := by omega

local macro "membership_step" : tactic => `(tactic|
  (simp [computer, FinTM2.step, cfg, program, stackContents, Alphabet,
    PreservingBinaryEquality.stackContents, observe, queryBit, candidateBit,
    outcome, clearBit, Function.update]
   <;> first | rfl | (funext k; cases k with
     | none => rfl
     | some k => cases k <;> rfl)))

private def query_load (bits saved : List Bool) (rest : List Wire) (state : State) :
    Run (cfg (some .query) state (bits.map Sum.inl ++ .inr none :: rest) saved [] [] [])
      (cfg (some .candidate) { state with cell := some (.inr none) }
        rest (bits.reverse ++ saved) [] [] []) (bits.length + 1) := by
  induction bits generalizing saved state with
  | nil => exact one (by membership_step)
  | cons bit bits ih =>
      have h : Run (cfg (some .query) state ((.inl bit) :: (bits.map Sum.inl ++ .inr none :: rest))
          saved [] [] [])
          (cfg (some .query) { state with cell := some (.inl bit) }
            (bits.map Sum.inl ++ .inr none :: rest) (bit :: saved) [] [] []) 1 :=
        one (by membership_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using seq h (ih (bit :: saved) { state with cell := some (.inl bit) })

private def query_empty (bits saved : List Bool) (state : State) :
    Run (cfg (some .query) state (bits.map Sum.inl) saved [] [] [])
      (cfg (some .clear) { state with cell := none }
        [] (bits.reverse ++ saved) [] [] []) (bits.length + 1) := by
  induction bits generalizing saved state with
  | nil => exact one (by membership_step)
  | cons bit bits ih =>
      have h : Run (cfg (some .query) state (.inl bit :: bits.map Sum.inl) saved [] [] [])
          (cfg (some .query) { state with cell := some (.inl bit) }
            (bits.map Sum.inl) (bit :: saved) [] [] []) 1 := one (by membership_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using seq h (ih (bit :: saved) { state with cell := some (.inl bit) })

private def candidate_load (bits query saved : List Bool) (rest : List Wire) (state : State) :
    Run (cfg (some .candidate) state
        (bits.map (fun bit => .inr (some bit)) ++ .inr none :: rest) query saved [] [])
      (cfg (some (.compare .scan)) { state with last := false, cell := some (.inr none) }
        rest query (bits.reverse ++ saved) [] []) (bits.length + 1) := by
  induction bits generalizing saved state with
  | nil => exact one (by membership_step)
  | cons bit bits ih =>
      have h : Run (cfg (some .candidate) state
          (.inr (some bit) :: (bits.map (fun bit => .inr (some bit)) ++ .inr none :: rest))
          query saved [] [])
          (cfg (some .candidate) { state with cell := some (.inr (some bit)) }
            (bits.map (fun bit => .inr (some bit)) ++ .inr none :: rest)
            query (bit :: saved) [] []) 1 := one (by membership_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using seq h (ih (bit :: saved) { state with cell := some (.inr (some bit)) })

private def candidate_last (bits query saved : List Bool) (state : State) :
    Run (cfg (some .candidate) state (bits.map (fun bit => .inr (some bit))) query saved [] [])
      (cfg (some (.compare .scan)) { state with last := true, cell := none }
        [] query (bits.reverse ++ saved) [] []) (bits.length + 1) := by
  induction bits generalizing saved state with
  | nil => exact one (by membership_step)
  | cons bit bits ih =>
      have h : Run (cfg (some .candidate) state
          (.inr (some bit) :: bits.map (fun bit => .inr (some bit))) query saved [] [])
          (cfg (some .candidate) { state with cell := some (.inr (some bit)) }
            (bits.map (fun bit => .inr (some bit))) query (bit :: saved) [] []) 1 :=
        one (by membership_step)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using seq h (ih (bit :: saved) { state with cell := some (.inr (some bit)) })

private def clear_run (query : List Bool) (state : State) :
    Run (cfg (some .clear) state [] query [] [] [])
      (cfg none initialState [] [] [] [] [state.found]) (query.length + 1) := by
  induction query generalizing state with
  | nil => exact one (by membership_step)
  | cons bit query ih =>
      have h : Run (cfg (some .clear) state [] (bit :: query) [] [] [])
          (cfg (some .clear) { state with core := { state.core with left := some bit } }
            [] query [] [] []) 1 := one (by membership_step)
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        seq h (ih { state with core := { state.core with left := some bit } })

private def ready (found last : Bool) (cell : Option Wire) : State :=
  ⟨PreservingBinaryEquality.initialState, found, last, cell⟩

private def candidateWire (value : ℕ) (rest : List ℕ) : List Wire :=
  (encodeNat value).map (fun bit => .inr (some bit)) ++
    (SourceOrderRawFields.encode rest).map Sum.inr

private def cost (query : ℕ) : List ℕ → ℕ
  | [] => 0
  | value :: values => 2 * (encodeNat query).length + 2 * (encodeNat value).length + 4 + cost query values

private theorem reversed_eq (query value : ℕ) :
    decide ((encodeNat query).reverse = (encodeNat value).reverse) = decide (query = value) := by
  simp only [List.reverse_inj, BinaryEquality.encodeNat_eq_iff]

/-- Every candidate is read and compared, even after a previous match. -/
private def candidates_run (query value : ℕ) (values : List ℕ)
    (found last : Bool) (cell : Option Wire) :
    Run (cfg (some .candidate) (ready found last cell) (candidateWire value values)
        (encodeNat query).reverse [] [] [])
      (cfg (some .clear) (ready (found || decide (query ∈ value :: values)) true none)
        [] (encodeNat query).reverse [] [] []) (cost query (value :: values)) := by
  induction values generalizing value found last cell with
  | nil =>
      have hl := candidate_last (encodeNat value) (encodeNat query).reverse [] (ready found last cell)
      simp only [List.append_nil] at hl
      have hc := compare_run [] (ready found true none) (encodeNat query).reverse (encodeNat value).reverse
      simp only [ready, List.length_reverse, reversed_eq] at hc
      have he : Run (cfg (some .checked) (ready found true none) [] (encodeNat query).reverse
          [] [] [decide (query = value)])
          (cfg (some .clear) (ready (found || decide (query = value)) true none)
            [] (encodeNat query).reverse [] [] []) 1 := one (by dsimp only [ready]; membership_step)
      convert seq (seq hl hc) he using 1 <;>
        (simp [candidateWire, SourceOrderRawFields.encode, ready, cost]; all_goals omega)
  | cons next values ih =>
      have hw : candidateWire value (next :: values) =
          (encodeNat value).map (fun bit => .inr (some bit)) ++ .inr none :: candidateWire next values := by
        simp [candidateWire, SourceOrderRawFields.encode, List.map_append,
          List.map_map, Function.comp_def]
      rw [hw]
      have hl := candidate_load (encodeNat value) (encodeNat query).reverse []
        (candidateWire next values) (ready found last cell)
      simp only [List.append_nil] at hl
      have hc := compare_run (candidateWire next values) (ready found false (some (.inr none)))
        (encodeNat query).reverse (encodeNat value).reverse
      simp only [ready, List.length_reverse, reversed_eq] at hc
      have he : Run (cfg (some .checked) (ready found false (some (.inr none)))
          (candidateWire next values) (encodeNat query).reverse [] [] [decide (query = value)])
          (cfg (some .candidate) (ready (found || decide (query = value)) false (some (.inr none)))
            (candidateWire next values) (encodeNat query).reverse [] [] []) 1 := one (by dsimp only [ready]; membership_step)
      have hr := ih next (found || decide (query = value)) false (some (.inr none))
      convert seq (seq (seq hl hc) he) hr using 1 <;>
        (simp [ready, cost, Bool.or_assoc]; all_goals omega)

private theorem fields_length_cons (value : ℕ) (values : List ℕ) :
    (SourceOrderRawFields.encode (value :: values)).length =
      (encodeNat value).length + 1 + (SourceOrderRawFields.encode values).length := by
  simp [SourceOrderRawFields.encode, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

private theorem cost_le (query : ℕ) (values : List ℕ) :
    cost query values ≤
      (2 * (encodeNat query).length + 4) * (SourceOrderRawFields.encode values).length := by
  induction values with
  | nil => simp [cost, SourceOrderRawFields.encode]
  | cons value values ih =>
      rw [cost, fields_length_cons]
      nlinarith

private theorem input_length (query : ℕ) (values : List ℕ) :
    (DomainSymbolMembership.finEncoding.encode (query, values)).length =
      (encodeNat query).length + (SourceOrderRawFields.encode values).length := by
  simp [DomainSymbolMembership.finEncoding,
    finEncodingNatBool, encodingNatBool, SourceOrderRawFields.finEncoding]

private def run (query : ℕ) (values : List ℕ) :
    Run (cfg (some .query) initialState (DomainSymbolMembership.finEncoding.encode (query, values))
        [] [] [] [])
      (cfg none initialState [] [] [] [] [decide (query ∈ values)])
      (6 * ((DomainSymbolMembership.finEncoding.encode (query, values)).length + 1)^2) := by
  have hrun : Run
      (cfg (some .query) initialState (DomainSymbolMembership.finEncoding.encode (query, values))
        [] [] [] [])
      (cfg none initialState [] [] [] [] [decide (query ∈ values)])
      (2 * (encodeNat query).length + 2 + cost query values) := by
    cases values with
    | nil =>
        have hl := query_empty (encodeNat query) [] initialState
        simp only [List.append_nil] at hl
        have hc := clear_run (encodeNat query).reverse initialState
        convert seq hl hc using 1 <;>
          (simp [DomainSymbolMembership.finEncoding, LeanNPHardness.PairEncoding.finEncoding,
            finEncodingNatBool, encodingNatBool, SourceOrderRawFields.finEncoding,
            SourceOrderRawFields.encode, initialState, cost]; all_goals omega)
    | cons value values =>
        have hi : DomainSymbolMembership.finEncoding.encode (query, value :: values) =
            (encodeNat query).map Sum.inl ++ .inr none :: candidateWire value values := by
          simp [DomainSymbolMembership.finEncoding, LeanNPHardness.PairEncoding.finEncoding,
            finEncodingNatBool, encodingNatBool, SourceOrderRawFields.finEncoding,
            SourceOrderRawFields.encode, candidateWire, List.map_append, List.map_map,
            Function.comp_def]
        rw [hi]
        have hl := query_load (encodeNat query) [] (candidateWire value values) initialState
        simp only [List.append_nil] at hl
        have hr := candidates_run query value values false false (some (.inr none))
        have hc := clear_run (encodeNat query).reverse
          (ready (false || decide (query ∈ value :: values)) true none)
        convert seq (seq hl hr) hc using 1
        simp only [List.length_reverse]
        omega
  apply evalsToInTimeMono hrun
  rw [input_length]
  have h := cost_le query values
  nlinarith

private theorem init_eq (input : List Wire) :
    initList computer input = cfg (some .query) initialState input [] [] [] [] := by
  simp only [initList, computer, cfg]
  congr 1
  funext k
  cases k with
  | none => rfl
  | some k => cases k <;> rfl

private theorem halt_eq (output : List Bool) :
    haltList computer output = cfg none initialState [] [] [] [] output := by
  simp only [haltList, computer, cfg]
  congr 1
  funext k
  cases k with
  | none => rfl
  | some k => cases k <;> rfl

end SymbolMembershipMachine

/-- Decide membership directly from serialized binary query/symbol fields in
at most `6(s+1)^2` finite-machine steps for complete tagged input length `s`.
Every input and scratch stack is empty at halt. -/
def domainSymbolMembership_outputsInTime (input : DomainSymbolMembership.Input) :
    TM2OutputsInTime SymbolMembershipMachine.computer
      (DomainSymbolMembership.finEncoding.encode input)
      (some (finEncodingBoolBool.encode (DomainSymbolMembership.contains input)))
      (6 * ((DomainSymbolMembership.finEncoding.encode input).length + 1)^2) := by
  rcases input with ⟨query, values⟩
  rw [TM2OutputsInTime, SymbolMembershipMachine.init_eq]
  simp only [Option.map_some]
  rw [SymbolMembershipMachine.halt_eq]
  exact SymbolMembershipMachine.run query values

noncomputable def domainSymbolMembershipComputableInPolyTime :
    @TM2ComputableInPolyTime DomainSymbolMembership.Input Bool
      DomainSymbolMembership.finEncoding finEncodingBoolBool DomainSymbolMembership.contains where
  tm := SymbolMembershipMachine.computer
  inputAlphabet := Equiv.refl SymbolMembershipMachine.Wire
  outputAlphabet := Equiv.refl Bool
  time := 6 * (Polynomial.X + 1)^2
  outputsFun input := by
    simpa [Equiv.refl, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_natCast, Polynomial.eval_X] using domainSymbolMembership_outputsInTime input

#print axioms domainSymbolMembership_outputsInTime
#print axioms domainSymbolMembershipComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
