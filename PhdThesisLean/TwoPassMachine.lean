import PhdThesisLean.SignedThreeSatReduction
import PhdThesisLean.FixedPrimeMaxCutMachine

/-!
# A two-pass interpreter machine over unary CNF input

Several reductions from CNF-SAT stream one row family clause by clause and also need one
Boolean forcing pair per literal occurrence. A single pass cannot interleave the two:
each output clause must be contiguous, and the four interpreter registers cannot hold
the indices of every literal of a clause. This module provides a reusable machine that
builds one interpreter job in two passes.

* The first pass reads the input with a caller-supplied chunk function `ch1` and keeps a
  reversed copy of the input on the `xkeep` stack (`loopKeepInput`).
* A separator closes the last clause opened by the first pass.
* The second pass reads the reversed copy (`loopKeep`), so the marks of each literal
  arrive before its sign symbol. With the standard chunk function `chunk2`, `win`
  counts the literal index and the sign symbol emits the forcing pair on it
  (`render_pass2`, which renders `SignedThreeSatReduction.occurrenceRows`).
* A fixed suffix emits the bound clause from `pw`.

The prefix, first-pass chunks, separator and second-pass chunks are parameters;
`chunk2` with the separator `[.endClause]` is the standard second pass. `R_exits` is
the exact run from the input alone to the rendered job alone, for any valid job, and
`cost_le` bounds the run by `10⁶ (n + 1)²` whenever the registers stay at most
`20n + 40` and the job has length at most `60n + 15`; `prefixLE_job` and
`job_length_le` discharge these from per-block facts (`BlockBounded`, `ChunkBounded`).
`outputsInTime` packages the bounded run for `TM2ComputableInPolyTime`.
-/

namespace PhdThesisLean.TwoPassMachine

open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime
open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat
open Polynomial StateTransition
open LeanNPHardness (FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime)
open LeanNPHardness LeanNPHardness.CNF LeanNPHardness.CNF.Unary LeanNPHardness.TableauJobs
open LeanNPHardness.TableauStacks LeanNPHardness.Routines LeanNPHardness.MachinePrimitives
open PhdThesisLean.PadicRegressionLanguage PhdThesisLean.SignedThreeSatReduction
open PhdThesisLean.FixedPrimeMaxCutJob (regs regs_base regs_win regs_w regs_pw update_base
  update_win update_pw regsLE_regs Bounded)
open PhdThesisLean.FixedPrimeMaxCutMachine (E push_reg regStacks)

private alias pcons := FixedPrimeMaxCutJob.prefixLE_cons
private alias pnil := FixedPrimeMaxCutJob.prefixLE_nil

/-! ### The job -/

/-- The forcing pair on the literal index held by `win`. -/
def forcingJob : List Instr :=
  [.lit true, .lit true, .reg .win, .endClause,
    .lit true, .lit true, .reg .win, .lit true, .endClause]

/-- Second-pass chunks, read on the reversed input: count a literal's marks, then emit
its forcing pair at its sign symbol. -/
def chunk2 : Sym → List Instr
  | .mark => [.addTo .win .w]
  | .pos => forcingJob ++ [.clear .win, .addTo .win .w]
  | .neg => forcingJob ++ [.clear .win, .addTo .win .w]
  | .endClause => []

/-- The job of a chunk function on a symbol list. -/
def jobOf (ch : Sym → List Instr) (L : List Sym) : List Instr := (L.map ch).flatten

theorem jobOf_append (ch : Sym → List Instr) (L M : List Sym) :
    jobOf ch (L ++ M) = jobOf ch L ++ jobOf ch M := by simp [jobOf]

/-- The bound clause. -/
def suffix : List Instr := [.lit true, .reg .pw, .endClause]

/-- The whole job of an input: prefix, first pass, separator, second pass on the
reversed input, bound clause. -/
def job (pre : List Instr) (ch1 : Sym → List Instr) (sep : List Instr) (ch2 : Sym → List Instr)
    (x : List Sym) : List Instr :=
  pre ++ jobOf ch1 x ++ sep ++ jobOf ch2 x.reverse ++ suffix

/-! ### Rendering the second pass -/

theorem reverse_encode (F : Formula ℕ) :
    (encode F).reverse = F.reverse.flatMap fun c =>
      Sym.endClause :: c.reverse.flatMap fun l => (encodeLiteral l).reverse := by
  induction F with
  | nil => rfl
  | cons c F ih =>
      rw [encode_cons, List.reverse_append, ih, List.reverse_cons, List.flatMap_append]
      simp [encodeClause, List.reverse_flatMap, Function.comp_def]

theorem render_lit2 (k : ℕ) (l : Literal ℕ) :
    render (regs 0 1 k) (jobOf chunk2 (encodeLiteral l).reverse) =
      (encode ((forcingRows (litVar l + 1)).map signedClause), regs 0 1 k) := by
  have hm : ∀ v i, render (regs 0 i k) (jobOf chunk2 (List.replicate v .mark)) =
      ([], regs 0 (i + v) k) := by
    intro v
    induction v with
    | zero => intro i; simp [jobOf, render]
    | succ v ih =>
        intro i
        rw [List.replicate_succ, show Sym.mark :: List.replicate v Sym.mark =
          [Sym.mark] ++ List.replicate v Sym.mark from rfl, jobOf_append, render_append]
        simp only [jobOf, chunk2, List.map_cons, List.map_nil, List.flatten_cons,
          List.flatten_nil, List.append_nil, render, renderInstr] at ih ⊢
        simp only [regs_win, regs_w, update_win, List.nil_append]
        rw [ih]
        ring_nf
  have hs : ∀ (s : Sym), s = .pos ∨ s = .neg → ∀ v,
      render (regs 0 (1 + v) k) (jobOf chunk2 [s]) =
        (encode ((forcingRows (v + 1)).map signedClause), regs 0 1 k) := by
    intro s hs v
    rcases hs with rfl | rfl <;>
      simp [jobOf, chunk2, forcingJob, render, renderInstr, forcingRows, signedClause, marker,
        encode, encodeClause, encodeLiteral, Nat.add_comm]
  cases l with
  | positive v =>
      rw [encodeLiteral, List.reverse_cons, List.reverse_replicate, jobOf_append, render_append,
        hm]
      simp only [List.nil_append]
      exact hs _ (Or.inl rfl) v
  | negative v =>
      rw [encodeLiteral, List.reverse_cons, List.reverse_replicate, jobOf_append, render_append,
        hm]
      simp only [List.nil_append]
      exact hs _ (Or.inr rfl) v

theorem render_lits2 (k : ℕ) (L : List (Literal ℕ)) :
    render (regs 0 1 k) (jobOf chunk2 (L.flatMap fun l => (encodeLiteral l).reverse)) =
      (encode ((L.flatMap fun l => forcingRows (litVar l + 1)).map signedClause), regs 0 1 k) := by
  induction L with
  | nil => simp [jobOf, render, encode]
  | cons l L ih =>
      rw [List.flatMap_cons, jobOf_append, render_append, render_lit2]
      simp only
      rw [ih, List.flatMap_cons, List.map_append, encode_append]

theorem render_pass2 (k : ℕ) (F : Formula ℕ) :
    render (regs 0 1 k) (jobOf chunk2 (encode F).reverse) =
      (encode ((occurrenceRows F).map signedClause), regs 0 1 k) := by
  rw [reverse_encode, occurrenceRows]
  induction F.reverse with
  | nil => simp [jobOf, render, encode]
  | cons c G ih =>
      rw [List.flatMap_cons, jobOf_append, render_append, List.flatMap_cons, List.map_append,
        encode_append]
      have hc : jobOf chunk2 (Sym.endClause :: c.reverse.flatMap
          fun l => (encodeLiteral l).reverse) =
          jobOf chunk2 (c.reverse.flatMap fun l => (encodeLiteral l).reverse) := by
        simp [jobOf, chunk2]
      rw [hc, render_lits2]
      simp only
      rw [ih]

/-! ### Register bounds -/

/-- An instruction block keeping registers bounded: started with `base` and `win` at
most `c` and `pw` at most `d`, every prefix keeps registers at most `M`, and the bounds
grow by at most `3` and `9`. -/
def BlockBounded (J : List Instr) : Prop :=
  ∀ {M c d : ℕ} {R : Regs}, Bounded c d R → 2 ≤ c → c + 3 ≤ M → d + 9 ≤ M →
    PrefixLE M R J ∧ Bounded (c + 3) (d + 9) (render R J).2

/-- Chunk functions keeping registers bounded. -/
def ChunkBounded (ch : Sym → List Instr) : Prop := ∀ s, BlockBounded (ch s)

theorem chunk2_bounded : ChunkBounded chunk2 := by
  intro s M c d R h _hc hcM hdM
  obtain ⟨b, i, k, rfl, hb, hi, hk⟩ := h
  cases s with
  | mark =>
      refine ⟨pcons ?_ (pnil ?_), ⟨b, i + 1, k, by
        simp [chunk2, render, renderInstr], by omega, by omega, by omega⟩⟩ <;>
        simp [renderInstr, regsLE_regs] <;> omega
  | pos =>
      refine ⟨?_, ⟨b, 1, k, by simp [chunk2, forcingJob, render, renderInstr], by omega,
        by omega, by omega⟩⟩
      simp only [chunk2, forcingJob, List.cons_append, List.nil_append]
      repeat' refine pcons ?_ ?_
      all_goals first
        | (refine pnil ?_; simp [renderInstr, regsLE_regs]; omega)
        | (simp [renderInstr, regsLE_regs]; omega)
  | neg =>
      refine ⟨?_, ⟨b, 1, k, by simp [chunk2, forcingJob, render, renderInstr], by omega,
        by omega, by omega⟩⟩
      simp only [chunk2, forcingJob, List.cons_append, List.nil_append]
      repeat' refine pcons ?_ ?_
      all_goals first
        | (refine pnil ?_; simp [renderInstr, regsLE_regs]; omega)
        | (simp [renderInstr, regsLE_regs]; omega)
  | endClause =>
      refine ⟨pnil ?_, ⟨b, i, k, by simp [chunk2, render], by omega, by omega,
        by omega⟩⟩
      rw [regsLE_regs]; omega

theorem jobOf_bounds (ch : Sym → List Instr) (hch : ChunkBounded ch)
    (L : List Sym) : ∀ {M c d : ℕ} {R : Regs}, Bounded c d R → 2 ≤ c →
    c + 3 * L.length ≤ M → d + 9 * L.length ≤ M →
    PrefixLE M R (jobOf ch L) ∧
      Bounded (c + 3 * L.length) (d + 9 * L.length) (render R (jobOf ch L)).2 := by
  induction L with
  | nil =>
      intro M c d R h hc hcM hdM
      refine ⟨pnil ?_, by simpa [jobOf, render] using h⟩
      obtain ⟨b, i, k, rfl, hb, hi, hk⟩ := h
      rw [regsLE_regs]
      simp at hcM hdM
      omega
  | cons s L ih =>
      intro M c d R h hc hcM hdM
      simp only [List.length_cons] at hcM hdM
      obtain ⟨h1, h2⟩ := hch s (M := M) h hc (by omega) (by omega)
      have hjob : jobOf ch (s :: L) = ch s ++ jobOf ch L := by simp [jobOf]
      obtain ⟨h3, h4⟩ := ih (M := M) h2 (by omega) (by omega) (by omega)
      refine ⟨by rw [hjob]; exact prefixLE_append h1 h3, ?_⟩
      rw [hjob, MachineTableau.render_append_snd, List.length_cons,
        show c + 3 * (L.length + 1) = c + 3 + 3 * L.length by ring,
        show d + 9 * (L.length + 1) = d + 9 + 9 * L.length by ring]
      exact h4

theorem bounded_mono {c d c' d' : ℕ} {R : Regs} (h : Bounded c d R) (hc : c ≤ c')
    (hd : d ≤ d') : Bounded c' d' R := by
  obtain ⟨b, i, k, rfl, hb, hi, hk⟩ := h
  exact ⟨b, i, k, rfl, by omega, by omega, by omega⟩

theorem prefixLE_pure_bounded {M c d : ℕ} {R : Regs} {J : List Instr} (h : ∀ i ∈ J, i.pure)
    (hR : Bounded c d R) (hc : c ≤ M) (hd : d ≤ M) (h1 : 1 ≤ M) :
    PrefixLE M R J ∧ Bounded c d (render R J).2 := by
  obtain ⟨b, i, k, rfl, hb, hi, hk⟩ := hR
  refine ⟨TableauJobs.prefixLE_of_pure h (by rw [regsLE_regs]; omega), ?_⟩
  rw [TableauJobs.render_pure_snd _ _ h]
  exact ⟨b, i, k, rfl, hb, hi, hk⟩

theorem blockBounded_of_pure {J : List Instr} (h : ∀ i ∈ J, i.pure) : BlockBounded J := by
  intro M c d R hR hc hcM hdM
  obtain ⟨p, b⟩ := prefixLE_pure_bounded (M := M) h hR (by omega) (by omega) (by omega)
  exact ⟨p, bounded_mono b (by omega) (by omega)⟩

/-- Weaken per-symbol bounds `(c + 1, d + 3)` to those of `BlockBounded`. -/
theorem blockBounded_of_small {J : List Instr}
    (h : ∀ {M c d : ℕ} {R : Regs}, Bounded c d R → 2 ≤ c → c + 1 ≤ M → d + 3 ≤ M →
      PrefixLE M R J ∧ Bounded (c + 1) (d + 3) (render R J).2) : BlockBounded J := by
  intro M c d R hR hc hcM hdM
  obtain ⟨p, b⟩ := h (M := M) hR hc (by omega) (by omega)
  exact ⟨p, bounded_mono b (by omega) (by omega)⟩

/-- Every register stays at most `20n + 40` while the job of an input of length `n`
runs. -/
theorem prefixLE_job (pre : List Instr) (ch1 : Sym → List Instr) (sep : List Instr)
    (ch2 : Sym → List Instr) (hpre : BlockBounded pre) (h1 : ChunkBounded ch1)
    (hsep : BlockBounded sep) (h2 : ChunkBounded ch2) (x : List Sym) :
    PrefixLE (20 * x.length + 40) (regs 0 1 0) (job pre ch1 sep ch2 x) := by
  set n := x.length
  have h0 : Bounded 2 0 (regs 0 1 0) := ⟨0, 1, 0, rfl, by omega, by omega, le_rfl⟩
  obtain ⟨p0, b0⟩ := hpre (M := 20 * n + 40) h0 le_rfl (by omega) (by omega)
  obtain ⟨p1, b1⟩ := jobOf_bounds ch1 h1 x (M := 20 * n + 40) b0
    (by omega) (by omega) (by omega)
  obtain ⟨p2, b2⟩ := hsep (M := 20 * n + 40) b1 (by omega) (by omega) (by omega)
  obtain ⟨p3, b3⟩ := jobOf_bounds ch2 h2 x.reverse
    (M := 20 * n + 40) b2 (by omega) (by simp; omega) (by simp; omega)
  obtain ⟨p4, _⟩ := prefixLE_pure_bounded (M := 20 * n + 40) (J := suffix)
    (by simp [suffix, Instr.pure]) b3 (by simp; omega) (by simp; omega) (by omega)
  have q1 := prefixLE_append p0 p1
  have q2 := prefixLE_append q1 (by rw [MachineTableau.render_append_snd]; exact p2)
  have q3 := prefixLE_append q2
    (by rw [MachineTableau.render_append_snd, MachineTableau.render_append_snd]; exact p3)
  have q4 := prefixLE_append q3
    (by rw [MachineTableau.render_append_snd, MachineTableau.render_append_snd,
      MachineTableau.render_append_snd]; exact p4)
  simpa [job, List.append_assoc] using q4

theorem job_length_le (pre : List Instr) (ch1 : Sym → List Instr) (sep : List Instr)
    (ch2 : Sym → List Instr) (hpre : pre.length ≤ 5) (h1 : ∀ s, (ch1 s).length ≤ 40)
    (hsep : sep.length ≤ 5) (h2 : ∀ s, (ch2 s).length ≤ 15) (x : List Sym) :
    (job pre ch1 sep ch2 x).length ≤ 60 * x.length + 15 := by
  have hl : ∀ (ch : Sym → List Instr) (k : ℕ), (∀ s, (ch s).length ≤ k) →
      ∀ L : List Sym, (jobOf ch L).length ≤ k * L.length := by
    intro ch k hk L
    induction L with
    | nil => simp [jobOf]
    | cons s L ih =>
        have := hk s
        simp only [jobOf, List.map_cons, List.flatten_cons, List.length_append,
          List.length_cons] at ih ⊢
        rw [Nat.mul_succ]
        omega
  have := hl ch1 40 h1 x
  have := hl ch2 15 h2 x.reverse
  simp only [job, suffix, List.length_append, List.length_cons, List.length_nil,
    List.length_reverse] at this ⊢
  omega

theorem job_ok (pre : List Instr) (ch1 : Sym → List Instr) (sep : List Instr)
    (ch2 : Sym → List Instr) (hpre : ∀ i ∈ pre, i.ok) (h1 : ∀ s, ∀ i ∈ ch1 s, i.ok)
    (hsep : ∀ i ∈ sep, i.ok) (h2 : ∀ s, ∀ i ∈ ch2 s, i.ok) (x : List Sym) :
    ∀ i ∈ job pre ch1 sep ch2 x, i.ok := by
  intro i hi
  simp only [job, suffix, List.mem_append] at hi
  rcases hi with (((h | h) | h) | h) | h
  · exact hpre i h
  · simp only [jobOf, List.mem_flatten, List.mem_map] at h
    obtain ⟨_, ⟨s, _, rfl⟩, h⟩ := h
    exact h1 s i h
  · exact hsep i h
  · simp only [jobOf, List.mem_flatten, List.mem_map] at h
    obtain ⟨_, ⟨s, _, rfl⟩, h⟩ := h
    exact h2 s i h
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with rfl | rfl | rfl <;> trivial

theorem chunk2_ok (s : Sym) : ∀ i ∈ chunk2 s, i.ok := by
  cases s <;> simp [chunk2, forcingJob, Instr.ok]

theorem chunk2_length_le (s : Sym) : (chunk2 s).length ≤ 15 := by
  cases s <;> simp [chunk2, forcingJob]

/-! ### The two input passes -/

/-- Emit a chunk per input symbol, keeping a reversed copy of the input on `xkeep`. -/
def loopKeepInput (f : Sym → List Instr) : GRoutine Sym :=
  loop .input (dispatch .input fun s => seq (emit (f s)) (pushList .xkeep [s]))

/-- Emit a chunk per symbol of the `xkeep` copy, consuming it. -/
def loopKeep (f : Sym → List Instr) : GRoutine Sym :=
  loop .xkeep (dispatch .xkeep fun s => emit (f s))

theorem loopKeepInput_exits (f : Sym → List Instr) (x xk : List Sym) (sk : List Instr) :
    (loopKeepInput f).Exits (emitStacks x xk 0 0 0 0 0 0 0 0 0 0 sk) (4 * x.length + 1)
      (emitStacks [] (x.reverse ++ xk) 0 0 0 0 0 0 0 0 0 0
        ((x.map f).flatten.reverse ++ sk)) := by
  have key := loop_exits (Γ := GAlphabet Sym) .input
    (dispatch .input fun s => seq (emit (f s)) (pushList .xkeep [s])) x.length
    (fun i => emitStacks (x.drop i) ((x.take i).reverse ++ xk) 0 0 0 0 0 0 0 0 0 0
      (((x.take i).map f).flatten.reverse ++ sk)) (fun _ => 3) ?_ ?_ ?_
  · have hsteps : loopSteps (fun _ => 3) x.length = 4 * x.length + 1 := by
      rw [loopSteps_eq_sum]; simp; omega
    rw [hsteps] at key
    simpa using! key
  · intro i hi
    have hsplit : (x.drop i) = x[i] :: x.drop (i + 1) := List.drop_eq_getElem_cons hi
    have em := emit_exits (Γx := Sym) (f x[i]) (x.drop (i + 1)) ((x.take i).reverse ++ xk)
      0 0 0 0 0 0 0 0 0 0 (((x.take i).map f).flatten.reverse ++ sk)
    have pu := pushList_exits (Γ := GAlphabet Sym) .xkeep [x[i]]
      (emitStacks (x.drop (i + 1)) ((x.take i).reverse ++ xk) 0 0 0 0 0 0 0 0 0 0
        ((f x[i]).reverse ++ (((x.take i).map f).flatten.reverse ++ sk)))
    have hpu : Function.update (emitStacks (x.drop (i + 1)) ((x.take i).reverse ++ xk)
        0 0 0 0 0 0 0 0 0 0 ((f x[i]).reverse ++ (((x.take i).map f).flatten.reverse ++ sk)))
        .xkeep ([x[i]] ++ (emitStacks (x.drop (i + 1)) ((x.take i).reverse ++ xk)
          0 0 0 0 0 0 0 0 0 0 ((f x[i]).reverse ++ (((x.take i).map f).flatten.reverse ++ sk)))
          .xkeep) =
        emitStacks (x.drop (i + 1)) ((x.take (i + 1)).reverse ++ xk) 0 0 0 0 0 0 0 0 0 0
          (((x.take (i + 1)).map f).flatten.reverse ++ sk) := by
      have ht : x.take (i + 1) = x.take i ++ [x[i]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some]
      have h1 : (x.take (i + 1)).reverse ++ xk = [x[i]] ++ ((x.take i).reverse ++ xk) := by
        rw [ht, List.reverse_append]
        rfl
      have h2 : ((x.take (i + 1)).map f).flatten.reverse ++ sk =
          (f x[i]).reverse ++ (((x.take i).map f).flatten.reverse ++ sk) := by
        rw [ht, List.map_append, List.flatten_append, List.reverse_append]
        simp
      rw [h1, h2]
      estacks_ext
    rw [hpu] at pu
    have hupd : Function.update (emitStacks (x.drop i) ((x.take i).reverse ++ xk)
        0 0 0 0 0 0 0 0 0 0 (((x.take i).map f).flatten.reverse ++ sk)) .input (x.drop (i + 1)) =
        emitStacks (x.drop (i + 1)) ((x.take i).reverse ++ xk) 0 0 0 0 0 0 0 0 0 0
          (((x.take i).map f).flatten.reverse ++ sk) := by estacks_ext
    rw [← hupd] at em
    exact dispatch_exits (Γ := GAlphabet Sym) .input
      (fun s => seq (emit (f s)) (pushList .xkeep [s])) _ x[i] (x.drop (i + 1))
      (by rw [← hsplit]; rfl) (seq_exits _ _ em pu)
  · intro i hi
    simp [emitStacks, List.drop_eq_nil_iff]; omega
  · simp [emitStacks]

theorem loopKeep_exits (f : Sym → List Instr) (y : List Sym) (sk : List Instr) :
    (loopKeep f).Exits (emitStacks [] y 0 0 0 0 0 0 0 0 0 0 sk) (3 * y.length + 1)
      (emitStacks [] [] 0 0 0 0 0 0 0 0 0 0 ((y.map f).flatten.reverse ++ sk)) := by
  have key := loop_exits (Γ := GAlphabet Sym) .xkeep (dispatch .xkeep fun s => emit (f s))
    y.length (fun i => emitStacks [] (y.drop i) 0 0 0 0 0 0 0 0 0 0
      (((y.take i).map f).flatten.reverse ++ sk)) (fun _ => 2) ?_ ?_ ?_
  · have hsteps : loopSteps (fun _ => 2) y.length = 3 * y.length + 1 := by
      rw [loopSteps_eq_sum]; simp; omega
    rw [hsteps] at key
    simpa using! key
  · intro i hi
    have hsplit : (y.drop i) = y[i] :: y.drop (i + 1) := List.drop_eq_getElem_cons hi
    have em := emit_exits (Γx := Sym) (f y[i]) [] (y.drop (i + 1)) 0 0 0 0 0 0 0 0 0 0
      (((y.take i).map f).flatten.reverse ++ sk)
    have hupd : Function.update (emitStacks [] (y.drop i) 0 0 0 0 0 0 0 0 0 0
        (((y.take i).map f).flatten.reverse ++ sk)) .xkeep (y.drop (i + 1)) =
        emitStacks [] (y.drop (i + 1)) 0 0 0 0 0 0 0 0 0 0
          (((y.take i).map f).flatten.reverse ++ sk) := by estacks_ext
    rw [← hupd] at em
    have body := dispatch_exits (Γ := GAlphabet Sym) .xkeep (fun s => emit (f s)) _ y[i]
      (y.drop (i + 1)) (by rw [← hsplit]; rfl) em
    have ht : y.take (i + 1) = y.take i ++ [y[i]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some]
    convert body using 2
    rw [ht, List.map_append, List.flatten_append, List.reverse_append]
    simp
  · intro i hi
    simp [emitStacks, List.drop_eq_nil_iff]; omega
  · simp [emitStacks]

/-! ### The machine -/

/-- The two-pass routine. -/
def R (pre : List Instr) (ch1 : Sym → List Instr) (sep : List Instr)
    (ch2 : Sym → List Instr) : GRoutine Sym :=
  seq (emit pre) <| seq (loopKeepInput ch1) <| seq (emit sep) <|
  seq (loopKeep ch2) <| seq (emit suffix) <| seq (moveAll .skel .job id .mark) <|
  seq (pushList (.work (.reg .win)) [.mark]) <| seq (pushList (.work (.reg .w)) [.mark]) <|
  seq interpret <| seq (drainAll regStacks) (moveAll (.work .buf) (.work .output) id .mark)

/-- The registers after interpretation. -/
def finalRegs (pre : List Instr) (ch1 : Sym → List Instr) (sep : List Instr)
    (ch2 : Sym → List Instr) (x : List Sym) : Regs :=
  (render (regs 0 1 0) (job pre ch1 sep ch2 x)).2

/-- Exact steps of the two-pass routine. -/
def cost (pre : List Instr) (ch1 : Sym → List Instr) (sep : List Instr)
    (ch2 : Sym → List Instr) (x out : List Sym) : ℕ :=
  1 + ((4 * x.length + 1) + (1 + ((3 * x.length + 1) + (1 +
    ((2 * (job pre ch1 sep ch2 x).length + 1) + (1 + (1 +
      (interpSteps (regs 0 1 0) (job pre ch1 sep ch2 x) +
      (((2 * finalRegs pre ch1 sep ch2 x .base + 1) + ((2 * finalRegs pre ch1 sep ch2 x .win + 1) +
        ((2 * finalRegs pre ch1 sep ch2 x .w + 1) +
          ((2 * finalRegs pre ch1 sep ch2 x .pw + 1) + 1)))) +
        (2 * out.length + 1))))))))))

theorem R_exits (pre : List Instr) (ch1 : Sym → List Instr) (sep : List Instr)
    (ch2 : Sym → List Instr) (x out : List Sym)
    (hok : ∀ i ∈ job pre ch1 sep ch2 x, i.ok)
    (hr : (render (regs 0 1 0) (job pre ch1 sep ch2 x)).1 = out) :
    (R pre ch1 sep ch2).Exits (paramStacks x [] 0 0 0 0 0 0 0 0) (cost pre ch1 sep ch2 x out)
      (outputStacks out) := by
  rw [paramStacks_eq_emitStacks]
  have s1 := emit_exits (Γx := Sym) pre x [] 0 0 0 0 0 0 0 0 0 0 []
  have s2 := loopKeepInput_exits ch1 x [] (pre.reverse ++ [])
  have s3 := emit_exits (Γx := Sym) sep [] (x.reverse ++ []) 0 0 0 0 0 0 0 0 0 0
    ((x.map ch1).flatten.reverse ++ (pre.reverse ++ []))
  have s4 := loopKeep_exits ch2 (x.reverse ++ [])
    (sep.reverse ++ ((x.map ch1).flatten.reverse ++ (pre.reverse ++ [])))
  have s5 := emit_exits (Γx := Sym) suffix [] [] 0 0 0 0 0 0 0 0 0 0
    (((x.reverse ++ []).map ch2).flatten.reverse ++ (sep.reverse ++
      ((x.map ch1).flatten.reverse ++ (pre.reverse ++ []))))
  have hsk : suffix.reverse ++ (((x.reverse ++ []).map ch2).flatten.reverse ++
      (sep.reverse ++ ((x.map ch1).flatten.reverse ++ (pre.reverse ++ [])))) =
      (job pre ch1 sep ch2 x).reverse := by
    simp [job, jobOf, List.reverse_append, List.append_assoc]
  rw [hsk] at s5
  set J := job pre ch1 sep ch2 x with hJ
  set S₅ : Stacks (GAlphabet Sym) := emitStacks [] [] 0 0 0 0 0 0 0 0 0 0 J.reverse with hS₅
  have s6 := moveAll_exits (Γ := GAlphabet Sym) .skel .job (by decide) id .mark S₅
  have hlen6 : (S₅ .skel).length = J.length := by simp [hS₅, emitStacks]
  have h6 : Function.update (Function.update S₅ .skel []) .job
      (((S₅ .skel).map id).reverse ++ S₅ .job) = interpStacks E J [] (fun _ => 0) := by
    rw [hS₅]
    gext
  rw [hlen6, h6] at s6
  have s7 := pushList_exits (Γ := GAlphabet Sym) (.work (.reg .win)) [.mark]
    (interpStacks E J [] (fun _ => 0))
  rw [push_reg, show Function.update (fun _ => 0 : Regs) .win (0 + 1) =
    Function.update (fun _ => 0) .win 1 from rfl] at s7
  have s8 := pushList_exits (Γ := GAlphabet Sym) (.work (.reg .w)) [.mark]
    (interpStacks E J [] (Function.update (fun _ => 0) .win 1))
  rw [push_reg] at s8
  have h8 : Function.update (Function.update (fun _ => 0 : Regs) .win 1) .w
      (Function.update (fun _ => 0 : Regs) .win 1 .w + 1) = regs 0 1 0 := by
    funext r; cases r <;> simp [regs]
  rw [h8] at s8
  have s9 := interpret_exits E rfl J hok [] (regs 0 1 0)
  rw [hJ, hr, List.append_nil] at s9
  set S₉ := interpStacks E [] out.reverse (finalRegs pre ch1 sep ch2 x) with hS₉
  have s10 := drainAll_exits regStacks S₉
  have hcost10 : drainAllCost regStacks S₉ =
      (2 * finalRegs pre ch1 sep ch2 x .base + 1) + ((2 * finalRegs pre ch1 sep ch2 x .win + 1) +
        ((2 * finalRegs pre ch1 sep ch2 x .w + 1) +
          ((2 * finalRegs pre ch1 sep ch2 x .pw + 1) + 1))) := by
    simp [drainAllCost, regStacks, hS₉, interpStacks, marks]
  rw [hcost10] at s10
  set S₁₀ : Stacks (GAlphabet Sym) := fun k => if k ∈ regStacks then [] else S₉ k with hS₁₀
  have s11 := moveAll_exits (Γ := GAlphabet Sym) (.work .buf) (.work .output) (by decide) id
    .mark S₁₀
  have h11 : Function.update (Function.update S₁₀ (.work .buf) []) (.work .output)
      (((S₁₀ (.work .buf)).map id).reverse ++ S₁₀ (.work .output)) = outputStacks out := by
    rw [hS₁₀, hS₉]
    gext
  have hlen11 : (S₁₀ (.work .buf)).length = out.length := by
    simp [hS₁₀, hS₉, regStacks, interpStacks]
  rw [h11, hlen11] at s11
  have := seq_exits _ _ s1 (seq_exits _ _ s2 (seq_exits _ _ s3 (seq_exits _ _ s4
    (seq_exits _ _ s5 (seq_exits _ _ s6 (seq_exits _ _ s7 (seq_exits _ _ s8
      (seq_exits _ _ s9 (seq_exits _ _ s10 s11)))))))))
  simpa [cost, finalRegs, hJ] using! this

/-! ### The time bound -/

theorem cost_le (pre : List Instr) (ch1 : Sym → List Instr) (sep : List Instr)
    (ch2 : Sym → List Instr) (x out : List Sym)
    (hpre : PrefixLE (20 * x.length + 40) (regs 0 1 0) (job pre ch1 sep ch2 x))
    (hlen : (job pre ch1 sep ch2 x).length ≤ 60 * x.length + 15)
    (hr : (render (regs 0 1 0) (job pre ch1 sep ch2 x)).1 = out) :
    cost pre ch1 sep ch2 x out ≤ 1000000 * (x.length + 1) ^ 2 := by
  set n := x.length with hn
  set L := (job pre ch1 sep ch2 x).length with hL
  have hint := interpSteps_le _ _ hpre
  have hout := render_fst_length_le _ _ hpre
  rw [hr] at hout
  have hR := hpre.finish
  have hb := hR .base
  have hwin := hR .win
  have hw := hR .w
  have hpw := hR .pw
  rw [← hL] at hint hout
  simp only [cost, finalRegs]
  rw [← hL]
  have hA : (4 * (20 * n + 40) + 4) * L ≤ (80 * n + 164) * (60 * n + 15) :=
    Nat.mul_le_mul (by omega) hlen
  have hB : (20 * n + 40 + 1) * L ≤ (20 * n + 41) * (60 * n + 15) :=
    Nat.mul_le_mul (by omega) hlen
  nlinarith

/-- The time polynomial of the two-pass machine. -/
noncomputable def timePoly : Polynomial ℕ := C 1000000 * (X + 1) ^ 2

/-- A bounded run of the two-pass machine, for `TM2ComputableInPolyTime`. -/
noncomputable def outputsInTime (pre : List Instr) (ch1 : Sym → List Instr)
    (sep : List Instr) (ch2 : Sym → List Instr) (x out : List Sym)
    (hok : ∀ i ∈ job pre ch1 sep ch2 x, i.ok)
    (hpre : PrefixLE (20 * x.length + 40) (regs 0 1 0) (job pre ch1 sep ch2 x))
    (hlen : (job pre ch1 sep ch2 x).length ≤ 60 * x.length + 15)
    (hr : (render (regs 0 1 0) (job pre ch1 sep ch2 x)).1 = out) :
    TM2OutputsInTime (toGenMachine (R pre ch1 sep ch2)) x (some out) (timePoly.eval x.length) :=
  evalsToInTimeMono (toGenMachine_outputsInTime _ _ _ _ (R_exits pre ch1 sep ch2 x out hok hr))
    (by
      simp only [timePoly, eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one]
      exact cost_le pre ch1 sep ch2 x out hpre hlen hr)

end PhdThesisLean.TwoPassMachine
