import PhdThesisLean.SignedThreeSatReduction
import PhdThesisLean.FixedPrimeMaxCutMachine

/-!
# Signed `p`-adic residual objectives are NP-hard at `p = 5`

This module completes the complexity transfer for thesis Corollary `cor:signed-nphard`
(`sudoku-via-padic-regression/body.tex`).

The machine `sgR` makes two passes over the unary encoding of a formula while building
one interpreter job.

* The first pass reads the input and keeps a reversed copy on the `xkeep` stack. Its
  chunks stream each clause row directly: a sign symbol starts the literal's terms, the
  marks of the literal extend its index, and a clause end closes the row, opens the next
  negative row, and adds `2` to the bound register `pw`. The final open row becomes the
  harmless negative zero row of `SignedThreeSatReduction.clauseRows`.
* The second pass reads the reversed copy, so the marks of each literal arrive before
  its sign symbol: marks count the literal index in `win`, and the sign symbol emits the
  forcing pair on `win` and resets it.

A fixed suffix emits the bound clause from `pw`. `sgR_exits` is the exact run from the
input alone to the unary encoding of `SignedThreeSatReduction.signedReduce F` alone,
within `10⁶ (n + 1)²` steps (`cost_le`).

Composed with the library's chain reduction (whose output has exact width three) this is
a checked polynomial-time reduction from unary CNF-SAT (`satReduction`), so the signed
threshold problem is NP-hard for every prime `p > 3` (`encodedUnarySignedRegression_NPHard`,
`encodedSignedRegression_NPHard`), in particular at `p = 5`
(`signed_nphard_five`).
-/

namespace PhdThesisLean.SignedThreeSatMachine

open Turing Computability Polynomial
open LeanNPHardness LeanNPHardness.CNF LeanNPHardness.CNF.Unary LeanNPHardness.TableauJobs
open LeanNPHardness.TableauStacks LeanNPHardness.Routines LeanNPHardness.MachinePrimitives
open PhdThesisLean.PadicRegressionLanguage PhdThesisLean.SignedThreeSatReduction
open PhdThesisLean.FixedPrimeMaxCutJob (regs regs_base regs_win regs_w regs_pw update_base
  update_win update_pw regsLE_regs Bounded)
open PhdThesisLean.FixedPrimeMaxCutMachine (E push_reg regStacks)

private alias pcons := FixedPrimeMaxCutJob.prefixLE_cons
private alias pnil := FixedPrimeMaxCutJob.prefixLE_nil

/-! ### The job -/

/-- First-pass chunks: stream the clause rows. -/
def chunk1 : Sym → List Instr
  | .mark => [.mark]
  | .pos => [.lit true, .lit true, .mark]
  | .neg => [.lit false, .mark]
  | .endClause => [.endClause, .lit false] ++ MaxCutJob.incr .pw 2

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

/-- The whole job of an input. -/
def job (x : List Sym) : List Instr :=
  [.lit false] ++ jobOf chunk1 x ++ [.endClause] ++ jobOf chunk2 x.reverse ++ suffix

/-! ### Rendering the first pass -/

theorem render_marks1 (k v : ℕ) :
    render (regs 0 1 k) (jobOf chunk1 (List.replicate v .mark)) =
      (List.replicate v .mark, regs 0 1 k) := by
  induction v with
  | zero => simp [jobOf, render]
  | succ v ih =>
      rw [List.replicate_succ, show Sym.mark :: List.replicate v Sym.mark =
        [Sym.mark] ++ List.replicate v Sym.mark from rfl, jobOf_append, render_append]
      have h1 : render (regs 0 1 k) (jobOf chunk1 [.mark]) = ([.mark], regs 0 1 k) := by
        simp [jobOf, chunk1, render, renderInstr]
      rw [h1]
      simp only
      rw [ih]

theorem render_lit1 (k : ℕ) (l : Literal ℕ) :
    render (regs 0 1 k) (jobOf chunk1 (encodeLiteral l)) =
      ((litTerms l).flatMap encodeLiteral, regs 0 1 k) := by
  cases l with
  | positive v =>
      rw [encodeLiteral, show Sym.pos :: List.replicate v Sym.mark =
        [Sym.pos] ++ List.replicate v Sym.mark from rfl, jobOf_append, render_append]
      have h1 : render (regs 0 1 k) (jobOf chunk1 [.pos]) =
          ([.pos, .pos, .mark], regs 0 1 k) := by
        simp [jobOf, chunk1, render, renderInstr]
      rw [h1]
      simp only
      rw [render_marks1]
      simp [litTerms, encodeLiteral, List.replicate_succ]
  | negative v =>
      rw [encodeLiteral, show Sym.neg :: List.replicate v Sym.mark =
        [Sym.neg] ++ List.replicate v Sym.mark from rfl, jobOf_append, render_append]
      have h1 : render (regs 0 1 k) (jobOf chunk1 [.neg]) = ([.neg, .mark], regs 0 1 k) := by
        simp [jobOf, chunk1, render, renderInstr]
      rw [h1]
      simp only
      rw [render_marks1]
      simp [litTerms, encodeLiteral, List.replicate_succ]

theorem render_clause1 (k : ℕ) (c : Clause ℕ) :
    render (regs 0 1 k) (jobOf chunk1 (encodeClause c)) =
      ((clauseRow c).flatMap encodeLiteral ++ [.endClause, .neg], regs 0 1 (k + 2)) := by
  have hl : ∀ c : Clause ℕ, render (regs 0 1 k) (jobOf chunk1 (c.flatMap encodeLiteral)) =
      ((clauseRow c).flatMap encodeLiteral, regs 0 1 k) := by
    intro c
    induction c with
    | nil => simp [jobOf, render, clauseRow]
    | cons l c ih =>
        rw [List.flatMap_cons, jobOf_append, render_append, render_lit1]
        simp only
        rw [ih]
        simp [clauseRow, List.flatMap_cons]
  rw [encodeClause, jobOf_append, render_append, hl]
  simp only
  have he : render (regs 0 1 k) (jobOf chunk1 [.endClause]) =
      ([.endClause, .neg], regs 0 1 (k + 2)) := by
    simp only [jobOf, chunk1, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, MaxCutJob.incr, List.cons_append, List.nil_append]
    simp [List.replicate, render, renderInstr]
  rw [he]

theorem render_pass1 (F : Formula ℕ) : ∀ k,
    render (regs 0 1 k) (jobOf chunk1 (encode F)) =
      ((F.flatMap fun c => (clauseRow c).flatMap encodeLiteral ++ [.endClause, .neg]),
        regs 0 1 (k + 2 * F.length)) := by
  induction F with
  | nil => intro k; simp [jobOf, render, encode]
  | cons c F ih =>
      intro k
      rw [encode_cons, jobOf_append, render_append, render_clause1]
      simp only
      rw [ih]
      simp only [List.flatMap_cons, List.length_cons]
      refine Prod.ext rfl ?_
      congr 1
      ring

theorem telescope (F : Formula ℕ) (L : Clause ℕ → List Sym) :
    [Sym.neg] ++ (F.flatMap fun c => L c ++ [Sym.endClause, Sym.neg]) =
      (F.flatMap fun c => [Sym.neg] ++ L c ++ [Sym.endClause]) ++ [Sym.neg] := by
  induction F with
  | nil => rfl
  | cons c F ih =>
      simp only [List.flatMap_cons, List.append_assoc] at ih ⊢
      rw [← ih]
      simp

theorem pass1_telescope (F : Formula ℕ) :
    [Sym.neg] ++ (F.flatMap fun c => (clauseRow c).flatMap encodeLiteral ++
      [Sym.endClause, Sym.neg]) ++ [Sym.endClause] =
      encode ((clauseRows F).map signedClause) := by
  rw [telescope]
  simp [clauseRows, encode, encodeClause, signedClause, marker, encodeLiteral, List.flatMap_map,
    List.append_assoc, Function.comp_def]

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

/-- The whole job renders to the unary encoding of the signed instance. -/
theorem render_job (F : Formula ℕ) :
    (render (regs 0 1 0) (job (encode F))).1 =
      signedUnaryEncoding.encode (signedReduce F) := by
  rw [job, render_append, render_append, render_append, render_append]
  have h0 : render (regs 0 1 0) [.lit false] = ([Sym.neg], regs 0 1 0) := by
    simp [render, renderInstr]
  rw [h0]
  simp only
  rw [render_pass1]
  simp only
  have h1 : render (regs 0 1 (0 + 2 * F.length)) [.endClause] =
      ([Sym.endClause], regs 0 1 (0 + 2 * F.length)) := by simp [render, renderInstr]
  rw [h1]
  simp only
  rw [render_pass2]
  simp only
  have h2 : render (regs 0 1 (0 + 2 * F.length)) suffix =
      (encodeClause [.positive (2 * F.length)], regs 0 1 (0 + 2 * F.length)) := by
    simp [suffix, render, renderInstr, encodeClause, encodeLiteral]
  rw [h2]
  simp only [signedUnaryEncoding, signedReduce, signedFormula, List.map_append, encode_append]
  rw [← pass1_telescope]
  simp [encode, List.append_assoc]

/-! ### Register bounds -/

theorem chunk1_bounds (s : Sym) {M c d : ℕ} {R : Regs} (h : Bounded c d R) (_hc : 2 ≤ c)
    (hcM : c + 1 ≤ M) (hdM : d + 3 ≤ M) :
    PrefixLE M R (chunk1 s) ∧ Bounded (c + 1) (d + 3) (render R (chunk1 s)).2 := by
  obtain ⟨b, i, k, rfl, hb, hi, hk⟩ := h
  cases s with
  | mark =>
      refine ⟨pcons ?_ (pnil ?_),
        ⟨b, i, k, by simp [chunk1, render, renderInstr], by omega, by omega, by omega⟩⟩ <;>
        simp [renderInstr, regsLE_regs] <;> omega
  | pos =>
      refine ⟨?_, ⟨b, i, k, by simp [chunk1, render, renderInstr], by omega, by omega,
        by omega⟩⟩
      simp only [chunk1]
      repeat' refine pcons ?_ ?_
      all_goals first
        | (refine pnil ?_; simp [renderInstr, regsLE_regs]; omega)
        | (simp [renderInstr, regsLE_regs]; omega)
  | neg =>
      refine ⟨?_, ⟨b, i, k, by simp [chunk1, render, renderInstr], by omega, by omega,
        by omega⟩⟩
      simp only [chunk1]
      repeat' refine pcons ?_ ?_
      all_goals first
        | (refine pnil ?_; simp [renderInstr, regsLE_regs]; omega)
        | (simp [renderInstr, regsLE_regs]; omega)
  | endClause =>
      refine ⟨?_, ⟨b, i, k + 2, ?_, by omega, by omega, by omega⟩⟩
      · simp only [chunk1, MaxCutJob.incr, List.replicate, List.cons_append, List.nil_append]
        repeat' refine pcons ?_ ?_
        all_goals first
          | (refine pnil ?_; simp [renderInstr, regsLE_regs]; omega)
          | (simp [renderInstr, regsLE_regs]; omega)
      · simp [chunk1, MaxCutJob.incr, render, renderInstr]

theorem chunk2_bounds (s : Sym) {M c d : ℕ} {R : Regs} (h : Bounded c d R) (_hc : 2 ≤ c)
    (hcM : c + 1 ≤ M) (hdM : d + 3 ≤ M) :
    PrefixLE M R (chunk2 s) ∧ Bounded (c + 1) (d + 3) (render R (chunk2 s)).2 := by
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

theorem jobOf_bounds (ch : Sym → List Instr)
    (hch : ∀ s {M c d : ℕ} {R : Regs}, Bounded c d R → 2 ≤ c → c + 1 ≤ M → d + 3 ≤ M →
      PrefixLE M R (ch s) ∧ Bounded (c + 1) (d + 3) (render R (ch s)).2)
    (L : List Sym) : ∀ {M c d : ℕ} {R : Regs}, Bounded c d R → 2 ≤ c →
    c + L.length ≤ M → d + 3 * L.length ≤ M →
    PrefixLE M R (jobOf ch L) ∧
      Bounded (c + L.length) (d + 3 * L.length) (render R (jobOf ch L)).2 := by
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
        show c + (L.length + 1) = c + 1 + L.length by ring,
        show d + 3 * (L.length + 1) = d + 3 + 3 * L.length by ring]
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

/-- Every register stays at most `8n + 20` while the job of an input of length `n`
runs. -/
theorem prefixLE_job (x : List Sym) : PrefixLE (8 * x.length + 20) (regs 0 1 0) (job x) := by
  set n := x.length
  have h0 : Bounded 2 0 (regs 0 1 0) := ⟨0, 1, 0, rfl, by omega, by omega, le_rfl⟩
  obtain ⟨p0, b0⟩ := prefixLE_pure_bounded (M := 8 * n + 20) (J := [.lit false])
    (by simp [Instr.pure]) h0 (by omega) (by omega) (by omega)
  obtain ⟨p1, b1⟩ := jobOf_bounds chunk1 (fun s => chunk1_bounds s) x (M := 8 * n + 20) b0
    le_rfl (by omega) (by omega)
  obtain ⟨p2, b2⟩ := prefixLE_pure_bounded (M := 8 * n + 20) (J := [.endClause])
    (by simp [Instr.pure]) b1 (by omega) (by omega) (by omega)
  obtain ⟨p3, b3⟩ := jobOf_bounds chunk2 (fun s => chunk2_bounds s) x.reverse
    (M := 8 * n + 20) b2 (by omega) (by simp; omega) (by simp; omega)
  obtain ⟨p4, _⟩ := prefixLE_pure_bounded (M := 8 * n + 20) (J := suffix)
    (by simp [suffix, Instr.pure]) b3 (by simp; omega) (by simp; omega) (by omega)
  have q1 := prefixLE_append p0 p1
  have q2 := prefixLE_append q1 (by rw [MachineTableau.render_append_snd]; exact p2)
  have q3 := prefixLE_append q2
    (by rw [MachineTableau.render_append_snd, MachineTableau.render_append_snd]; exact p3)
  have q4 := prefixLE_append q3
    (by rw [MachineTableau.render_append_snd, MachineTableau.render_append_snd,
      MachineTableau.render_append_snd]; exact p4)
  simpa [job, List.append_assoc] using q4

theorem job_length_le (x : List Sym) : (job x).length ≤ 30 * x.length + 5 := by
  have h1 : ∀ L : List Sym, (jobOf chunk1 L).length ≤ 5 * L.length := by
    intro L
    induction L with
    | nil => simp [jobOf]
    | cons s L ih =>
        have : (chunk1 s).length ≤ 5 := by cases s <;> simp [chunk1, MaxCutJob.incr]
        simp only [jobOf, List.map_cons, List.flatten_cons, List.length_append,
          List.length_cons] at ih ⊢
        omega
  have h2 : ∀ L : List Sym, (jobOf chunk2 L).length ≤ 15 * L.length := by
    intro L
    induction L with
    | nil => simp [jobOf]
    | cons s L ih =>
        have : (chunk2 s).length ≤ 15 := by cases s <;> simp [chunk2, forcingJob]
        simp only [jobOf, List.map_cons, List.flatten_cons, List.length_append,
          List.length_cons] at ih ⊢
        omega
  have := h1 x
  have := h2 x.reverse
  simp only [job, suffix, List.length_append, List.length_cons, List.length_nil,
    List.length_reverse] at this ⊢
  omega

theorem job_ok (x : List Sym) : ∀ i ∈ job x, i.ok := by
  have h1 : ∀ s, ∀ i ∈ chunk1 s, i.ok := by
    intro s; cases s <;> simp [chunk1, MaxCutJob.incr, Instr.ok, List.replicate]
  have h2 : ∀ s, ∀ i ∈ chunk2 s, i.ok := by
    intro s; cases s <;> simp [chunk2, forcingJob, Instr.ok]
  intro i hi
  simp only [job, suffix, List.mem_append] at hi
  rcases hi with (((h | h) | h) | h) | h
  · simp only [List.mem_singleton] at h; subst h; trivial
  · simp only [jobOf, List.mem_flatten, List.mem_map] at h
    obtain ⟨_, ⟨s, _, rfl⟩, h⟩ := h
    exact h1 s i h
  · simp only [List.mem_singleton] at h; subst h; trivial
  · simp only [jobOf, List.mem_flatten, List.mem_map] at h
    obtain ⟨_, ⟨s, _, rfl⟩, h⟩ := h
    exact h2 s i h
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with rfl | rfl | rfl <;> trivial

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
    simpa using key
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
    simpa using key
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

/-- The reduction routine. -/
def sgR : GRoutine Sym :=
  seq (emit [.lit false]) <| seq (loopKeepInput chunk1) <| seq (emit [.endClause]) <|
  seq (loopKeep chunk2) <| seq (emit suffix) <| seq (moveAll .skel .job id .mark) <|
  seq (pushList (.work (.reg .win)) [.mark]) <| seq (pushList (.work (.reg .w)) [.mark]) <|
  seq interpret <| seq (drainAll regStacks) (moveAll (.work .buf) (.work .output) id .mark)

/-- The registers after interpretation. -/
def finalRegs (F : Formula ℕ) : Regs := (render (regs 0 1 0) (job (encode F))).2

/-- Exact steps of the reduction routine. -/
def cost (F : Formula ℕ) : ℕ :=
  1 + ((4 * (encode F).length + 1) + (1 + ((3 * (encode F).length + 1) + (1 +
    ((2 * (job (encode F)).length + 1) + (1 + (1 + (interpSteps (regs 0 1 0) (job (encode F)) +
      (((2 * finalRegs F .base + 1) + ((2 * finalRegs F .win + 1) + ((2 * finalRegs F .w + 1) +
        ((2 * finalRegs F .pw + 1) + 1)))) +
        (2 * (signedUnaryEncoding.encode (signedReduce F)).length + 1))))))))))

theorem sgR_exits (F : Formula ℕ) :
    sgR.Exits (paramStacks (encode F) [] 0 0 0 0 0 0 0 0) (cost F)
      (outputStacks (signedUnaryEncoding.encode (signedReduce F))) := by
  set x := encode F with hx
  rw [paramStacks_eq_emitStacks]
  have s1 := emit_exits (Γx := Sym) [.lit false] x [] 0 0 0 0 0 0 0 0 0 0 []
  have s2 := loopKeepInput_exits chunk1 x [] ([Instr.lit false].reverse ++ [])
  have s3 := emit_exits (Γx := Sym) [.endClause] [] (x.reverse ++ []) 0 0 0 0 0 0 0 0 0 0
    ((x.map chunk1).flatten.reverse ++ ([Instr.lit false].reverse ++ []))
  have s4 := loopKeep_exits chunk2 (x.reverse ++ [])
    ([Instr.endClause].reverse ++ ((x.map chunk1).flatten.reverse ++
      ([Instr.lit false].reverse ++ [])))
  have s5 := emit_exits (Γx := Sym) suffix [] [] 0 0 0 0 0 0 0 0 0 0
    (((x.reverse ++ []).map chunk2).flatten.reverse ++ ([Instr.endClause].reverse ++
      ((x.map chunk1).flatten.reverse ++ ([Instr.lit false].reverse ++ []))))
  have hsk : suffix.reverse ++ (((x.reverse ++ []).map chunk2).flatten.reverse ++
      ([Instr.endClause].reverse ++ ((x.map chunk1).flatten.reverse ++
        ([Instr.lit false].reverse ++ [])))) = (job x).reverse := by
    simp [job, jobOf, List.reverse_append, List.append_assoc]
  rw [hsk] at s5
  set J := job x with hJ
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
  have s9 := interpret_exits E rfl J (job_ok x) [] (regs 0 1 0)
  rw [hJ, hx, render_job, List.append_nil] at s9
  set S₉ := interpStacks E [] (signedUnaryEncoding.encode (signedReduce F)).reverse
    (finalRegs F) with hS₉
  have s10 := drainAll_exits regStacks S₉
  have hcost10 : drainAllCost regStacks S₉ =
      (2 * finalRegs F .base + 1) + ((2 * finalRegs F .win + 1) + ((2 * finalRegs F .w + 1) +
        ((2 * finalRegs F .pw + 1) + 1))) := by
    simp [drainAllCost, regStacks, hS₉, interpStacks, marks]
  rw [hcost10] at s10
  set S₁₀ : Stacks (GAlphabet Sym) := fun k => if k ∈ regStacks then [] else S₉ k with hS₁₀
  have s11 := moveAll_exits (Γ := GAlphabet Sym) (.work .buf) (.work .output) (by decide) id
    .mark S₁₀
  have h11 : Function.update (Function.update S₁₀ (.work .buf) []) (.work .output)
      (((S₁₀ (.work .buf)).map id).reverse ++ S₁₀ (.work .output)) =
      outputStacks (signedUnaryEncoding.encode (signedReduce F)) := by
    rw [hS₁₀, hS₉]
    gext
  have hlen11 : (S₁₀ (.work .buf)).length =
      (signedUnaryEncoding.encode (signedReduce F)).length := by
    simp [hS₁₀, hS₉, regStacks, interpStacks]
  rw [h11, hlen11] at s11
  have := seq_exits _ _ s1 (seq_exits _ _ s2 (seq_exits _ _ s3 (seq_exits _ _ s4
    (seq_exits _ _ s5 (seq_exits _ _ s6 (seq_exits _ _ s7 (seq_exits _ _ s8
      (seq_exits _ _ s9 (seq_exits _ _ s10 s11)))))))))
  simpa [cost, finalRegs, hJ, hx] using this

/-! ### The time bound -/

theorem cost_le (F : Formula ℕ) : cost F ≤ 1000000 * ((encode F).length + 1) ^ 2 := by
  set n := (encode F).length with hn
  set L := (job (encode F)).length with hL
  have hLn : L ≤ 30 * n + 5 := job_length_le _
  have hpre := prefixLE_job (encode F)
  have hint := interpSteps_le _ _ hpre
  have hout := render_fst_length_le _ _ hpre
  rw [render_job] at hout
  have hR := hpre.finish
  have hb := hR .base
  have hwin := hR .win
  have hw := hR .w
  have hpw := hR .pw
  rw [← hn, ← hL] at hint hout
  rw [← hn] at hb hwin hw hpw
  simp only [cost, finalRegs]
  rw [← hn, ← hL]
  have hA : (4 * (8 * n + 20) + 4) * L ≤ (32 * n + 84) * (30 * n + 5) :=
    Nat.mul_le_mul (by omega) hLn
  have hB : (8 * n + 20 + 1) * L ≤ (8 * n + 21) * (30 * n + 5) := Nat.mul_le_mul (by omega) hLn
  nlinarith

/-- The time polynomial of the reduction machine. -/
noncomputable def timePoly : Polynomial ℕ := C 1000000 * (X + 1) ^ 2

/-- The signed clause-reward reduction is computed in polynomial time. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime CNF.Unary.finEncoding signedUnaryEncoding signedReduce where
  tm := toGenMachine sgR
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePoly
  outputsFun F := by
    have run := evalsToInTimeMono (toGenMachine_outputsInTime _ _ _ _ (sgR_exits F))
      (show cost F ≤ timePoly.eval (encode F).length by
        simp only [timePoly, eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one]
        exact cost_le F)
    simpa [Equiv.refl] using run

/-! ### Hardness -/

/-- The checked polynomial-time reduction from unary CNF-SAT to the signed threshold
problem: the library's chain reduction to exact width three, then `signedReduce`. -/
noncomputable def satReduction (p : ℕ) [Fact p.Prime] (hp3 : 3 < p) :
    CNF.Unary.encodedUnarySAT.PolytimeReducesTo (encodedUnarySignedRegression p) where
  map := signedReduce ∘ CNF.Chain.chainThree
  correct F := by
    show F.Satisfiable ↔ SignedRegressionLang p (signedReduce (CNF.Chain.chainThree F))
    rw [← CNF.Chain.satisfiable_chainThree]
    exact signed_iff hp3 _ (CNF.Chain.exactWidth_chainThree F)
  polytime := ⟨MachineComposition.compositionComputableInPolyTime CNF.Unary.finEncoding
    CNF.Unary.finEncoding signedUnaryEncoding CNF.Chain.chainThree signedReduce
    ChainMachine.computableInPolyTime computableInPolyTime⟩

/-- **Thesis `cor:signed-nphard`, unary encoding.** For every prime `p > 3`, the
threshold decision problem for signed affine `p`-adic residual objectives is NP-hard. -/
theorem encodedUnarySignedRegression_NPHard (p : ℕ) [Fact p.Prime] (hp3 : 3 < p) :
    (encodedUnarySignedRegression p).NPHard :=
  EncodedLanguage.NPHard.of_reduction (satReduction p hp3) CookLevin.encodedUnarySAT_NPHard

/-- Re-encoding signed instances in binary, in polynomial time. -/
noncomputable def binaryComputable :
    TM2ComputableInPolyTime signedUnaryEncoding signedBinaryEncoding id where
  tm := BinaryConvert.machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := BinaryConvert.timePoly
  outputsFun x := by
    have run := toMachine_outputsInTime_le BinaryConvert.conv .input .out
      (encode (signedFormula x.1 x.2)) (Formula.encode (signedFormula x.1 x.2)) _
      (by
        have h1 := BinaryConvert.initList_eq (encode (signedFormula x.1 x.2))
        have h2 := BinaryConvert.haltList_eq (Formula.encode (signedFormula x.1 x.2))
        simp only [BinaryConvert.machine] at h1 h2
        rw [h1, h2]
        exact BinaryConvert.conv_exits _)
    have run' := evalsToInTimeMono run
      (show BinaryConvert.convBound (encode (signedFormula x.1 x.2)).length ≤
          BinaryConvert.timePoly.eval (encode (signedFormula x.1 x.2)).length by
        simp only [BinaryConvert.timePoly, eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one]
        exact BinaryConvert.convBound_le _)
    simpa [Equiv.refl, signedUnaryEncoding, signedBinaryEncoding] using run'

/-- Unary signed instances reduce to binary ones by re-encoding. -/
noncomputable def binaryReduction (p : ℕ) :
    (encodedUnarySignedRegression p).PolytimeReducesTo (encodedSignedRegression p) where
  map := id
  correct _ := Iff.rfl
  polytime := ⟨binaryComputable⟩

/-- **Thesis `cor:signed-nphard`, binary encoding.** -/
theorem encodedSignedRegression_NPHard (p : ℕ) [Fact p.Prime] (hp3 : 3 < p) :
    (encodedSignedRegression p).NPHard :=
  EncodedLanguage.NPHard.of_reduction (binaryReduction p)
    (encodedUnarySignedRegression_NPHard p hp3)

/-- **Thesis `cor:signed-nphard`** at the thesis's prime `p = 5`, in both encodings. -/
theorem signed_nphard_five :
    (encodedUnarySignedRegression 5).NPHard ∧ (encodedSignedRegression 5).NPHard := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact ⟨encodedUnarySignedRegression_NPHard 5 (by norm_num),
    encodedSignedRegression_NPHard 5 (by norm_num)⟩

end PhdThesisLean.SignedThreeSatMachine

#print axioms PhdThesisLean.SignedThreeSatMachine.signed_nphard_five
