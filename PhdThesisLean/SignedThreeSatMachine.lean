import PhdThesisLean.TwoPassMachine

/-!
# Signed `p`-adic residual objectives are NP-hard at `p = 5`

This module completes the complexity transfer for thesis Corollary `cor:signed-nphard`
(`sudoku-via-padic-regression/body.tex`).

The instance `SignedThreeSatReduction.signedReduce F` is computed by the two-pass
machine of `TwoPassMachine.lean` with the first-pass chunks `chunk1`, which stream each
clause row directly: a sign symbol starts the literal's terms, the marks of the literal
extend its index, and a clause end closes the row, opens the next negative row, and adds
`2` to the bound register `pw`. The prefix `[.lit false]` opens the first row, and the
row left open at the end becomes the harmless negative zero row of
`SignedThreeSatReduction.clauseRows`. The second pass emits the forcing pair of every
literal occurrence. `render_job` shows that the job renders to the unary encoding of
`signedReduce F`, and `computableInPolyTime` packages the run within `10⁶ (n + 1)²`
steps.

Composed with the library's chain reduction (whose output has exact width three) this is
a checked polynomial-time reduction from unary CNF-SAT (`satReduction`), so the signed
threshold problem is NP-hard for every prime `p > 3` (`encodedUnarySignedRegression_NPHard`,
`encodedSignedRegression_NPHard`), in particular at `p = 5` (`signed_nphard_five`).
-/

namespace PhdThesisLean.SignedThreeSatMachine

open Turing Computability Polynomial
open LeanNPHardness LeanNPHardness.CNF LeanNPHardness.CNF.Unary LeanNPHardness.TableauJobs
open LeanNPHardness.TableauStacks LeanNPHardness.Routines LeanNPHardness.MachinePrimitives
open PhdThesisLean.PadicRegressionLanguage PhdThesisLean.SignedThreeSatReduction
open PhdThesisLean.FixedPrimeMaxCutJob (regs regs_base regs_win regs_w regs_pw update_base
  update_win update_pw regsLE_regs Bounded)
open PhdThesisLean.TwoPassMachine (jobOf jobOf_append render_pass2 jobOf_bounds
  prefixLE_pure_bounded suffix)

private alias pcons := FixedPrimeMaxCutJob.prefixLE_cons
private alias pnil := FixedPrimeMaxCutJob.prefixLE_nil

/-! ### The job -/

/-- First-pass chunks: stream the clause rows. -/
def chunk1 : Sym → List Instr
  | .mark => [.mark]
  | .pos => [.lit true, .lit true, .mark]
  | .neg => [.lit false, .mark]
  | .endClause => [.endClause, .lit false] ++ MaxCutJob.incr .pw 2

/-- The whole job of an input. -/
def job (x : List Sym) : List Instr := TwoPassMachine.job [.lit false] chunk1 x

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

/-- The whole job renders to the unary encoding of the signed instance. -/
theorem render_job (F : Formula ℕ) :
    (render (regs 0 1 0) (job (encode F))).1 =
      signedUnaryEncoding.encode (signedReduce F) := by
  rw [job, TwoPassMachine.job, render_append, render_append, render_append, render_append]
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

theorem chunk1_bounded : TwoPassMachine.ChunkBounded chunk1 :=
  fun s => chunk1_bounds s

theorem chunk1_ok (s : Sym) : ∀ i ∈ chunk1 s, i.ok := by
  cases s <;> simp [chunk1, MaxCutJob.incr, Instr.ok, List.replicate]

theorem chunk1_length_le (s : Sym) : (chunk1 s).length ≤ 8 := by
  cases s <;> simp [chunk1, MaxCutJob.incr]

/-- The signed clause-reward reduction is computed in polynomial time by the two-pass
machine. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime CNF.Unary.finEncoding signedUnaryEncoding signedReduce where
  tm := toGenMachine (TwoPassMachine.R [.lit false] chunk1)
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := TwoPassMachine.timePoly
  outputsFun F := by
    have run := TwoPassMachine.outputsInTime [.lit false] chunk1 (encode F)
      (signedUnaryEncoding.encode (signedReduce F))
      (TwoPassMachine.job_ok _ _ (by simp [Instr.ok]) chunk1_ok _)
      (TwoPassMachine.prefixLE_job _ _ (by simp [Instr.pure]) chunk1_bounded _)
      (TwoPassMachine.job_length_le _ _ (by simp) chunk1_length_le _) (render_job F)
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
