import PhdThesisLean.PolynomialResidualReduction
import PhdThesisLean.TwoPassMachine

/-!
# Multilinear positive polynomial-residual objectives over `ℤ_2` are NP-hard

This module completes the complexity transfer for thesis Corollary
`cor:sudoku-polynomial-dyadic-hardness` (`sudoku-via-padic-regression/body.tex`).

The instance `PolynomialResidualReduction.polyReduce F` is computed by the two-pass
machine of `TwoPassMachine.lean`.

* The prefix opens a zero residual and sets `base` to the first occurrence index.
* First-pass chunks (`chunk1`): at a sign symbol, close the open clause, emit the two
  forcing pairs on the occurrence coordinate held in `win`, open the linking residual
  of the occurrence (whose variable index is then streamed from the doubled marks), and
  advance `win` by `2`. At a clause end, close the open clause, emit the clause product
  on the occurrence coordinates `base, base + 2, base + 4`, open a zero residual, move
  `win` to `base`, and add `9` to the bound.
* The separator closes the last zero residual and resets `win` to `2`.
* Second-pass chunks (`chunk2x`): on the reversed input the doubled marks of each
  literal count its variable index `2v + 2` in `win`, and the sign symbol emits the
  forcing pair on it.

`render_job` shows that the job renders to the unary encoding of `polyReduce F`, and
`computableInPolyTime` packages the run within `10⁶ (n + 1)²` steps. Composed with the
library's chain reduction this gives `satReduction`, so the multilinear degree-three
problem is NP-hard for every prime (`encodedUnaryPolyML_NPHard`,
`encodedPolyML_NPHard`), in particular over `ℤ_2` (`dyadic_poly_nphard`).
-/

namespace PhdThesisLean.PolynomialResidualMachine

open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime
open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat
open Polynomial StateTransition
open LeanNPHardness (FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime)
open LeanNPHardness LeanNPHardness.CNF LeanNPHardness.CNF.Unary LeanNPHardness.TableauJobs
open LeanNPHardness.TableauStacks LeanNPHardness.Routines LeanNPHardness.MachinePrimitives
open PhdThesisLean.PadicRegressionLanguage PhdThesisLean.PolynomialResidualLanguage
open PhdThesisLean.PolynomialResidualReduction
open PhdThesisLean.SignedThreeSatReduction (litVar)
open PhdThesisLean.FixedPrimeMaxCutJob (regs regs_base regs_win regs_w regs_pw update_base
  update_win update_pw regsLE_regs Bounded)
open PhdThesisLean.TwoPassMachine (jobOf jobOf_append forcingJob suffix BlockBounded
  ChunkBounded)

private alias pcons := FixedPrimeMaxCutJob.prefixLE_cons
private alias pnil := FixedPrimeMaxCutJob.prefixLE_nil

/-! ### The job -/

/-- Open the linking residual of a positive literal occurrence. -/
def openPos : List Instr := [.lit true, .lit true, .reg .win, .lit false, .mark, .mark]

/-- Open the linking residual of a negative literal occurrence. -/
def openNeg : List Instr := [.lit true, .lit true, .reg .win, .lit true, .lit true, .mark, .mark]

/-- The clause product on the occurrence coordinates `base`, `base + 2`, `base + 4`. -/
def prodJob : List Instr :=
  [.lit true, .lit true, .reg .base, .endClause,
    .lit true, .mark, .lit true, .reg .base, .mark, .mark, .endClause,
    .lit true, .mark, .lit true, .reg .base, .mark, .mark, .mark, .mark, .endClause]

/-- First-pass chunks. -/
def chunk1 : Sym → List Instr
  | .mark => [.mark, .mark]
  | .pos => [.endClause] ++ forcingJob ++ forcingJob ++ openPos ++ MaxCutJob.incr .win 2
  | .neg => [.endClause] ++ forcingJob ++ forcingJob ++ openNeg ++ MaxCutJob.incr .win 2
  | .endClause => [.endClause] ++ prodJob ++ [.lit true, .clear .base, .addTo .base .win] ++
      MaxCutJob.incr .pw 9

/-- The prefix: open a zero residual and set `base` to the first occurrence index. -/
def pre : List Instr := [.lit true, .clear .base, .addTo .base .win]

/-- The separator: close the last zero residual and reset `win` to `2`. -/
def sep : List Instr := [.endClause, .clear .win, .addTo .win .w, .addTo .win .w]

/-- Second-pass chunks: count doubled marks, emit the forcing pair, reset `win` to `2`. -/
def chunk2x : Sym → List Instr
  | .mark => [.addTo .win .w, .addTo .win .w]
  | .pos => forcingJob ++ [.clear .win, .addTo .win .w, .addTo .win .w]
  | .neg => forcingJob ++ [.clear .win, .addTo .win .w, .addTo .win .w]
  | .endClause => []

/-- The whole job of an input. -/
def job (x : List Sym) : List Instr := TwoPassMachine.job pre chunk1 sep chunk2x x

/-! ### Rendering the first pass -/

/-- The symbols of a residual list. -/
def resSyms (rs : List PolyResidual) : List Sym := encode (rs.flatMap residualClauses)

/-- The open part of a residual: its clauses without the final clause end. -/
def openLink (k : ℕ) (l : Literal ℕ) : List Sym :=
  (factorClause true (linking k l).1).flatMap encodeLiteral

theorem resSyms_append (A B : List PolyResidual) : resSyms (A ++ B) = resSyms A ++ resSyms B := by
  simp [resSyms, List.flatMap_append, encode_append]

theorem marks2 (n : ℕ) :
    Sym.mark :: Sym.mark :: List.replicate n Sym.mark =
      List.replicate n Sym.mark ++ [.mark, .mark] := by
  rw [show [Sym.mark, Sym.mark] = List.replicate 2 Sym.mark from rfl,
    List.replicate_append_replicate]
  rfl

theorem render_marks1 (b i t v : ℕ) :
    render (regs b i t) (jobOf chunk1 (List.replicate v .mark)) =
      (List.replicate (2 * v) .mark, regs b i t) := by
  induction v with
  | zero => simp [jobOf, render]
  | succ v ih =>
      rw [List.replicate_succ, show Sym.mark :: List.replicate v Sym.mark =
        [Sym.mark] ++ List.replicate v Sym.mark from rfl, jobOf_append, render_append]
      have h1 : render (regs b i t) (jobOf chunk1 [.mark]) = ([.mark, .mark], regs b i t) := by
        simp [jobOf, chunk1, render, renderInstr]
      rw [h1]
      simp only
      rw [ih, show 2 * (v + 1) = 2 + 2 * v by ring, List.replicate_add]
      rfl

theorem render_forcing (b i t : ℕ) :
    render (regs b i t) forcingJob = (resSyms (forcingRes i), regs b i t) := by
  simp [forcingJob, render, renderInstr, resSyms, forcingRes, residualClauses, factorClause,
    encode, encodeClause, encodeLiteral]

theorem render_lit1 (b k t : ℕ) (l : Literal ℕ) :
    render (regs b (yIdx k) t) (jobOf chunk1 (encodeLiteral l)) =
      (.endClause :: (resSyms (forcingRes (yIdx k)) ++ resSyms (forcingRes (yIdx k)) ++
        openLink k l), regs b (yIdx (k + 1)) t) := by
  have hincr : render (regs b (yIdx k) t) (MaxCutJob.incr .win 2) =
      ([], regs b (yIdx (k + 1)) t) := by
    rw [FixedPrimeMaxCutJob.render_incr_regs _ _ _ _ (by decide)]
    simp [yIdx]
    ring_nf
  cases l with
  | positive v =>
      rw [encodeLiteral, show Sym.pos :: List.replicate v Sym.mark =
        [Sym.pos] ++ List.replicate v Sym.mark from rfl, jobOf_append, render_append]
      have h1 : render (regs b (yIdx k) t) (jobOf chunk1 [.pos]) =
          (.endClause :: (resSyms (forcingRes (yIdx k)) ++ resSyms (forcingRes (yIdx k)) ++
            [.pos, .pos] ++ List.replicate (yIdx k) .mark ++ [.neg, .mark, .mark]),
            regs b (yIdx (k + 1)) t) := by
        simp only [jobOf, chunk1, List.map_cons, List.map_nil, List.flatten_cons,
          List.flatten_nil, List.append_nil, render_append]
        simp only [render, renderInstr]
        rw [render_forcing]
        simp only
        rw [render_forcing]
        simp only [openPos, render, renderInstr, regs_win]
        rw [hincr]
        simp
      rw [h1]
      simp only
      rw [render_marks1]
      refine Prod.ext ?_ rfl
      simp [openLink, factorClause, linking, encodeLiteral, xIdx, List.replicate_add,
        List.append_assoc]
      ring_nf
      exact marks2 _
  | negative v =>
      rw [encodeLiteral, show Sym.neg :: List.replicate v Sym.mark =
        [Sym.neg] ++ List.replicate v Sym.mark from rfl, jobOf_append, render_append]
      have h1 : render (regs b (yIdx k) t) (jobOf chunk1 [.neg]) =
          (.endClause :: (resSyms (forcingRes (yIdx k)) ++ resSyms (forcingRes (yIdx k)) ++
            [.pos, .pos] ++ List.replicate (yIdx k) .mark ++ [.pos, .pos, .mark, .mark]),
            regs b (yIdx (k + 1)) t) := by
        simp only [jobOf, chunk1, List.map_cons, List.map_nil, List.flatten_cons,
          List.flatten_nil, List.append_nil, render_append]
        simp only [render, renderInstr]
        rw [render_forcing]
        simp only
        rw [render_forcing]
        simp only [openNeg, render, renderInstr, regs_win]
        rw [hincr]
        simp
      rw [h1]
      simp only
      rw [render_marks1]
      refine Prod.ext ?_ rfl
      simp [openLink, factorClause, linking, encodeLiteral, xIdx, List.replicate_add,
        List.append_assoc]
      ring_nf
      exact marks2 _

/-- The items of the first-pass output: each item is preceded by a clause end that closes
the previous open residual. -/
def litItems : ℕ → Clause ℕ → List (List Sym)
  | _, [] => []
  | k, l :: ls =>
      (resSyms (forcingRes (yIdx k)) ++ resSyms (forcingRes (yIdx k)) ++ openLink k l) ::
        litItems (k + 1) ls

/-- The item of a clause end: the clause product and an opened zero residual. -/
def endItem (k : ℕ) : List Sym := resSyms [product k] ++ [.pos]

def clauseItems (k : ℕ) (c : Clause ℕ) : List (List Sym) := litItems k c ++ [endItem k]

def formulaItems : ℕ → Formula ℕ → List (List Sym)
  | _, [] => []
  | k, c :: F => clauseItems k c ++ formulaItems (k + c.length) F

theorem render_lits1 (b t : ℕ) (c : Clause ℕ) : ∀ k,
    render (regs b (yIdx k) t) (jobOf chunk1 (c.flatMap encodeLiteral)) =
      ((litItems k c).flatMap (.endClause :: ·), regs b (yIdx (k + c.length)) t) := by
  induction c with
  | nil => intro k; simp [jobOf, render, litItems]
  | cons l c ih =>
      intro k
      rw [List.flatMap_cons, jobOf_append, render_append, render_lit1]
      simp only
      rw [ih]
      simp only [litItems, List.flatMap_cons, List.length_cons]
      refine Prod.ext ?_ ?_
      · simp
      · simp only
        congr 2
        ring

theorem render_clause1 (k t : ℕ) (c : Clause ℕ) :
    render (regs (yIdx k) (yIdx k) t) (jobOf chunk1 (encodeClause c)) =
      ((clauseItems k c).flatMap (.endClause :: ·),
        regs (yIdx (k + c.length)) (yIdx (k + c.length)) (t + 9)) := by
  rw [encodeClause, jobOf_append, render_append, render_lits1]
  simp only
  have he : ∀ i, render (regs (yIdx k) i t) (jobOf chunk1 [.endClause]) =
      (.endClause :: endItem k, regs i i (t + 9)) := by
    intro i
    simp only [jobOf, chunk1, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, render_append]
    simp only [prodJob, MaxCutJob.incr, List.replicate, render, renderInstr]
    simp [endItem, resSyms, product, residualClauses, factorClause, encode, encodeClause,
      encodeLiteral, yIdx, List.replicate_add, List.append_assoc]
    ring_nf
    rw [show 2 + k * 2 = k * 2 + 2 by ring, show 4 + k * 2 = k * 2 + 4 by ring,
      List.replicate_add, List.replicate_add]
    simp [List.replicate, List.append_assoc]
  rw [he]
  simp [clauseItems, List.flatMap_append]

theorem render_pass1 (F : Formula ℕ) : ∀ k t,
    render (regs (yIdx k) (yIdx k) t) (jobOf chunk1 (encode F)) =
      ((formulaItems k F).flatMap (.endClause :: ·),
        regs (yIdx (k + (F.map List.length).sum)) (yIdx (k + (F.map List.length).sum))
          (t + 9 * F.length)) := by
  induction F with
  | nil => intro k t; simp [jobOf, render, encode, formulaItems]
  | cons c F ih =>
      intro k t
      rw [encode_cons, jobOf_append, render_append, render_clause1]
      simp only
      rw [ih]
      simp only [formulaItems, List.flatMap_append, List.map_cons, List.sum_cons,
        List.length_cons]
      refine Prod.ext rfl ?_
      simp only
      congr 1 <;> ring_nf

theorem telescope_aux (L : List (List Sym)) :
    L.flatMap (Sym.endClause :: ·) ++ [Sym.endClause] =
      [Sym.endClause] ++ L.flatMap (· ++ [Sym.endClause]) := by
  induction L with
  | nil => rfl
  | cons z L ih =>
      simp only [List.flatMap_cons, List.cons_append, List.append_assoc, List.nil_append] at ih ⊢
      rw [ih]

theorem telescope (a : Sym) (L : List (List Sym)) :
    [a] ++ L.flatMap (.endClause :: ·) ++ [Sym.endClause] =
      [a, .endClause] ++ L.flatMap (· ++ [.endClause]) := by
  rw [List.append_assoc, telescope_aux]
  rfl

theorem closed_litItems (c : Clause ℕ) : ∀ k,
    (litItems k c).flatMap (· ++ [.endClause]) = resSyms (litsBlock k c) := by
  induction c with
  | nil => intro k; simp [litItems, litsBlock, resSyms, encode]
  | cons l c ih =>
      intro k
      rw [litItems, litsBlock, List.flatMap_cons, ih, resSyms_append, litBlock, resSyms_append,
        resSyms_append]
      cases l <;> simp [resSyms, residualClauses, linking, openLink, factorClause, encode,
        encodeClause, List.append_assoc]

theorem closed_formulaItems (F : Formula ℕ) : ∀ k,
    (formulaItems k F).flatMap (· ++ [.endClause]) = resSyms (formulaBlocks k F) := by
  induction F with
  | nil => intro k; simp [formulaItems, formulaBlocks, resSyms, encode]
  | cons c F ih =>
      intro k
      rw [formulaItems, formulaBlocks, List.flatMap_append, ih, resSyms_append, clauseItems,
        clauseBlock, List.flatMap_append, closed_litItems, resSyms_append]
      simp [endItem, resSyms, residualClauses, dummy, factorClause, encode, encodeClause,
        encodeLiteral, List.append_assoc]

/-! ### Rendering the second pass -/

theorem render_lit2 (b t : ℕ) (l : Literal ℕ) :
    render (regs b 2 t) (jobOf chunk2x (encodeLiteral l).reverse) =
      (resSyms (forcingRes (xIdx (litVar l))), regs b 2 t) := by
  have hm : ∀ v i, render (regs b i t) (jobOf chunk2x (List.replicate v .mark)) =
      ([], regs b (i + 2 * v) t) := by
    intro v
    induction v with
    | zero => intro i; simp [jobOf, render]
    | succ v ih =>
        intro i
        rw [List.replicate_succ, show Sym.mark :: List.replicate v Sym.mark =
          [Sym.mark] ++ List.replicate v Sym.mark from rfl, jobOf_append, render_append]
        simp only [jobOf, chunk2x, List.map_cons, List.map_nil, List.flatten_cons,
          List.flatten_nil, List.append_nil, render, renderInstr] at ih ⊢
        simp only [regs_win, regs_w, update_win, List.nil_append]
        rw [ih]
        ring_nf
  have hs : ∀ (s : Sym), s = .pos ∨ s = .neg → ∀ v,
      render (regs b (2 + 2 * v) t) (jobOf chunk2x [s]) =
        (resSyms (forcingRes (xIdx v)), regs b 2 t) := by
    intro s hs v
    rcases hs with rfl | rfl <;>
      simp [jobOf, chunk2x, forcingJob, render, renderInstr, resSyms, forcingRes,
        residualClauses, factorClause, encode, encodeClause, encodeLiteral, xIdx,
        Nat.add_comm]
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

theorem render_lits2 (b t : ℕ) (L : List (Literal ℕ)) :
    render (regs b 2 t) (jobOf chunk2x (L.flatMap fun l => (encodeLiteral l).reverse)) =
      (resSyms (L.flatMap fun l => forcingRes (xIdx (litVar l))), regs b 2 t) := by
  induction L with
  | nil => simp [jobOf, render, resSyms, encode]
  | cons l L ih =>
      rw [List.flatMap_cons, jobOf_append, render_append, render_lit2]
      simp only
      rw [ih, List.flatMap_cons, resSyms_append]

theorem render_pass2 (b t : ℕ) (F : Formula ℕ) :
    render (regs b 2 t) (jobOf chunk2x (encode F).reverse) =
      (resSyms (xForcing F), regs b 2 t) := by
  rw [TwoPassMachine.reverse_encode, xForcing]
  induction F.reverse with
  | nil => simp [jobOf, render, resSyms, encode]
  | cons c G ih =>
      rw [List.flatMap_cons, jobOf_append, render_append, List.flatMap_cons, resSyms_append]
      have hc : jobOf chunk2x (Sym.endClause :: c.reverse.flatMap
          fun l => (encodeLiteral l).reverse) =
          jobOf chunk2x (c.reverse.flatMap fun l => (encodeLiteral l).reverse) := by
        simp [jobOf, chunk2x]
      rw [hc, render_lits2]
      simp only
      rw [ih]

/-! ### The whole job -/

theorem render_job (F : Formula ℕ) :
    (render (regs 0 1 0) (job (encode F))).1 = polyUnaryEncoding.encode (polyReduce F) := by
  rw [job, TwoPassMachine.job, render_append, render_append, render_append, render_append]
  have h0 : render (regs 0 1 0) pre = ([Sym.pos], regs (yIdx 0) (yIdx 0) 0) := by
    simp [pre, render, renderInstr, yIdx]
  rw [h0]
  simp only
  rw [render_pass1]
  simp only
  have h1 : ∀ b i t, render (regs b i t) sep = ([Sym.endClause], regs b 2 t) := by
    intro b i t
    simp [sep, render, renderInstr]
  rw [h1]
  simp only
  rw [render_pass2]
  simp only
  have h2 : ∀ b t, render (regs b 2 t) suffix = (encodeClause [.positive t], regs b 2 t) := by
    intro b t
    simp [suffix, render, renderInstr, encodeClause, encodeLiteral]
  rw [h2]
  have key : Sym.pos :: ((formulaItems 0 F).flatMap (Sym.endClause :: ·) ++ [Sym.endClause]) =
      encode (residualClauses dummy) ++ resSyms (formulaBlocks 0 F) := by
    have := telescope Sym.pos (formulaItems 0 F)
    rw [closed_formulaItems] at this
    simpa [dummy, residualClauses, factorClause, encode, encodeClause, encodeLiteral] using this
  have e1 : ∀ (X R B : List Sym), [Sym.pos] ++ X ++ [Sym.endClause] ++ R ++ B =
      (Sym.pos :: (X ++ [Sym.endClause])) ++ R ++ B := by
    intros; simp
  rw [e1, key]
  simp [polyUnaryEncoding, polyReduce, polyFormula, resSyms, List.append_assoc, encode]

/-! ### Register bounds and validity -/

theorem chunk1_bounded : ChunkBounded chunk1 := by
  intro s M c d R h _hc hcM hdM
  obtain ⟨b, i, k, rfl, hb, hi, hk⟩ := h
  cases s with
  | mark =>
      refine ⟨?_, ⟨b, i, k, by simp [chunk1, render, renderInstr], by omega, by omega,
        by omega⟩⟩
      simp only [chunk1]
      repeat' refine pcons ?_ ?_
      all_goals first
        | (refine pnil ?_; simp [renderInstr, regsLE_regs]; omega)
        | (simp [renderInstr, regsLE_regs]; omega)
  | pos =>
      refine ⟨?_, ⟨b, i + 2, k, ?_, by omega, by omega, by omega⟩⟩
      · simp only [chunk1, forcingJob, openPos, MaxCutJob.incr, List.replicate, List.cons_append,
          List.nil_append]
        repeat' refine pcons ?_ ?_
        all_goals first
          | (refine pnil ?_; simp [renderInstr, regsLE_regs]; omega)
          | (simp [renderInstr, regsLE_regs]; omega)
      · simp [chunk1, forcingJob, openPos, MaxCutJob.incr, render, renderInstr]
  | neg =>
      refine ⟨?_, ⟨b, i + 2, k, ?_, by omega, by omega, by omega⟩⟩
      · simp only [chunk1, forcingJob, openNeg, MaxCutJob.incr, List.replicate, List.cons_append,
          List.nil_append]
        repeat' refine pcons ?_ ?_
        all_goals first
          | (refine pnil ?_; simp [renderInstr, regsLE_regs]; omega)
          | (simp [renderInstr, regsLE_regs]; omega)
      · simp [chunk1, forcingJob, openNeg, MaxCutJob.incr, render, renderInstr]
  | endClause =>
      refine ⟨?_, ⟨i, i, k + 9, ?_, by omega, by omega, by omega⟩⟩
      · simp only [chunk1, prodJob, MaxCutJob.incr, List.replicate, List.cons_append,
          List.nil_append]
        repeat' refine pcons ?_ ?_
        all_goals first
          | (refine pnil ?_; simp [renderInstr, regsLE_regs]; omega)
          | (simp [renderInstr, regsLE_regs]; omega)
      · simp [chunk1, prodJob, MaxCutJob.incr, render, renderInstr]

theorem chunk2x_bounded : ChunkBounded chunk2x := by
  intro s M c d R h _hc hcM hdM
  obtain ⟨b, i, k, rfl, hb, hi, hk⟩ := h
  cases s with
  | mark =>
      refine ⟨?_, ⟨b, i + 2, k, ?_, by omega, by omega, by omega⟩⟩
      · simp only [chunk2x]
        repeat' refine pcons ?_ ?_
        all_goals first
          | (refine pnil ?_; simp [renderInstr, regsLE_regs]; omega)
          | (simp [renderInstr, regsLE_regs]; omega)
      · simp [chunk2x, render, renderInstr]
  | pos =>
      refine ⟨?_, ⟨b, 2, k, by simp [chunk2x, forcingJob, render, renderInstr], by omega,
        by omega, by omega⟩⟩
      simp only [chunk2x, forcingJob, List.cons_append, List.nil_append]
      repeat' refine pcons ?_ ?_
      all_goals first
        | (refine pnil ?_; simp [renderInstr, regsLE_regs]; omega)
        | (simp [renderInstr, regsLE_regs]; omega)
  | neg =>
      refine ⟨?_, ⟨b, 2, k, by simp [chunk2x, forcingJob, render, renderInstr], by omega,
        by omega, by omega⟩⟩
      simp only [chunk2x, forcingJob, List.cons_append, List.nil_append]
      repeat' refine pcons ?_ ?_
      all_goals first
        | (refine pnil ?_; simp [renderInstr, regsLE_regs]; omega)
        | (simp [renderInstr, regsLE_regs]; omega)
  | endClause =>
      refine ⟨pnil ?_, ⟨b, i, k, by simp [chunk2x, render], by omega, by omega, by omega⟩⟩
      rw [regsLE_regs]; omega

theorem pre_bounded : BlockBounded pre := by
  intro M c d R h _hc hcM hdM
  obtain ⟨b, i, k, rfl, hb, hi, hk⟩ := h
  refine ⟨?_, ⟨i, i, k, by simp [pre, render, renderInstr], by omega, by omega, by omega⟩⟩
  simp only [pre]
  repeat' refine pcons ?_ ?_
  all_goals first
    | (refine pnil ?_; simp [renderInstr, regsLE_regs]; omega)
    | (simp [renderInstr, regsLE_regs]; omega)

theorem sep_bounded : BlockBounded sep := by
  intro M c d R h hc hcM hdM
  obtain ⟨b, i, k, rfl, hb, hi, hk⟩ := h
  refine ⟨?_, ⟨b, 2, k, by simp [sep, render, renderInstr], by omega, by omega, by omega⟩⟩
  simp only [sep]
  repeat' refine pcons ?_ ?_
  all_goals first
    | (refine pnil ?_; simp [renderInstr, regsLE_regs]; omega)
    | (simp [renderInstr, regsLE_regs]; omega)

theorem chunk1_ok (s : Sym) : ∀ i ∈ chunk1 s, i.ok := by
  cases s <;> simp [chunk1, forcingJob, openPos, openNeg, prodJob, MaxCutJob.incr, Instr.ok,
    List.replicate]

theorem chunk2x_ok (s : Sym) : ∀ i ∈ chunk2x s, i.ok := by
  cases s <;> simp [chunk2x, forcingJob, Instr.ok]

theorem chunk1_length_le (s : Sym) : (chunk1 s).length ≤ 40 := by
  cases s <;> simp [chunk1, forcingJob, openPos, openNeg, prodJob, MaxCutJob.incr]

theorem chunk2x_length_le (s : Sym) : (chunk2x s).length ≤ 15 := by
  cases s <;> simp [chunk2x, forcingJob]

/-! ### Polynomial time and hardness -/

/-- The multilinear polynomial-residual reduction is computed in polynomial time by the
two-pass machine. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime CNF.Unary.finEncoding polyUnaryEncoding polyReduce where
  tm := toGenMachine (TwoPassMachine.R pre chunk1 sep chunk2x)
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := TwoPassMachine.timePoly
  outputsFun F := by
    have run := TwoPassMachine.outputsInTime pre chunk1 sep chunk2x (encode F)
      (polyUnaryEncoding.encode (polyReduce F))
      (TwoPassMachine.job_ok _ _ _ _ (by simp [pre, Instr.ok]) chunk1_ok
        (by simp [sep, Instr.ok]) chunk2x_ok _)
      (TwoPassMachine.prefixLE_job _ _ _ _ pre_bounded chunk1_bounded sep_bounded
        chunk2x_bounded _)
      (TwoPassMachine.job_length_le _ _ _ _ (by simp [pre]) chunk1_length_le (by simp [sep])
        chunk2x_length_le _) (render_job F)
    simpa [Equiv.refl] using run

/-- The checked polynomial-time reduction from unary CNF-SAT to the multilinear
degree-three polynomial-residual problem: the library's chain reduction to exact width
three, then `polyReduce`. -/
noncomputable def satReduction (p : ℕ) [Fact p.Prime] :
    CNF.Unary.encodedUnarySAT.PolytimeReducesTo (encodedUnaryPolyML p) where
  map := polyReduce ∘ CNF.Chain.chainThree
  correct F := by
    show F.Satisfiable ↔ PolyRegressionLangML p (polyReduce (CNF.Chain.chainThree F))
    rw [← CNF.Chain.satisfiable_chainThree]
    exact poly_iff _ (CNF.Chain.exactWidth_chainThree F)
  polytime := ⟨MachineComposition.compositionComputableInPolyTime CNF.Unary.finEncoding
    CNF.Unary.finEncoding polyUnaryEncoding CNF.Chain.chainThree polyReduce
    ChainMachine.computableInPolyTime computableInPolyTime⟩

/-- **Thesis `cor:sudoku-polynomial-dyadic-hardness`, unary encoding.** For every prime
`p`, minimisation of positive polynomial-residual objectives over `ℤ_p^n` is NP-hard,
already when every residual is multilinear of degree at most three. -/
theorem encodedUnaryPolyML_NPHard (p : ℕ) [Fact p.Prime] : (encodedUnaryPolyML p).NPHard :=
  EncodedLanguage.NPHard.of_reduction (satReduction p) CookLevin.encodedUnarySAT_NPHard

/-- Re-encoding polynomial-residual instances in binary, in polynomial time. -/
noncomputable def binaryComputable :
    TM2ComputableInPolyTime polyUnaryEncoding polyBinaryEncoding id where
  tm := BinaryConvert.machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := BinaryConvert.timePoly
  outputsFun x := by
    have run := toMachine_outputsInTime_le BinaryConvert.conv .input .out
      (encode (polyFormula x.1 x.2)) (Formula.encode (polyFormula x.1 x.2)) _
      (by
        have h1 := BinaryConvert.initList_eq (encode (polyFormula x.1 x.2))
        have h2 := BinaryConvert.haltList_eq (Formula.encode (polyFormula x.1 x.2))
        simp only [BinaryConvert.machine] at h1 h2
        rw [h1, h2]
        exact BinaryConvert.conv_exits _)
    have run' := evalsToInTimeMono run
      (show BinaryConvert.convBound (encode (polyFormula x.1 x.2)).length ≤
          BinaryConvert.timePoly.eval (encode (polyFormula x.1 x.2)).length by
        simp only [BinaryConvert.timePoly, eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one]
        exact BinaryConvert.convBound_le _)
    simpa [Equiv.refl, polyUnaryEncoding, polyBinaryEncoding] using! run'

/-- Unary polynomial-residual instances reduce to binary ones by re-encoding. -/
noncomputable def binaryReduction (p : ℕ) [Fact p.Prime] :
    (encodedUnaryPolyML p).PolytimeReducesTo (encodedPolyML p) where
  map := id
  correct _ := Iff.rfl
  polytime := ⟨binaryComputable⟩

/-- **Thesis `cor:sudoku-polynomial-dyadic-hardness`, binary encoding.** -/
theorem encodedPolyML_NPHard (p : ℕ) [Fact p.Prime] : (encodedPolyML p).NPHard :=
  EncodedLanguage.NPHard.of_reduction (binaryReduction p) (encodedUnaryPolyML_NPHard p)

/-- **Thesis `cor:sudoku-polynomial-dyadic-hardness`** over `ℤ_2`, in both encodings. -/
theorem dyadic_poly_nphard :
    (encodedUnaryPolyML 2).NPHard ∧ (encodedPolyML 2).NPHard := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨encodedUnaryPolyML_NPHard 2, encodedPolyML_NPHard 2⟩

end PhdThesisLean.PolynomialResidualMachine

#print axioms PhdThesisLean.PolynomialResidualMachine.dyadic_poly_nphard
