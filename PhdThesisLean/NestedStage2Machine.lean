import PhdThesisLean.NestedStage2Reduction
import PhdThesisLean.TwoPassMachine

/-!
# Stage 2 of the nested family is a polynomial-time reduction

This module completes the complexity part of Stage 2 of thesis Theorem
`thm:nested-easy-hard-easy` (`complexity-regimes/body.tex`): the map `G ↦ A'_G` is a
polynomial-time reduction from an NP-hard problem, so summed `5`-adic regression over
the family `{A'_G}` is NP-hard.

The instance `NestedStage2Reduction.nestedReduce (G, K)` is computed by the two-pass
machine of `TwoPassMachine.lean`.

* First-pass chunks (`chunkA`) stream the edge rows exactly as in the fixed-prime
  machine, but without zero rows: a sign symbol moves `win` to `base`, marks count in
  `win`, and a clause end emits the five edge rows on `base` and `win`, adds `3` to the
  bound, and restarts `win` at the fresh vertex `z`. The threshold clause becomes the
  pendant edge `(z, K)`.
* The separator clears `base` and restarts `win` at `1`.
* Second-pass chunks (`chunkB`) emit one forcing pair per input symbol on the vertex
  counter `win`. On the reversed input the threshold clause comes first, so `base`
  serves as a flag that is set at the first sign symbol: the leading clause end and the
  `K` marks of the threshold add nothing to the bound, and every other symbol adds one.
  The bound register therefore ends at `3|E| + 2 + L - K` without any subtraction.

`computableInPolyTime` packages the run within `10⁶ (n + 1)²` steps. With the library's
Cook--Levin-based hardness of unary Max-Cut this gives `stage2Reduction` and
`encodedUnaryRegression_five_NPHard_via_stage2`. Composed with the library's chain and
Max-Cut gadget reductions from CNF-SAT (`satStage2Reduction`), every produced dataset is
literally `A'_G` of a loopless graph (`satStage2_dataset_eq_A'_G`), which is the
family statement of Stage 2.
-/

namespace PhdThesisLean.NestedStage2Machine

open Turing Computability Polynomial
open LeanNPHardness LeanNPHardness.CNF LeanNPHardness.CNF.Unary LeanNPHardness.TableauJobs
open LeanNPHardness.TableauStacks LeanNPHardness.Routines LeanNPHardness.MachinePrimitives
open LeanNPHardness.MaxCut
open PhdThesisLean.PadicRegressionLanguage PhdThesisLean.NestedStage2Reduction
open PhdThesisLean.FixedPrimeMaxCutReduction (edgeRows)
open PhdThesisLean.FixedPrimeMaxCutJob (regs regs_base regs_win regs_w regs_pw update_base
  update_win update_pw regsLE_regs Bounded render_incr_regs)
open PhdThesisLean.TwoPassMachine (jobOf jobOf_append suffix BlockBounded ChunkBounded)

private alias pcons := FixedPrimeMaxCutJob.prefixLE_cons
private alias pnil := FixedPrimeMaxCutJob.prefixLE_nil

/-! ### The job -/

/-- The five edge rows on the literal indices held by `base` and `win`. -/
def rows5 : List Instr :=
  [.lit true, .reg .base, .endClause,
    .lit true, .reg .base, .lit true, .endClause,
    .lit true, .reg .win, .endClause,
    .lit true, .reg .win, .lit true, .endClause,
    .lit true, .reg .base, .lit true, .reg .win, .lit true, .endClause]

/-- First-pass chunks: the edge rows of the Max-Cut instance. -/
def chunkA : Sym → List Instr
  | .mark => [.addTo .win .w]
  | .pos => [.clear .base, .addTo .base .win, .clear .win, .addTo .win .w, .addTo .win .w]
  | .neg => []
  | .endClause => rows5 ++ MaxCutJob.incr .pw 3 ++
      [.clear .base, .addTo .base .win, .clear .win, .addTo .win .w]

/-- The separator: clear the flag `base` and restart the vertex counter. -/
def sepA : List Instr := [.clear .base, .clear .win, .addTo .win .w]

/-- The forcing pair on the vertex counter `win`. -/
def vertexJob : List Instr :=
  [.lit true, .reg .win, .endClause, .lit true, .reg .win, .lit true, .endClause]

/-- Second-pass chunks: one forcing pair per symbol; the bound grows by the flag on
marks and clause ends and by one on sign symbols, which also raise the flag. -/
def chunkB : Sym → List Instr
  | .mark => vertexJob ++ [.addTo .win .w, .addTo .pw .base]
  | .pos => vertexJob ++ [.addTo .win .w, .addTo .pw .w, .clear .base, .addTo .base .w]
  | .neg => vertexJob ++ [.addTo .win .w, .addTo .pw .w, .clear .base, .addTo .base .w]
  | .endClause => vertexJob ++ [.addTo .win .w, .addTo .pw .base]

/-- The whole job of an input. -/
def job (x : List Sym) : List Instr := TwoPassMachine.job [] chunkA sepA chunkB x

/-! ### Rendering the first pass -/

theorem render_rows5 (b i k : ℕ) :
    render (regs b i k) rows5 = (encode (edgeRows b i), regs b i k) := by
  simp [rows5, render, renderInstr, edgeRows, encode, encodeClause, encodeLiteral]

theorem render_posA (b i k : ℕ) : render (regs b i k) (jobOf chunkA [.pos]) = ([], regs i 2 k) := by
  simp [jobOf, chunkA, render, renderInstr]

theorem render_endA (b i k : ℕ) :
    render (regs b i k) (jobOf chunkA [.endClause]) =
      (encode (edgeRows b i), regs i 1 (k + 3)) := by
  have hj : jobOf chunkA [.endClause] = rows5 ++ (MaxCutJob.incr .pw 3 ++
      [.clear .base, .addTo .base .win, .clear .win, .addTo .win .w]) := by
    simp [jobOf, chunkA]
  rw [hj, render_append, render_rows5]
  simp only
  rw [render_append, render_incr_regs _ _ _ _ (by decide)]
  simp only [regs_pw, update_pw]
  simp [render, renderInstr]

theorem render_marksA (b i k u : ℕ) :
    render (regs b i k) (jobOf chunkA (List.replicate u .mark)) = ([], regs b (i + u) k) := by
  induction u generalizing i with
  | zero => simp [jobOf, render]
  | succ u ih =>
      rw [List.replicate_succ, show Sym.mark :: List.replicate u Sym.mark =
        [Sym.mark] ++ List.replicate u Sym.mark from rfl, jobOf_append, render_append]
      have h1 : render (regs b i k) (jobOf chunkA [.mark]) = ([], regs b (i + 1) k) := by
        simp [jobOf, chunkA, render, renderInstr]
      rw [h1]
      simp only [List.nil_append]
      rw [ih]
      ring_nf

theorem render_eposA (b i k u : ℕ) :
    render (regs b i k) (jobOf chunkA (MaxCutJob.epos u)) = ([], regs i (u + 2) k) := by
  rw [MaxCutJob.epos, encodeLiteral, show Sym.pos :: List.replicate u Sym.mark =
    [Sym.pos] ++ List.replicate u Sym.mark from rfl, jobOf_append, render_append, render_posA]
  simp only [List.nil_append]
  rw [render_marksA]
  ring_nf

theorem render_edgeA (b k : ℕ) (e : Edge) :
    render (regs b 1 k) (jobOf chunkA (MaxCutJob.edgeSyms e)) =
      (encode (edgeRows (e.1 + 2) (e.2 + 2)), regs (e.2 + 2) 1 (k + 3)) := by
  rw [MaxCutJob.edgeSyms, jobOf_append, jobOf_append, render_append, render_append,
    render_eposA]
  simp only [List.nil_append]
  rw [render_eposA, render_endA]
  simp

theorem render_edgesA (G : List Edge) : ∀ b k, ∃ b',
    render (regs b 1 k) (jobOf chunkA (G.flatMap MaxCutJob.edgeSyms)) =
      (encode (G.flatMap fun e => edgeRows (e.1 + 2) (e.2 + 2)),
        regs b' 1 (k + 3 * G.length)) := by
  induction G with
  | nil => intro b k; exact ⟨b, by simp [jobOf, render, encode]⟩
  | cons e G ih =>
      intro b k
      obtain ⟨b', hb'⟩ := ih (e.2 + 2) (k + 3)
      refine ⟨b', ?_⟩
      rw [List.flatMap_cons, jobOf_append, render_append, render_edgeA]
      simp only
      rw [hb']
      refine Prod.ext ?_ ?_
      · simp [encode_append]
      · simp only [List.length_cons]
        congr 1
        ring_nf

theorem render_passA (G : List Edge) (K : ℕ) :
    render (regs 0 1 0) (jobOf chunkA (encode (graphFormula G K))) =
      (encode (G.flatMap (fun e => edgeRows (e.1 + 2) (e.2 + 2)) ++ edgeRows 1 (K + 2)),
        regs (K + 2) 1 (3 * G.length + 3)) := by
  obtain ⟨b', hb'⟩ := render_edgesA G 0 0
  rw [MaxCutJob.encode_edges, List.append_assoc, jobOf_append, jobOf_append, render_append,
    hb']
  simp only
  rw [render_append, render_eposA]
  simp only [List.nil_append]
  rw [render_endA]
  refine Prod.ext ?_ ?_
  · simp [encode_append]
  · simp only
    congr 1
    ring_nf

/-! ### Rendering the second pass -/

/-- The symbols of the forcing pairs of vertices `i, …, i + n - 1`. -/
def vertexSyms : ℕ → ℕ → List Sym
  | _, 0 => []
  | i, n + 1 => encode (vertexRows i) ++ vertexSyms (i + 1) n

theorem vertexSyms_add (a : ℕ) :
    ∀ i b, vertexSyms i (a + b) = vertexSyms i a ++ vertexSyms (i + a) b := by
  induction a with
  | zero => intro i b; simp [vertexSyms]
  | succ a ih =>
      intro i b
      rw [show a + 1 + b = (a + b) + 1 by ring, vertexSyms, vertexSyms, ih, List.append_assoc]
      congr 3
      ring_nf

theorem encode_vertexRows_range (i n : ℕ) :
    encode ((List.range n).flatMap fun j => vertexRows (j + i)) = vertexSyms i n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ, List.flatMap_append, encode_append, ih, vertexSyms_add n i 1]
      simp [vertexSyms, Nat.add_comm]

theorem render_vertexJob (b i k : ℕ) :
    render (regs b i k) vertexJob = (encode (vertexRows i), regs b i k) := by
  simp [vertexJob, render, renderInstr, vertexRows, encode, encodeClause, encodeLiteral]

theorem render_markB (b i k : ℕ) :
    render (regs b i k) (jobOf chunkB [.mark]) =
      (encode (vertexRows i), regs b (i + 1) (k + b)) := by
  simp [jobOf, chunkB, render_append, render_vertexJob, render, renderInstr]

theorem render_endB (b i k : ℕ) :
    render (regs b i k) (jobOf chunkB [.endClause]) =
      (encode (vertexRows i), regs b (i + 1) (k + b)) := by
  simp [jobOf, chunkB, render_append, render_vertexJob, render, renderInstr]

theorem render_signB (b i k : ℕ) (s : Sym) (hs : s = .pos ∨ s = .neg) :
    render (regs b i k) (jobOf chunkB [s]) = (encode (vertexRows i), regs 1 (i + 1) (k + 1)) := by
  rcases hs with rfl | rfl <;>
    simp [jobOf, chunkB, render_append, render_vertexJob, render, renderInstr]

theorem render_flagged (S : List Sym) : ∀ i k,
    render (regs 1 i k) (jobOf chunkB S) =
      (vertexSyms i S.length, regs 1 (i + S.length) (k + S.length)) := by
  induction S with
  | nil => intro i k; simp [jobOf, render, vertexSyms]
  | cons s S ih =>
      intro i k
      have h1 : render (regs 1 i k) (jobOf chunkB [s]) =
          (encode (vertexRows i), regs 1 (i + 1) (k + 1)) := by
        cases s with
        | mark => exact render_markB 1 i k
        | endClause => exact render_endB 1 i k
        | pos => exact render_signB 1 i k _ (Or.inl rfl)
        | neg => exact render_signB 1 i k _ (Or.inr rfl)
      rw [show s :: S = [s] ++ S from rfl, jobOf_append, render_append, h1]
      simp only
      rw [ih]
      simp only [List.singleton_append, List.length_cons, vertexSyms]
      refine Prod.ext rfl ?_
      congr 1
      ring_nf

theorem render_unflagged (K : ℕ) : ∀ i k,
    render (regs 0 i k) (jobOf chunkB (List.replicate K .mark)) =
      (vertexSyms i K, regs 0 (i + K) k) := by
  induction K with
  | zero => intro i k; simp [jobOf, render, vertexSyms]
  | succ K ih =>
      intro i k
      rw [List.replicate_succ, show Sym.mark :: List.replicate K Sym.mark =
        [Sym.mark] ++ List.replicate K Sym.mark from rfl, jobOf_append, render_append,
        render_markB]
      simp only [Nat.add_zero]
      rw [ih]
      simp only [vertexSyms]
      refine Prod.ext rfl ?_
      congr 1; ring_nf

theorem reverse_input (G : List Edge) (K : ℕ) :
    (encode (graphFormula G K)).reverse =
      [Sym.endClause] ++ List.replicate K .mark ++ [Sym.pos] ++
        (G.flatMap MaxCutJob.edgeSyms).reverse := by
  rw [MaxCutJob.encode_edges]
  simp [MaxCutJob.epos, encodeLiteral, List.reverse_append, List.append_assoc]

theorem input_length (G : List Edge) (K : ℕ) :
    (encode (graphFormula G K)).length = (G.flatMap MaxCutJob.edgeSyms).length + K + 2 := by
  rw [MaxCutJob.encode_edges]
  simp [MaxCutJob.epos, encodeLiteral]
  omega

theorem render_passB (G : List Edge) (K t : ℕ) :
    render (regs 0 1 t) (jobOf chunkB (encode (graphFormula G K)).reverse) =
      (vertexSyms 1 (encode (graphFormula G K)).length,
        regs 1 (1 + (encode (graphFormula G K)).length)
          (t + ((encode (graphFormula G K)).length - 1 - K))) := by
  set R := (G.flatMap MaxCutJob.edgeSyms).reverse.length with hR
  have hL : (encode (graphFormula G K)).length = R + K + 2 := by
    rw [input_length, hR, List.length_reverse]
  rw [reverse_input, jobOf_append, jobOf_append, jobOf_append, render_append, render_append,
    render_append, render_endB]
  simp only [Nat.add_zero]
  rw [render_unflagged, render_signB _ _ _ _ (Or.inl rfl)]
  simp only
  rw [render_flagged, hL]
  refine Prod.ext ?_ ?_
  · simp only
    rw [show R + K + 2 = 1 + (K + (1 + R)) by ring, vertexSyms_add, vertexSyms_add,
      vertexSyms_add]
    simp only [vertexSyms, List.append_nil, List.append_assoc]
    congr 3
  · simp only
    congr 1
    · omega
    · omega

/-! ### The whole job -/

theorem render_job (G : List Edge) (K : ℕ) :
    (render (regs 0 1 0) (job (encode (graphFormula G K)))).1 =
      PadicRegressionLanguage.unaryEncoding.encode (nestedReduce (G, K)) := by
  rw [job, TwoPassMachine.job, render_append, render_append, render_append, render_append]
  simp only [render]
  rw [render_passA]
  simp only
  have hsep : render (regs (K + 2) 1 (3 * G.length + 3)) sepA =
      ([], regs 0 1 (3 * G.length + 3)) := by
    simp [sepA, render, renderInstr]
  rw [hsep]
  simp only [List.nil_append]
  rw [render_passB]
  simp only
  have hsuf : ∀ b i t, render (regs b i t) suffix = (encodeClause [.positive t], regs b i t) := by
    intro b i t
    simp [suffix, render, renderInstr, encodeClause, encodeLiteral]
  rw [hsuf]
  have hL : K + 2 ≤ (encode (graphFormula G K)).length := by
    rw [input_length]; omega
  have hT : 3 * G.length + 3 + ((encode (graphFormula G K)).length - 1 - K) =
      stage2Bound G K (encode (graphFormula G K)).length := by
    rw [stage2Bound]; omega
  rw [hT]
  simp only [PadicRegressionLanguage.unaryEncoding, nestedReduce, stage2Rows, instanceFormula,
    MaxCut.unaryEncoding, encode_append, List.append_assoc]
  rw [encode_vertexRows_range]
  simp [encode]

/-! ### Register bounds and validity -/

theorem chunkA_bounded : ChunkBounded chunkA := by
  intro s M c d R h _hc hcM hdM
  obtain ⟨b, i, k, rfl, hb, hi, hk⟩ := h
  cases s with
  | mark =>
      refine ⟨pcons ?_ (pnil ?_), ⟨b, i + 1, k, by simp [chunkA, render, renderInstr],
        by omega, by omega, by omega⟩⟩ <;>
        simp [renderInstr, regsLE_regs] <;> omega
  | neg =>
      refine ⟨pnil ?_, ⟨b, i, k, by simp [chunkA, render], by omega, by omega, by omega⟩⟩
      rw [regsLE_regs]; omega
  | pos =>
      refine ⟨?_, ⟨i, 2, k, by simp [chunkA, render, renderInstr], by omega, by omega,
        by omega⟩⟩
      simp only [chunkA]
      repeat' refine pcons ?_ ?_
      all_goals first
        | (refine pnil ?_; simp [renderInstr, regsLE_regs]; omega)
        | (simp [renderInstr, regsLE_regs]; omega)
  | endClause =>
      refine ⟨?_, ⟨i, 1, k + 3, by simpa [jobOf] using congrArg Prod.snd (render_endA b i k),
        by omega, by omega, by omega⟩⟩
      simp only [chunkA, rows5, MaxCutJob.incr, List.replicate, List.cons_append,
        List.nil_append]
      repeat' refine pcons ?_ ?_
      all_goals first
        | (refine pnil ?_; simp [renderInstr, regsLE_regs]; omega)
        | (simp [renderInstr, regsLE_regs]; omega)

/-- Second-pass register values: the flag `base` is `0` or `1`, `win` at most `c`, `pw`
at most `d`. -/
def FlagBounded (c d : ℕ) (R : Regs) : Prop :=
  ∃ b i k, R = regs b i k ∧ b ≤ 1 ∧ i ≤ c ∧ k ≤ d

theorem chunkB_bounds (s : Sym) {M c d : ℕ} {R : Regs} (h : FlagBounded c d R)
    (hcM : c + 3 ≤ M) (hdM : d + 9 ≤ M) :
    PrefixLE M R (chunkB s) ∧ FlagBounded (c + 1) (d + 1) (render R (chunkB s)).2 := by
  obtain ⟨b, i, k, rfl, hb, hi, hk⟩ := h
  refine ⟨?_, ?_⟩
  · cases s <;> simp only [chunkB, vertexJob, List.cons_append, List.nil_append] <;>
      repeat' refine pcons ?_ ?_
    all_goals first
      | (refine pnil ?_; simp [renderInstr, regsLE_regs]; omega)
      | (simp [renderInstr, regsLE_regs]; omega)
  · cases s with
    | mark =>
        have := congrArg Prod.snd (render_markB b i k)
        exact ⟨b, i + 1, k + b, by simpa [jobOf] using this, hb, by omega, by omega⟩
    | endClause =>
        have := congrArg Prod.snd (render_endB b i k)
        exact ⟨b, i + 1, k + b, by simpa [jobOf] using this, hb, by omega, by omega⟩
    | pos =>
        have := congrArg Prod.snd (render_signB b i k _ (Or.inl rfl))
        exact ⟨1, i + 1, k + 1, by simpa [jobOf] using this, le_rfl, by omega, by omega⟩
    | neg =>
        have := congrArg Prod.snd (render_signB b i k _ (Or.inr rfl))
        exact ⟨1, i + 1, k + 1, by simpa [jobOf] using this, le_rfl, by omega, by omega⟩

theorem jobB_bounds (L : List Sym) : ∀ {M c d : ℕ} {R : Regs}, FlagBounded c d R →
    c + L.length + 3 ≤ M → d + L.length + 9 ≤ M →
    PrefixLE M R (jobOf chunkB L) ∧
      FlagBounded (c + L.length) (d + L.length) (render R (jobOf chunkB L)).2 := by
  induction L with
  | nil =>
      intro M c d R h hcM hdM
      refine ⟨pnil ?_, by simpa [jobOf, render] using h⟩
      obtain ⟨b, i, k, rfl, hb, hi, hk⟩ := h
      rw [regsLE_regs]
      simp at hcM hdM
      omega
  | cons s L ih =>
      intro M c d R h hcM hdM
      simp only [List.length_cons] at hcM hdM
      obtain ⟨h1, h2⟩ := chunkB_bounds s (M := M) h (by omega) (by omega)
      have hjob : jobOf chunkB (s :: L) = chunkB s ++ jobOf chunkB L := by simp [jobOf]
      obtain ⟨h3, h4⟩ := ih (M := M) h2 (by omega) (by omega)
      refine ⟨by rw [hjob]; exact prefixLE_append h1 h3, ?_⟩
      rw [hjob, MachineTableau.render_append_snd, List.length_cons,
        show c + (L.length + 1) = c + 1 + L.length by ring,
        show d + (L.length + 1) = d + 1 + L.length by ring]
      exact h4

theorem sepA_bounded : BlockBounded sepA := by
  intro M c d R h hc hcM hdM
  obtain ⟨b, i, k, rfl, hb, hi, hk⟩ := h
  refine ⟨?_, ⟨0, 1, k, by simp [sepA, render, renderInstr], by omega, by omega, by omega⟩⟩
  simp only [sepA]
  repeat' refine pcons ?_ ?_
  all_goals first
    | (refine pnil ?_; simp [renderInstr, regsLE_regs]; omega)
    | (simp [renderInstr, regsLE_regs]; omega)

/-- Every register stays at most `20n + 40` while the job runs. -/
theorem prefixLE_job (x : List Sym) :
    PrefixLE (20 * x.length + 40) (regs 0 1 0) (job x) := by
  set n := x.length
  have h0 : Bounded 2 0 (regs 0 1 0) := ⟨0, 1, 0, rfl, by omega, by omega, le_rfl⟩
  obtain ⟨p1, b1⟩ := TwoPassMachine.jobOf_bounds chunkA chunkA_bounded x (M := 20 * n + 40)
    h0 le_rfl (by omega) (by omega)
  obtain ⟨p2, b2⟩ := sepA_bounded (M := 20 * n + 40) b1 (by omega) (by omega) (by omega)
  have b2' : FlagBounded (2 + 3 * n + 3) (0 + 9 * n + 9)
      (render (render (regs 0 1 0) (jobOf chunkA x)).2 sepA).2 := by
    obtain ⟨b, i, k, hR, hb, hi, hk⟩ := b2
    refine ⟨b, i, k, hR, ?_, hi, hk⟩
    have : (render (render (regs 0 1 0) (jobOf chunkA x)).2 sepA).2 .base = 0 := by
      obtain ⟨b', i', k', hR', -⟩ := b1
      rw [hR']
      simp [sepA, render, renderInstr]
    rw [hR] at this
    simp at this
    omega
  obtain ⟨p3, b3⟩ := jobB_bounds x.reverse (M := 20 * n + 40) b2' (by simp; omega)
    (by simp; omega)
  have p4 : PrefixLE (20 * n + 40)
      (render (render (render (regs 0 1 0) (jobOf chunkA x)).2 sepA).2
        (jobOf chunkB x.reverse)).2 suffix := by
    obtain ⟨b, i, k, hR, hb, hi, hk⟩ := b3
    rw [hR]
    exact TableauJobs.prefixLE_of_pure (by simp [suffix, Instr.pure])
      (by rw [regsLE_regs]; simp at hi hk; omega)
  have q1 := prefixLE_append (TableauJobs.prefixLE_of_pure (J := []) (by simp)
    (regsLE_regs.mpr ⟨by omega, by omega, by omega, by omega⟩)) p1
  have q2 := prefixLE_append q1 (by rw [MachineTableau.render_append_snd]; simpa [render] using p2)
  have q3 := prefixLE_append q2
    (by rw [MachineTableau.render_append_snd, MachineTableau.render_append_snd]
        simpa [render] using p3)
  have q4 := prefixLE_append q3
    (by rw [MachineTableau.render_append_snd, MachineTableau.render_append_snd,
      MachineTableau.render_append_snd]
        simpa [render] using p4)
  simpa [job, TwoPassMachine.job, List.append_assoc] using q4

theorem chunkA_ok (s : Sym) : ∀ i ∈ chunkA s, i.ok := by
  cases s <;> simp [chunkA, rows5, MaxCutJob.incr, Instr.ok, List.replicate]

theorem chunkB_ok (s : Sym) : ∀ i ∈ chunkB s, i.ok := by
  cases s <;> simp [chunkB, vertexJob, Instr.ok]

theorem chunkA_length_le (s : Sym) : (chunkA s).length ≤ 40 := by
  cases s <;> simp [chunkA, rows5, MaxCutJob.incr]

theorem chunkB_length_le (s : Sym) : (chunkB s).length ≤ 15 := by
  cases s <;> simp [chunkB, vertexJob]

/-! ### Polynomial time and hardness -/

/-- The Stage 2 map is computed in polynomial time by the two-pass machine. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime MaxCut.unaryEncoding PadicRegressionLanguage.unaryEncoding
      nestedReduce where
  tm := toGenMachine (TwoPassMachine.R [] chunkA sepA chunkB)
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := TwoPassMachine.timePoly
  outputsFun x := by
    obtain ⟨G, K⟩ := x
    have run := TwoPassMachine.outputsInTime [] chunkA sepA chunkB (encode (graphFormula G K))
      (PadicRegressionLanguage.unaryEncoding.encode (nestedReduce (G, K)))
      (TwoPassMachine.job_ok _ _ _ _ (by simp) chunkA_ok (by simp [sepA, Instr.ok]) chunkB_ok _)
      (prefixLE_job _)
      (TwoPassMachine.job_length_le _ _ _ _ (by simp) chunkA_length_le (by simp [sepA])
        chunkB_length_le _) (render_job G K)
    simpa [Equiv.refl, MaxCut.unaryEncoding] using run

/-- The Stage 2 map is a checked polynomial-time reduction from unary Max-Cut to summed
`p`-adic regression, for every prime `p`. -/
noncomputable def stage2Reduction (p : ℕ) [Fact p.Prime] :
    encodedUnaryMaxCut.PolytimeReducesTo (encodedUnaryRegression p) where
  map := nestedReduce
  correct x := maxCut_iff_stage2 x.1 x.2 _
  polytime := ⟨computableInPolyTime⟩

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- Through Stage 2, summed `5`-adic regression is NP-hard. -/
theorem encodedUnaryRegression_five_NPHard_via_stage2 :
    (encodedUnaryRegression 5).NPHard :=
  EncodedLanguage.NPHard.of_reduction (stage2Reduction 5) MaxCutMachine.encodedUnaryMaxCut_NPHard

/-! ### The family statement -/

theorem litsEdges_loopless (b : ℕ) (hb : b % 2 = 1) (c : Clause ℕ) :
    ∀ i, ∀ e ∈ MaxCut.litsEdges b i c, e.1 ≠ e.2 := by
  induction c with
  | nil => intro i e he; simp [MaxCut.litsEdges] at he
  | cons l c ih =>
      intro i e he
      simp only [MaxCut.litsEdges, List.mem_append] at he
      rcases he with he | he
      · cases l <;> simp [MaxCut.litEdges] at he <;> rcases he with rfl | rfl <;> simp <;>
          omega
      · exact ih (i + 1) e he

/-- The Max-Cut gadget graphs are loopless. -/
theorem gadgetEdges_loopless (F : Formula ℕ) : ∀ b, b % 2 = 1 → 3 ≤ b →
    ∀ e ∈ MaxCut.gadgetEdges b F, e.1 ≠ e.2 := by
  induction F with
  | nil => intro b _ _ e he; simp [MaxCut.gadgetEdges] at he; subst he; simp
  | cons c F ih =>
      intro b hb hb3 e he
      simp only [MaxCut.gadgetEdges, List.cons_append, List.mem_cons, List.mem_append] at he
      rcases he with rfl | (he | he) | he
      · simp
      · exact litsEdges_loopless b hb c 0 e he
      · simp [MaxCut.fixedEdges] at he
        rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      · exact ih (b + 18) (by omega) (by omega) e he

theorem edgesOf_bound (G : List Edge) (K : ℕ) :
    ∀ e ∈ edgesOf G K, e.1 < (MaxCut.unaryEncoding.encode (G, K)).length ∧
      e.2 < (MaxCut.unaryEncoding.encode (G, K)).length := by
  have hlen : (MaxCut.unaryEncoding.encode (G, K)).length =
      (G.map fun e => e.1 + e.2 + 3).sum + K + 2 := by
    show (encode (graphFormula G K)).length = _
    rw [MaxCutJob.encode_edges]
    simp only [List.length_append, MaxCutJob.epos, encodeLiteral, List.length_cons,
      List.length_replicate, List.length_nil]
    have : ∀ L : List Edge, (L.flatMap MaxCutJob.edgeSyms).length =
        (L.map fun e => e.1 + e.2 + 3).sum := by
      intro L
      induction L with
      | nil => rfl
      | cons e L ih =>
          simp [List.flatMap_cons, MaxCutJob.edgeSyms, MaxCutJob.epos, encodeLiteral, ih]
          ring_nf
    rw [this]
    ring_nf
  intro e he
  rw [hlen]
  simp only [edgesOf, List.mem_append, List.mem_map, List.mem_singleton] at he
  rcases he with ⟨e', he', rfl⟩ | rfl
  · have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun e : Edge => e.1 + e.2 + 3) he')
    simp only at this ⊢
    omega
  · simp; omega

/-- The reduction from unary CNF-SAT through the library's chain and Max-Cut gadget
reductions and Stage 2. -/
noncomputable def satStage2Reduction :
    CNF.Unary.encodedUnarySAT.PolytimeReducesTo (encodedUnaryRegression 5) :=
  PolytimeManyOneReduction.comp MaxCutMachine.satReduction (stage2Reduction 5)

/-- **Thesis `thm:nested-easy-hard-easy`, Stage 2.** Summed `5`-adic regression is
NP-hard through a polynomial-time reduction all of whose produced datasets are, as
multisets of dense rows, exactly `A'_G` of a loopless graph `G`. -/
theorem satStage2_dataset_eq_A'_G (F : Formula ℕ) :
    let x := MaxCut.gadget (CNF.Chain.chainThree F)
    ((((nestedReduce x).1.map (toDense (MaxCut.unaryEncoding.encode x).length)) : List _) :
      Multiset (NestedEasyHardEasy.Row (MaxCut.unaryEncoding.encode x).length)) =
      NestedEasyHardEasy.A'_G
        (leftOf (edgesOf x.1 x.2) _ (edgesOf_bound x.1 x.2))
        (rightOf (edgesOf x.1 x.2) _ (edgesOf_bound x.1 x.2)) :=
  stage2_rows_eq_A'_G _ _ _
    (gadgetEdges_loopless (CNF.Chain.chainThree F) 3 rfl le_rfl) (edgesOf_bound _ _)

theorem satStage2_NPHard : (encodedUnaryRegression 5).NPHard :=
  EncodedLanguage.NPHard.of_reduction satStage2Reduction CookLevin.encodedUnarySAT_NPHard

end PhdThesisLean.NestedStage2Machine

#print axioms PhdThesisLean.NestedStage2Machine.encodedUnaryRegression_five_NPHard_via_stage2
#print axioms PhdThesisLean.NestedStage2Machine.satStage2_dataset_eq_A'_G
#print axioms PhdThesisLean.NestedStage2Machine.satStage2_NPHard
