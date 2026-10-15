import PhdThesisLean.FixedPrimeMaxCutReduction
import LeanNPHardness.MaxCutJob
import LeanNPHardness.TableauRegisterBounds

/-!
# The fixed-prime Max-Cut rows as an interpreter job

The machine of `FixedPrimeMaxCutMachine.lean` streams the unary encoding of a Max-Cut
instance through the library's job interpreter (`LeanNPHardness.TableauJobs`). This
module defines the per-symbol instruction chunks and proves what the job renders.

Registers: `win` counts the marks of the number being read, offset by `2` so that
vertex `x` has literal index `x + 2`; `base` holds the previous number of the clause;
`w` is the constant `1`; `pw` accumulates the bound.

* A sign symbol moves `win` to `base` and restarts `win` at `2`.
* A mark increments `win`.
* A clause end emits `edgeBlock base win` (the five edge rows and five zero rows), adds
  `3` to `pw`, moves `win` to `base`, and restarts `win` at `1`, the index of the fresh
  vertex `z`.

An edge clause `u, v` therefore emits `edgeBlock (u + 2) (v + 2)`. The final threshold
clause `K` has a single number, so `base` is still `1` at its end and it emits
`edgeBlock 1 (K + 2)`: the pendant edge of `FixedPrimeMaxCutReduction.reduceRows`. After
the job, `base` holds `K + 2` and `pw` holds `3|E| + 4` (`render_job`); the machine
emits the constant rows and the bound from these two registers.

`prefixLE_job` bounds every register by `3n + 10` throughout, for input length `n`, as
the interpreter's runtime bound requires.
-/

namespace PhdThesisLean.FixedPrimeMaxCutJob

open LeanNPHardness LeanNPHardness.CNF LeanNPHardness.CNF.Unary LeanNPHardness.TableauJobs
open LeanNPHardness.MaxCut LeanNPHardness.MaxCutJob
open PhdThesisLean.PadicRegressionLanguage PhdThesisLean.FixedPrimeMaxCutReduction

/-! ### The job -/

/-- The rows of the edge between the literal indices held by `base` and `win`, followed
by five zero rows. -/
def rowsJob : List Instr :=
  [.lit true, .reg .base, .endClause,
    .lit true, .reg .base, .lit true, .endClause,
    .lit true, .reg .win, .endClause,
    .lit true, .reg .win, .lit true, .endClause,
    .lit true, .reg .base, .lit true, .reg .win, .lit true, .endClause,
    .endClause, .endClause, .endClause, .endClause, .endClause]

/-- Move `win` to `base` and empty `win`. -/
def shift : List Instr := [.clear .base, .addTo .base .win, .clear .win]

/-- The chunk of one input symbol. -/
def chunk : Sym → List Instr
  | .mark => [.addTo .win .w]
  | .pos => shift ++ incr .win 2
  | .neg => []
  | .endClause => rowsJob ++ incr .pw 3 ++ shift ++ incr .win 1

/-- The job of an input symbol list. -/
def job (L : List Sym) : List Instr := (L.map chunk).flatten

theorem job_append (L M : List Sym) : job (L ++ M) = job L ++ job M := by simp [job]

/-- Registers with given values and `w = 1`. -/
def regs (b i k : ℕ) : Regs
  | .base => b
  | .win => i
  | .w => 1
  | .pw => k

/-- Registers at the start of the job. -/
def initRegs : Regs := regs 0 1 1

@[simp] theorem regs_base (b i k : ℕ) : regs b i k .base = b := rfl
@[simp] theorem regs_win (b i k : ℕ) : regs b i k .win = i := rfl
@[simp] theorem regs_w (b i k : ℕ) : regs b i k .w = 1 := rfl
@[simp] theorem regs_pw (b i k : ℕ) : regs b i k .pw = k := rfl

@[simp] theorem update_base (b i k x : ℕ) : Function.update (regs b i k) .base x = regs x i k := by
  funext r; cases r <;> simp [regs]

@[simp] theorem update_win (b i k x : ℕ) : Function.update (regs b i k) .win x = regs b x k := by
  funext r; cases r <;> simp [regs]

@[simp] theorem update_pw (b i k x : ℕ) : Function.update (regs b i k) .pw x = regs b i x := by
  funext r; cases r <;> simp [regs]

/-! ### Rendering -/

theorem render_rowsJob (b i k : ℕ) :
    render (regs b i k) rowsJob = (encode (edgeBlock b i), regs b i k) := by
  simp [rowsJob, render, renderInstr, edgeBlock, edgeRows, zeros, encode, encodeClause,
    encodeLiteral]

theorem render_incr_regs (b i k : ℕ) (r : RegName) (hr : r ≠ .w) (n : ℕ) :
    render (regs b i k) (incr r n) =
      ([], Function.update (regs b i k) r (regs b i k r + n)) := by
  rw [render_incr _ r hr n, regs_w, Nat.mul_one]

theorem render_shift (b i k : ℕ) : render (regs b i k) shift = ([], regs i 0 k) := by
  simp [shift, render, renderInstr]

theorem render_shift_incr (b i k n : ℕ) :
    render (regs b i k) (shift ++ incr .win n) = ([], regs i n k) := by
  rw [render_append, render_shift]
  simp only
  rw [render_incr_regs _ _ _ _ (by decide)]
  simp

theorem render_pos (b i k : ℕ) : render (regs b i k) (job [.pos]) = ([], regs i 2 k) := by
  simpa [job, chunk] using render_shift_incr b i k 2

theorem render_end (b i k : ℕ) :
    render (regs b i k) (job [.endClause]) = (encode (edgeBlock b i), regs i 1 (k + 3)) := by
  have hj : job [.endClause] = rowsJob ++ (incr .pw 3 ++ (shift ++ incr .win 1)) := by
    simp [job, chunk]
  rw [hj, render_append, render_rowsJob]
  simp only
  rw [render_append, render_incr_regs _ _ _ _ (by decide)]
  simp only [regs_pw, update_pw]
  rw [render_shift_incr]
  simp

theorem render_marks (b i k u : ℕ) :
    render (regs b i k) (job (List.replicate u .mark)) = ([], regs b (i + u) k) := by
  induction u generalizing i with
  | zero => simp [job, render]
  | succ u ih =>
      rw [List.replicate_succ, show Sym.mark :: List.replicate u Sym.mark =
        [Sym.mark] ++ List.replicate u Sym.mark from rfl, job_append, render_append]
      have h1 : render (regs b i k) (job [.mark]) = ([], regs b (i + 1) k) := by
        simp [job, chunk, render, renderInstr]
      rw [h1]
      simp only [List.nil_append]
      rw [ih]
      ring_nf

theorem render_epos (b i k u : ℕ) :
    render (regs b i k) (job (epos u)) = ([], regs i (u + 2) k) := by
  rw [epos, encodeLiteral, show Sym.pos :: List.replicate u Sym.mark =
    [Sym.pos] ++ List.replicate u Sym.mark from rfl, job_append, render_append, render_pos]
  simp only [List.nil_append]
  rw [render_marks]
  ring_nf

theorem render_edge (b k : ℕ) (e : Edge) :
    render (regs b 1 k) (job (edgeSyms e)) =
      (encode (edgeBlock (e.1 + 2) (e.2 + 2)), regs (e.2 + 2) 1 (k + 3)) := by
  rw [edgeSyms, job_append, job_append, render_append, render_append, render_epos]
  simp only [List.nil_append]
  rw [render_epos, render_end]
  simp

theorem render_edges (G : List Edge) : ∀ b k, ∃ b',
    render (regs b 1 k) (job (G.flatMap edgeSyms)) =
      (encode (G.flatMap fun e => edgeBlock (e.1 + 2) (e.2 + 2)),
        regs b' 1 (k + 3 * G.length)) := by
  induction G with
  | nil => intro b k; exact ⟨b, by simp [job, render, encode]⟩
  | cons e G ih =>
      intro b k
      obtain ⟨b', hb'⟩ := ih (e.2 + 2) (k + 3)
      refine ⟨b', ?_⟩
      rw [List.flatMap_cons, job_append, render_append, render_edge]
      simp only
      rw [hb']
      refine Prod.ext ?_ ?_
      · simp [encode_append]
      · simp only [List.length_cons]
        congr 1
        ring

/-- The job renders the rows of every edge and the pendant edge; afterwards `base`
holds `K + 2` and `pw` holds `3|E| + 4`. -/
theorem render_job (G : List Edge) (K : ℕ) :
    render initRegs (job (encode (graphFormula G K))) =
      (encode (G.flatMap (fun e => edgeBlock (e.1 + 2) (e.2 + 2)) ++ edgeBlock 1 (K + 2)),
        regs (K + 2) 1 (3 * G.length + 4)) := by
  obtain ⟨b', hb'⟩ := render_edges G 0 1
  rw [encode_edges, List.append_assoc, job_append, job_append, render_append, initRegs, hb']
  simp only
  rw [render_append, render_epos]
  simp only [List.nil_append]
  rw [render_end]
  refine Prod.ext ?_ ?_
  · simp [encode_append]
  · simp only
    congr 1
    ring

/-! ### Register bounds -/

theorem regsLE_regs {M b i k : ℕ} : RegsLE M (regs b i k) ↔ b ≤ M ∧ i ≤ M ∧ 1 ≤ M ∧ k ≤ M := by
  constructor
  · intro h
    exact ⟨h .base, h .win, h .w, h .pw⟩
  · rintro ⟨hb, hi, hw, hk⟩ r
    cases r <;> simpa

theorem prefixLE_cons {M : ℕ} {R : Regs} {i : Instr} {J : List Instr} (hR : RegsLE M R)
    (hJ : PrefixLE M (renderInstr R i).2 J) : PrefixLE M R (i :: J) := by
  intro k hk
  cases k with
  | zero => simpa [render] using hR
  | succ k =>
      simp only [List.take_succ_cons, render]
      exact hJ k (by simpa using hk)

theorem prefixLE_nil {M : ℕ} {R : Regs} (hR : RegsLE M R) : PrefixLE M R [] := by
  intro k hk
  simp at hk
  subst hk
  simpa [render] using hR

/-- Register values at a chunk boundary: `base` and `win` at most `c`, `pw` at most
`d`. -/
def Bounded (c d : ℕ) (R : Regs) : Prop :=
  ∃ b i k, R = regs b i k ∧ b ≤ c ∧ i ≤ c ∧ k ≤ d

/-- One chunk keeps every register at most `M`, and moves the boundary bounds from
`(c, d)` to `(c + 1, d + 3)`. -/
theorem chunk_bounds (s : Sym) {M c d : ℕ} {R : Regs} (h : Bounded c d R) (hc : 2 ≤ c)
    (hcM : c + 1 ≤ M) (hdM : d + 3 ≤ M) :
    PrefixLE M R (chunk s) ∧ Bounded (c + 1) (d + 3) (render R (chunk s)).2 := by
  obtain ⟨b, i, k, rfl, hb, hi, hk⟩ := h
  cases s with
  | mark =>
      refine ⟨?_, ?_⟩
      · refine prefixLE_cons ?_ (prefixLE_nil ?_) <;>
          simp only [renderInstr, regs_win, regs_w, update_win, regsLE_regs] <;> omega
      · exact ⟨b, i + 1, k, by simp [chunk, render, renderInstr], by omega, by omega, by omega⟩
  | neg =>
      refine ⟨prefixLE_nil ?_, ⟨b, i, k, by simp [chunk, render], by omega, by omega, by omega⟩⟩
      rw [regsLE_regs]; omega
  | pos =>
      refine ⟨?_, ⟨i, 2, k, ?_, by omega, by omega, by omega⟩⟩
      · simp only [chunk, shift, incr, List.replicate, List.cons_append, List.nil_append]
        repeat' refine prefixLE_cons ?_ ?_
        all_goals first
          | (refine prefixLE_nil ?_; simp [renderInstr, regsLE_regs]; omega)
          | (simp [renderInstr, regsLE_regs]; omega)
      · simpa [job, chunk] using congrArg Prod.snd (render_shift_incr b i k 2)
  | endClause =>
      refine ⟨?_, ⟨i, 1, k + 3, ?_, by omega, by omega, by omega⟩⟩
      · simp only [chunk, rowsJob, shift, incr, List.replicate, List.cons_append,
          List.nil_append]
        repeat' refine prefixLE_cons ?_ ?_
        all_goals first
          | (refine prefixLE_nil ?_; simp [renderInstr, regsLE_regs]; omega)
          | (simp [renderInstr, regsLE_regs]; omega)
      · simpa [job] using congrArg Prod.snd (render_end b i k)

theorem job_bounds (L : List Sym) : ∀ {M c d : ℕ} {R : Regs}, Bounded c d R → 2 ≤ c →
    c + L.length ≤ M → d + 3 * L.length ≤ M →
    PrefixLE M R (job L) ∧ Bounded (c + L.length) (d + 3 * L.length) (render R (job L)).2 := by
  induction L with
  | nil =>
      intro M c d R h hc hcM hdM
      refine ⟨prefixLE_nil ?_, by simpa [job, render] using h⟩
      obtain ⟨b, i, k, rfl, hb, hi, hk⟩ := h
      rw [regsLE_regs]
      simp at hcM hdM
      omega
  | cons s L ih =>
      intro M c d R h hc hcM hdM
      simp only [List.length_cons] at hcM hdM
      obtain ⟨h1, h2⟩ := chunk_bounds s (M := M) h hc (by omega) (by omega)
      have hjob : job (s :: L) = chunk s ++ job L := by simp [job]
      obtain ⟨h3, h4⟩ := ih (M := M) h2 (by omega) (by omega) (by omega)
      refine ⟨by rw [hjob]; exact prefixLE_append h1 h3, ?_⟩
      rw [hjob, MachineTableau.render_append_snd, List.length_cons,
        show c + (L.length + 1) = c + 1 + L.length by ring,
        show d + 3 * (L.length + 1) = d + 3 + 3 * L.length by ring]
      exact h4

/-- Every register stays at most `3n + 10` while the job of an input of length `n`
runs. -/
theorem prefixLE_job (L : List Sym) : PrefixLE (3 * L.length + 10) initRegs (job L) :=
  (job_bounds L (c := 2) (d := 1) ⟨0, 1, 1, rfl, by omega, by omega, le_rfl⟩ le_rfl
    (by omega) (by omega)).1

theorem chunk_length_le (s : Sym) : (chunk s).length ≤ 40 := by
  cases s <;> simp [chunk, rowsJob, shift, incr]

theorem job_length_le (L : List Sym) : (job L).length ≤ 40 * L.length := by
  induction L with
  | nil => simp [job]
  | cons s L ih =>
      have := chunk_length_le s
      simp only [job, List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
        at ih ⊢
      omega

theorem chunk_ok (s : Sym) : ∀ i ∈ chunk s, i.ok := by
  cases s <;> simp [chunk, rowsJob, shift, incr, Instr.ok, List.replicate]

theorem job_ok (L : List Sym) : ∀ i ∈ job L, i.ok := by
  intro i hi
  simp only [job, List.mem_flatten, List.mem_map] at hi
  obtain ⟨_, ⟨s, _, rfl⟩, h⟩ := hi
  exact chunk_ok s i h

end PhdThesisLean.FixedPrimeMaxCutJob
