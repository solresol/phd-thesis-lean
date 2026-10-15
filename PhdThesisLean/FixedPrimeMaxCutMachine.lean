import PhdThesisLean.FixedPrimeMaxCutJob
import LeanNPHardness.MaxCutMachine

/-!
# Summed `p`-adic regression is NP-hard for every fixed prime

This module completes the complexity transfer for thesis Theorem
`thm:fixed-prime-hardness` (`padic-regression-complexity/body.tex`) and, at `p = 2`,
for the published Theorem `thm:main`.

The machine `fmcR` reads the unary encoding of a Max-Cut instance `(G, K)`, streams the
job of `FixedPrimeMaxCutJob` through the library's input loop and interpreter, and then
runs two short loops on the interpreter's registers: `constLoop` emits one constant row
per mark of `base` (which holds `K + 2`), and `boundEmit` emits the bound clause from
`pw` (which holds `3|E| + 4`). `fmcR_exits` is the exact run from the input alone to
the unary encoding of `FixedPrimeMaxCutReduction.reduce (G, K)` alone, and `cost_le`
bounds its length by `10⁶ (n + 1)²` for input length `n`.

Together with `FixedPrimeMaxCutReduction.maxCut_iff_regression` this gives a checked
polynomial-time many-one reduction from the library's unary Max-Cut language
(`reduction`). Since that language is NP-hard (`MaxCutMachine.encodedUnaryMaxCut_NPHard`,
from the library's Cook--Levin theorem), so is summed `p`-adic regression for every
prime `p`, under the unary encoding (`encodedUnaryRegression_NPHard`) and, through the
library's unary-to-binary CNF converter, under the binary encoding
(`encodedRegression_NPHard`).

The rows produced include `r + 1` zero rows, where `r` is the number of other rows. They
cost nothing in the homogeneous model and pin the intercept in the affine model
(`FixedPrimeMaxCutReduction.maxCut_iff_affine`), so the same machine also proves thesis
`cor:affine-hardness` (`encodedUnaryAffineRegression_NPHard`,
`encodedAffineRegression_NPHard`).
-/

namespace PhdThesisLean.FixedPrimeMaxCutMachine

open Turing hiding TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime
open Computability hiding FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat
open Polynomial StateTransition
open LeanNPHardness (FinEncoding finEncodingNatBool finEncodingBoolBool unaryFinEncodingNat TM2ComputableInPolyTime TM2Computable TM2ComputableInTime idComputableInPolyTime)
open LeanNPHardness LeanNPHardness.CNF LeanNPHardness.CNF.Unary LeanNPHardness.TableauJobs
open LeanNPHardness.TableauStacks LeanNPHardness.Routines LeanNPHardness.MachinePrimitives
open LeanNPHardness.MaxCut
open PhdThesisLean.PadicRegressionLanguage PhdThesisLean.FixedPrimeMaxCutReduction
open PhdThesisLean.FixedPrimeMaxCutJob

/-! ### The routine -/

/-- The register stacks drained at the end. -/
def regStacks : List GStack :=
  [.work (.reg .base), .work (.reg .win), .work (.reg .w), .work (.reg .pw)]

/-- One constant row `(0, 1)` and one zero row per mark of `base`. -/
def constLoop : GRoutine Sym :=
  loop (.work (.reg .base))
    (seq (popOne (.work (.reg .base))) (pushList (.work .buf) [.endClause, .endClause, .pos]))

/-- A final zero row and the bound clause `[pw]`. -/
def boundEmit : GRoutine Sym :=
  seq (pushList (.work .buf) [.pos, .endClause])
    (seq (copyWork (.reg .pw) .buf .scratch) (pushList (.work .buf) [.endClause]))

/-- The reduction routine. -/
def fmcR : GRoutine Sym :=
  seq (loopInput FixedPrimeMaxCutJob.chunk) <| seq (moveAll .skel .job id .mark) <|
  seq (pushList (.work (.reg .win)) [.mark]) <| seq (pushList (.work (.reg .w)) [.mark]) <|
  seq (pushList (.work (.reg .pw)) [.mark]) <| seq interpret <| seq constLoop <|
  seq boundEmit <|
  seq (drainAll regStacks) (moveAll (.work .buf) (.work .output) id .mark)

/-- The empty generator stacks. -/
def E : Stacks (GAlphabet Sym) := emitStacks [] [] 0 0 0 0 0 0 0 0 0 0 []

/-- Pointwise comparison over the generator's stacks. -/
macro "gext" : tactic =>
  `(tactic| (funext k; rcases k with _ | _ | _ | _ | _ | (_ | _ | _ | r | c) <;>
    (try rcases r with _ | _ | _ | _) <;>
    (try rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) <;>
    simp [E, emitStacks, interpStacks, outputStacks, regStacks, Function.update_apply, marks]))

/-! ### The two register loops -/

/-- The symbols of `n` constant blocks, reversed. -/
def constSyms (n : ℕ) : List Sym :=
  (List.replicate n [Sym.endClause, Sym.endClause, Sym.pos]).flatten

theorem constLoop_exits (J : List Instr) (B : List Sym) (R : Regs) :
    constLoop.Exits (interpStacks E J B R) (3 * R .base + 1)
      (interpStacks E J (constSyms (R .base) ++ B) (Function.update R .base 0)) := by
  set n := R .base with hn
  have key := loop_exits (Γ := GAlphabet Sym) (.work (.reg .base))
    (seq (popOne (.work (.reg .base))) (pushList (.work .buf) [.endClause, .endClause, .pos])) n
    (fun i => interpStacks E J (constSyms i ++ B) (Function.update R .base (n - i)))
    (fun _ => 2) ?_ ?_ ?_
  · have hsteps : loopSteps (fun _ => 2) n = 3 * n + 1 := by
      rw [loopSteps_eq_sum]; simp; omega
    rw [hsteps] at key
    have h0 : interpStacks E J (constSyms 0 ++ B) (Function.update R .base (n - 0)) =
        interpStacks E J B R := by
      rw [show constSyms 0 = [] from rfl, List.nil_append, Nat.sub_zero, hn,
        Function.update_eq_self]
    rw [h0, Nat.sub_self] at key
    exact key
  · intro i hi
    have s1 := popOne_exits (Γ := GAlphabet Sym) (.work (.reg .base))
      (interpStacks E J (constSyms i ++ B) (Function.update R .base (n - i)))
    have h1 : (interpStacks E J (constSyms i ++ B) (Function.update R .base (n - i))
        (.work (.reg .base))).tail = marks (n - (i + 1)) := by
      simp only [interpStacks_reg, Function.update_self, marks, List.tail_replicate, Nat.sub_sub]
    rw [h1, interpStacks_update_reg, Function.update_idem] at s1
    have s2 := pushList_exits (Γ := GAlphabet Sym) (.work .buf) [.endClause, .endClause, .pos]
      (interpStacks E J (constSyms i ++ B) (Function.update R .base (n - (i + 1))))
    rw [interpStacks_buf, interpStacks_update_buf] at s2
    have hc : [Sym.endClause, Sym.endClause, Sym.pos] ++ (constSyms i ++ B) =
        constSyms (i + 1) ++ B := by
      simp [constSyms, List.replicate_succ]
    rw [hc] at s2
    exact seq_exits _ _ s1 s2
  · intro i hi
    simp [marks, Function.update_self]
    omega
  · simp [marks]

theorem boundEmit_exits (J : List Instr) (B : List Sym) (R : Regs) :
    boundEmit.Exits (interpStacks E J B R) (4 * R .pw + 4)
      (interpStacks E J ((.endClause :: marks (R .pw)) ++ (.pos :: .endClause :: B)) R) := by
  have s1 := pushList_exits (Γ := GAlphabet Sym) (.work .buf) [.pos, .endClause]
    (interpStacks E J B R)
  rw [interpStacks_buf, interpStacks_update_buf] at s1
  have s2 := copyWork_exits (Γx := Sym) (.reg .pw) .buf .scratch (by decide) (by decide)
    (by decide) (interpStacks E J ([.pos, .endClause] ++ B) R) (by simp [E, emitStacks])
  rw [interpStacks_reg, interpStacks_buf, interpStacks_update_buf, marks_length] at s2
  have s3 := pushList_exits (Γ := GAlphabet Sym) (.work .buf) [.endClause]
    (interpStacks E J (marks (R .pw) ++ ([.pos, .endClause] ++ B)) R)
  rw [interpStacks_buf, interpStacks_update_buf] at s3
  have := seq_exits _ _ s1 (seq_exits _ _ s2 s3)
  rw [show 1 + (4 * R .pw + 2 + 1) = 4 * R .pw + 4 by ring] at this
  simpa using! this

theorem push_reg (J : List Instr) (B : List Sym) (R : Regs) (r : RegName) :
    Function.update (interpStacks E J B R) (.work (.reg r))
      ([.mark] ++ interpStacks E J B R (.work (.reg r))) =
      interpStacks E J B (Function.update R r (R r + 1)) := by
  rw [interpStacks_reg, ← interpStacks_update_reg]
  simp [marks, List.replicate_succ]

/-! ### The run -/

/-- The rows emitted by the job. -/
def jobRows (G : List Edge) (K : ℕ) : List Row :=
  G.flatMap (fun e => edgeBlock (e.1 + 2) (e.2 + 2)) ++ edgeBlock 1 (K + 2)

/-- The bound of the produced instance. -/
def bound (G : List Edge) : ℕ := 3 * G.length + 4

theorem output_eq (G : List Edge) (K : ℕ) :
    ((Sym.endClause :: marks (bound G)) ++ (Sym.pos :: Sym.endClause :: (constSyms (K + 2) ++
      (encode (jobRows G K)).reverse))).reverse =
      PadicRegressionLanguage.unaryEncoding.encode (reduce (G, K)) := by
  have hc : ∀ n, (constSyms n).reverse = encode (List.replicate n constBlock).flatten := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [constSyms, List.replicate_succ, List.flatten_cons, List.reverse_append, ← constSyms,
          ih, List.replicate_succ', List.flatten_append, encode_append]
        simp [constBlock, constRow, zeros, encode, encodeClause, encodeLiteral]
  simp only [PadicRegressionLanguage.unaryEncoding, reduce, reduceRows, instanceFormula,
    List.reverse_cons, List.reverse_append, hc, jobRows, encode_append, List.reverse_reverse]
  simp [encode, encodeClause, encodeLiteral, marks, List.append_assoc, bound, zeros]

/-- Exact steps of the reduction routine. -/
def cost (G : List Edge) (K : ℕ) : ℕ :=
  let x := encode (graphFormula G K)
  (3 * x.length + 1) + ((2 * (FixedPrimeMaxCutJob.job x).length + 1) + (1 + (1 + (1 +
    (interpSteps FixedPrimeMaxCutJob.initRegs (FixedPrimeMaxCutJob.job x) + ((3 * (K + 2) + 1) +
      ((4 * bound G + 4) + (((2 * 0 + 1) + ((2 * 1 + 1) + ((2 * 1 + 1) + ((2 * bound G + 1) + 1))))
        + (2 * (PadicRegressionLanguage.unaryEncoding.encode (reduce (G, K))).length + 1)))))))))

theorem fmcR_exits (G : List Edge) (K : ℕ) :
    fmcR.Exits (paramStacks (encode (graphFormula G K)) [] 0 0 0 0 0 0 0 0) (cost G K)
      (outputStacks (PadicRegressionLanguage.unaryEncoding.encode (reduce (G, K)))) := by
  set x := encode (graphFormula G K) with hx
  rw [paramStacks_eq_emitStacks]
  have s1 := loopInput_exits (Γx := Sym) FixedPrimeMaxCutJob.chunk x [] 0 0 0 0 0 0 0 0 0 0 []
  rw [List.append_nil, show (x.map FixedPrimeMaxCutJob.chunk).flatten =
    FixedPrimeMaxCutJob.job x from rfl] at s1
  set S₁ : Stacks (GAlphabet Sym) := emitStacks [] [] 0 0 0 0 0 0 0 0 0 0
    (FixedPrimeMaxCutJob.job x).reverse with hS₁
  have s2 := moveAll_exits (Γ := GAlphabet Sym) .skel .job (by decide) id .mark S₁
  have hlen2 : (S₁ .skel).length = (FixedPrimeMaxCutJob.job x).length := by
    simp [hS₁, emitStacks]
  set J := FixedPrimeMaxCutJob.job x with hJ
  have h2 : Function.update (Function.update S₁ .skel []) .job
      (((S₁ .skel).map id).reverse ++ S₁ .job) = interpStacks E J [] (fun _ => 0) := by
    rw [hS₁]
    gext
  rw [hlen2, h2] at s2
  have s3 := pushList_exits (Γ := GAlphabet Sym) (.work (.reg .win)) [.mark]
    (interpStacks E J [] (fun _ => 0))
  rw [push_reg] at s3
  rw [show Function.update (fun _ => 0 : Regs) .win (0 + 1) = Function.update (fun _ => 0) .win 1
    from rfl] at s3
  set R₁ : Regs := Function.update (fun _ => 0) .win 1 with hR₁
  have s4 := pushList_exits (Γ := GAlphabet Sym) (.work (.reg .w)) [.mark] (interpStacks E J [] R₁)
  rw [push_reg, show R₁ .w + 1 = 1 by simp [hR₁]] at s4
  set R₂ : Regs := Function.update R₁ .w 1 with hR₂
  have s5 := pushList_exits (Γ := GAlphabet Sym) (.work (.reg .pw)) [.mark] (interpStacks E J [] R₂)
  rw [push_reg] at s5
  have h5 : Function.update R₂ .pw (R₂ .pw + 1) = FixedPrimeMaxCutJob.initRegs := by
    funext r
    cases r <;> simp [hR₂, hR₁, FixedPrimeMaxCutJob.initRegs, FixedPrimeMaxCutJob.regs]
  rw [h5] at s5
  have s6 := interpret_exits E rfl J (job_ok x) [] FixedPrimeMaxCutJob.initRegs
  rw [hJ, hx, render_job, List.append_nil] at s6
  have s7 := constLoop_exits [] (encode (jobRows G K)).reverse
    (FixedPrimeMaxCutJob.regs (K + 2) 1 (bound G))
  simp only [FixedPrimeMaxCutJob.regs_base, FixedPrimeMaxCutJob.update_base] at s7
  have s8 := boundEmit_exits [] (constSyms (K + 2) ++ (encode (jobRows G K)).reverse)
    (FixedPrimeMaxCutJob.regs 0 1 (bound G))
  simp only [FixedPrimeMaxCutJob.regs_pw] at s8
  set S₈ := interpStacks E [] ((Sym.endClause :: marks (bound G)) ++
    (Sym.pos :: Sym.endClause :: (constSyms (K + 2) ++ (encode (jobRows G K)).reverse)))
    (FixedPrimeMaxCutJob.regs 0 1 (bound G)) with hS₈
  have s9 := drainAll_exits regStacks S₈
  have hcost9 : drainAllCost regStacks S₈ =
      (2 * 0 + 1) + ((2 * 1 + 1) + ((2 * 1 + 1) + ((2 * bound G + 1) + 1))) := by
    simp [drainAllCost, regStacks, hS₈, interpStacks, marks, FixedPrimeMaxCutJob.regs]
  rw [hcost9] at s9
  set S₉ : Stacks (GAlphabet Sym) := fun k => if k ∈ regStacks then [] else S₈ k with hS₉
  have s10 := moveAll_exits (Γ := GAlphabet Sym) (.work .buf) (.work .output) (by decide) id
    .mark S₉
  have h10 : Function.update (Function.update S₉ (.work .buf) []) (.work .output)
      (((S₉ (.work .buf)).map id).reverse ++ S₉ (.work .output)) =
      outputStacks (PadicRegressionLanguage.unaryEncoding.encode (reduce (G, K))) := by
    rw [← output_eq, hS₉, hS₈]
    gext
  have hlen10 : (S₉ (.work .buf)).length =
      (PadicRegressionLanguage.unaryEncoding.encode (reduce (G, K))).length := by
    rw [← output_eq, List.length_reverse]
    simp [hS₉, hS₈, regStacks, interpStacks, marks]
  rw [h10, hlen10] at s10
  exact seq_exits _ _ s1 (seq_exits _ _ s2 (seq_exits _ _ s3 (seq_exits _ _ s4
    (seq_exits _ _ s5 (seq_exits _ _ s6 (seq_exits _ _ s7 (seq_exits _ _ s8
      (seq_exits _ _ s9 s10))))))))

/-! ### The time bound -/

theorem input_length_ge (G : List Edge) (K : ℕ) :
    3 * G.length + K + 2 ≤ (encode (graphFormula G K)).length := by
  rw [MaxCutJob.encode_edges]
  have : 3 * G.length ≤ (G.flatMap MaxCutJob.edgeSyms).length := by
    induction G with
    | nil => simp
    | cons e G ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_cons]
        have : 3 ≤ (MaxCutJob.edgeSyms e).length := by
          simp [MaxCutJob.edgeSyms, MaxCutJob.epos, encodeLiteral]
          omega
        omega
  simp only [List.length_append, MaxCutJob.epos, encodeLiteral, List.length_cons,
    List.length_replicate]
  omega

theorem output_length_le (G : List Edge) (K : ℕ) :
    (PadicRegressionLanguage.unaryEncoding.encode (reduce (G, K))).length ≤
      (3 * (encode (graphFormula G K)).length + 10 + 1) *
        (FixedPrimeMaxCutJob.job (encode (graphFormula G K))).length + 3 * (K + 2) +
          (bound G + 3) := by
  rw [← output_eq]
  have h := render_fst_length_le _ _ (prefixLE_job (encode (graphFormula G K)))
  rw [render_job] at h
  simp only at h
  simp [constSyms, marks]
  rw [show (encode (jobRows G K)).length =
    (encode (G.flatMap (fun e => edgeBlock (e.1 + 2) (e.2 + 2)) ++ edgeBlock 1 (K + 2))).length
    from rfl]
  omega

theorem cost_le (G : List Edge) (K : ℕ) :
    cost G K ≤ 1000000 * ((encode (graphFormula G K)).length + 1) ^ 2 := by
  set n := (encode (graphFormula G K)).length with hn
  set L := (FixedPrimeMaxCutJob.job (encode (graphFormula G K))).length with hL
  have hLn : L ≤ 40 * n := job_length_le _
  have hint := interpSteps_le _ _ (prefixLE_job (encode (graphFormula G K)))
  have hout := output_length_le G K
  have hin := input_length_ge G K
  rw [← hn, ← hL] at hint
  rw [← hn, ← hL] at hout
  simp only [cost, bound] at hout ⊢
  rw [← hn, ← hL]
  have hA : (4 * (3 * n + 10) + 4) * L ≤ (12 * n + 44) * (40 * n) :=
    Nat.mul_le_mul (by omega) hLn
  have hB : (3 * n + 10 + 1) * L ≤ (3 * n + 10 + 1) * (40 * n) := Nat.mul_le_mul le_rfl hLn
  nlinarith

/-- The time polynomial of the reduction machine. -/
noncomputable def timePoly : Polynomial ℕ := C 1000000 * (X + 1) ^ 2

/-- The fixed-prime Max-Cut reduction is computed in polynomial time. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime MaxCut.unaryEncoding PadicRegressionLanguage.unaryEncoding reduce where
  tm := toGenMachine fmcR
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePoly
  outputsFun x := by
    obtain ⟨G, K⟩ := x
    have run := evalsToInTimeMono (toGenMachine_outputsInTime _ _ _ _ (fmcR_exits G K))
      (show cost G K ≤ timePoly.eval (encode (graphFormula G K)).length by
        simp only [timePoly, eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one]
        exact cost_le G K)
    simpa [Equiv.refl, MaxCut.unaryEncoding] using! run

/-! ### Hardness -/

/-- The checked polynomial-time reduction from unary Max-Cut to summed `p`-adic
regression under the unary encoding. -/
noncomputable def reduction (p : ℕ) [Fact p.Prime] :
    encodedUnaryMaxCut.PolytimeReducesTo (encodedUnaryRegression p) where
  map := reduce
  correct x := maxCut_iff_regression x
  polytime := ⟨computableInPolyTime⟩

/-- **Thesis `thm:fixed-prime-hardness`, complexity form.** For every prime `p`, the
decision version of summed `p`-adic linear regression with integral data is NP-hard
under the unary-index encoding. -/
theorem encodedUnaryRegression_NPHard (p : ℕ) [Fact p.Prime] :
    (encodedUnaryRegression p).NPHard :=
  EncodedLanguage.NPHard.of_reduction (reduction p) MaxCutMachine.encodedUnaryMaxCut_NPHard

/-- Re-encoding regression instances in binary, in polynomial time. -/
noncomputable def binaryComputable :
    TM2ComputableInPolyTime PadicRegressionLanguage.unaryEncoding
      PadicRegressionLanguage.binaryEncoding id where
  tm := BinaryConvert.machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := BinaryConvert.timePoly
  outputsFun x := by
    have run := toMachine_outputsInTime_le BinaryConvert.conv .input .out
      (encode (instanceFormula x.1 x.2)) (Formula.encode (instanceFormula x.1 x.2)) _
      (by
        have h1 := BinaryConvert.initList_eq (encode (instanceFormula x.1 x.2))
        have h2 := BinaryConvert.haltList_eq (Formula.encode (instanceFormula x.1 x.2))
        simp only [BinaryConvert.machine] at h1 h2
        rw [h1, h2]
        exact BinaryConvert.conv_exits _)
    have run' := evalsToInTimeMono run
      (show BinaryConvert.convBound (encode (instanceFormula x.1 x.2)).length ≤
          BinaryConvert.timePoly.eval (encode (instanceFormula x.1 x.2)).length by
        simp only [BinaryConvert.timePoly, eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one]
        exact BinaryConvert.convBound_le _)
    simpa [Equiv.refl, PadicRegressionLanguage.unaryEncoding,
      PadicRegressionLanguage.binaryEncoding] using! run'

/-- Unary regression reduces to binary regression by re-encoding. -/
noncomputable def binaryReduction (p : ℕ) :
    (encodedUnaryRegression p).PolytimeReducesTo (encodedRegression p) where
  map := id
  correct _ := Iff.rfl
  polytime := ⟨binaryComputable⟩

/-- **Thesis `thm:fixed-prime-hardness`, binary encoding.** For every prime `p`, summed
`p`-adic linear regression is NP-hard under the binary CNF-style encoding. At `p = 2`
this is the published Theorem `thm:main`. -/
theorem encodedRegression_NPHard (p : ℕ) [Fact p.Prime] : (encodedRegression p).NPHard :=
  EncodedLanguage.NPHard.of_reduction (binaryReduction p) (encodedUnaryRegression_NPHard p)

/-! ### The affine model -/

/-- The same machine reduces unary Max-Cut to affine summed `p`-adic regression: the
zero rows it emits pin the intercept. -/
noncomputable def affineReduction (p : ℕ) [Fact p.Prime] :
    encodedUnaryMaxCut.PolytimeReducesTo (encodedUnaryAffineRegression p) where
  map := reduce
  correct x := maxCut_iff_affine x
  polytime := ⟨computableInPolyTime⟩

/-- **Thesis `cor:affine-hardness`, complexity form.** For every prime `p`, affine
summed `p`-adic linear regression with integral data is NP-hard under the unary-index
encoding. -/
theorem encodedUnaryAffineRegression_NPHard (p : ℕ) [Fact p.Prime] :
    (encodedUnaryAffineRegression p).NPHard :=
  EncodedLanguage.NPHard.of_reduction (affineReduction p) MaxCutMachine.encodedUnaryMaxCut_NPHard

/-- Unary affine regression reduces to binary affine regression by re-encoding. -/
noncomputable def binaryAffineReduction (p : ℕ) :
    (encodedUnaryAffineRegression p).PolytimeReducesTo (encodedAffineRegression p) where
  map := id
  correct _ := Iff.rfl
  polytime := ⟨binaryComputable⟩

/-- **Thesis `cor:affine-hardness`, binary encoding.** -/
theorem encodedAffineRegression_NPHard (p : ℕ) [Fact p.Prime] :
    (encodedAffineRegression p).NPHard :=
  EncodedLanguage.NPHard.of_reduction (binaryAffineReduction p)
    (encodedUnaryAffineRegression_NPHard p)

end PhdThesisLean.FixedPrimeMaxCutMachine

#print axioms PhdThesisLean.FixedPrimeMaxCutMachine.encodedUnaryRegression_NPHard
#print axioms PhdThesisLean.FixedPrimeMaxCutMachine.encodedRegression_NPHard
#print axioms PhdThesisLean.FixedPrimeMaxCutMachine.encodedUnaryAffineRegression_NPHard
#print axioms PhdThesisLean.FixedPrimeMaxCutMachine.encodedAffineRegression_NPHard
