import LeanNPHardness.MaxCutSpec
import Mathlib.NumberTheory.Padics.PadicNorm

/-!
# The decision version of summed `p`-adic linear regression as an encoded language

This module states the decision problem of thesis Problem "p-adic linear regression
(decision version)" (`padic-regression-complexity/body.tex`, Section "Problem
definitions") as an `EncodedLanguage` of the `lean-np-hardness` library, so that
NP-hardness can be transferred to it by checked polynomial-time reductions.

## Instances

An instance is a list of data rows and a bound `T : ℕ`. A row is written as a list of
signed unit terms, reusing the library's CNF literal syntax:

* `.positive 0` / `.negative 0` add `+1` / `-1` to the row's target `y`;
* `.positive (v + 1)` / `.negative (v + 1)` add `+1` / `-1` to the coefficient of `β v`.

So every integral row `(x, y)` with finitely many nonzero coordinates is represented
(repeating a term gives larger integers), and `residual β r = x ⬝ β - y`. The instance
is accepted when some `β : ℕ → ℚ` has summed `p`-adic loss at most `T`
(`RegressionLang`). Only finitely many coordinates of `β` occur in an instance, so this
is the thesis's quantification over `β ∈ ℚ^n`.

## Encodings

`instanceFormula rows T` writes an instance as a CNF formula: the rows followed by the
single clause `[.positive T]`, exactly as the library writes Max-Cut instances
(`MaxCut.graphFormula`). Both library encodings of formulas then give encodings of
instances: `unaryEncoding` (unary variable indices, so integer magnitudes are also
unary) and `binaryEncoding` (framed binary). `encodedUnaryRegression p` and
`encodedRegression p` are the corresponding encoded languages.

## Correspondence notes

* The thesis's bound `B` ranges over `ℚ`; here it is a natural number. Natural bounds
  are a special case, so NP-hardness for this language is the stronger statement for
  the integral-bound restriction and transfers to rational bounds by the evident
  re-encoding.
* The data are integral, which is the restriction used by every hardness reduction of
  the chapter.
-/

namespace PhdThesisLean.PadicRegressionLanguage

open LeanNPHardness LeanNPHardness.CNF

/-- A data row, written as signed unit terms (see the module documentation). -/
abbrev Row := Clause ℕ

/-- The contribution of one signed unit term to the residual `x ⬝ β - y`. -/
def term (β : ℕ → ℚ) : Literal ℕ → ℚ
  | .positive 0 => -1
  | .negative 0 => 1
  | .positive (v + 1) => β v
  | .negative (v + 1) => -β v

/-- The residual `x ⬝ β - y` of a row. -/
def residual (β : ℕ → ℚ) (r : Row) : ℚ := (r.map (term β)).sum

/-- The summed `p`-adic loss of a list of rows. -/
def loss (p : ℕ) (β : ℕ → ℚ) (rows : List Row) : ℚ :=
  (rows.map fun r => padicNorm p (residual β r)).sum

/-- The decision problem: some `β` has summed `p`-adic loss at most the bound. -/
def RegressionLang (p : ℕ) : Language (List Row × ℕ) :=
  fun x => ∃ β : ℕ → ℚ, loss p β x.1 ≤ x.2

theorem loss_nil (p : ℕ) (β : ℕ → ℚ) : loss p β [] = 0 := rfl

theorem loss_cons (p : ℕ) (β : ℕ → ℚ) (r : Row) (rows : List Row) :
    loss p β (r :: rows) = padicNorm p (residual β r) + loss p β rows := by
  simp [loss]

theorem loss_append (p : ℕ) (β : ℕ → ℚ) (A B : List Row) :
    loss p β (A ++ B) = loss p β A + loss p β B := by
  simp [loss, List.map_append, List.sum_append]

theorem loss_flatMap {α : Type} (p : ℕ) (β : ℕ → ℚ) (f : α → List Row) (L : List α) :
    loss p β (L.flatMap f) = (L.map fun a => loss p β (f a)).sum := by
  induction L with
  | nil => rfl
  | cons a L ih => rw [List.flatMap_cons, loss_append, ih, List.map_cons, List.sum_cons]

theorem loss_replicate (p : ℕ) (β : ℕ → ℚ) (n : ℕ) (r : Row) :
    loss p β (List.replicate n r) = n * padicNorm p (residual β r) := by
  induction n with
  | zero => simp [loss_nil]
  | succ n ih =>
      rw [List.replicate_succ, loss_cons, ih]
      push_cast
      ring

/-! ### Encodings -/

/-- An instance as a formula: the rows, then the bound as the clause `[T]`. -/
def instanceFormula (rows : List Row) (T : ℕ) : Formula ℕ := rows ++ [[.positive T]]

/-- Recover an instance from its formula. -/
def decodeInstance (F : Formula ℕ) : Option (List Row × ℕ) :=
  match F.getLast? with
  | some [.positive T] => some (F.dropLast, T)
  | _ => none

theorem decodeInstance_instanceFormula (rows : List Row) (T : ℕ) :
    decodeInstance (instanceFormula rows T) = some (rows, T) := by
  simp [decodeInstance, instanceFormula]

/-- Regression instances under the unary-index CNF encoding. -/
def unaryEncoding : Computability.FinEncoding (List Row × ℕ) where
  Γ := CNF.Unary.Sym
  encode x := CNF.Unary.encode (instanceFormula x.1 x.2)
  decode syms := (CNF.Unary.decode syms).bind decodeInstance
  decode_encode x := by simp [CNF.Unary.decode_encode, decodeInstance_instanceFormula]
  ΓFin := inferInstance

/-- Regression instances under the binary CNF encoding. -/
def binaryEncoding : Computability.FinEncoding (List Row × ℕ) where
  Γ := Bool
  encode x := Formula.encode (instanceFormula x.1 x.2)
  decode bits := (Formula.decode bits).bind decodeInstance
  decode_encode x := by simp [decodeInstance_instanceFormula]
  ΓFin := inferInstance

/-- Summed `p`-adic regression with the unary-index encoding. -/
def encodedUnaryRegression (p : ℕ) : EncodedLanguage (List Row × ℕ) where
  encoding := unaryEncoding
  accepts := RegressionLang p

/-- Summed `p`-adic regression with the binary encoding. -/
def encodedRegression (p : ℕ) : EncodedLanguage (List Row × ℕ) where
  encoding := binaryEncoding
  accepts := RegressionLang p

end PhdThesisLean.PadicRegressionLanguage
