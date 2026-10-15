import PhdThesisLean.PadicRegressionLanguage
import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Positive polynomial-residual objectives over `ℤ_p` as an encoded language

This module states the decision problem behind thesis Corollary
`cor:sudoku-polynomial-dyadic-hardness` (`sudoku-via-padic-regression/body.tex`):
minimisation of positive polynomial-residual objectives over `ℤ_p^n`.

## Instances

A residual is a product of affine factors, given as its first factor and the list of
remaining factors (`PolyResidual`). Each factor is a row of signed unit terms as in
`PadicRegressionLanguage` (index `0` the constant, index `v + 1` the coordinate
`x v`). An instance is a list of residuals and a bound `T : ℕ`; it is accepted when some
point `x : ℕ → ℤ_p` has `∑ ‖P(x)‖ ≤ T` (`PolyRegressionLang`). The domain is `ℤ_p`
itself, as in the thesis, because a threshold question over its rational points could
differ.

`MultilinearDeg3 r` holds when `r` has at most three affine factors and different
factors involve disjoint sets of coordinates. A residual of this form is a multilinear
polynomial of total degree at most three. `PolyRegressionLangML` is the problem
restricted to instances all of whose residuals have this form, which is the restriction
named in the corollary.

## Encoding

Each factor is one clause with a marker literal in front: `.positive 0` for the first
factor of a residual and `.positive 1` for every later factor. The bound is the final
clause `[T]`. `parse` regroups the factors from the right. Both library encodings of
formulas then give encodings of instances (`polyUnaryEncoding`, `polyBinaryEncoding`).
-/

namespace PhdThesisLean.PolynomialResidualLanguage

open LeanNPHardness LeanNPHardness.CNF
open PhdThesisLean.PadicRegressionLanguage

/-- A polynomial residual as a product of affine factors: the first factor and the
remaining factors. -/
abbrev PolyResidual := Row × List Row

section Semantics

variable (p : ℕ) [Fact p.Prime]

/-- The contribution of one signed unit term to an affine factor. -/
noncomputable def termZ (x : ℕ → ℤ_[p]) : Literal ℕ → ℤ_[p]
  | .positive 0 => -1
  | .negative 0 => 1
  | .positive (v + 1) => x v
  | .negative (v + 1) => -x v

/-- The value of an affine factor. -/
noncomputable def factorValue (x : ℕ → ℤ_[p]) (r : Row) : ℤ_[p] := (r.map (termZ p x)).sum

/-- The value of a residual: the product of its factors. -/
noncomputable def residualValue (x : ℕ → ℤ_[p]) (r : PolyResidual) : ℤ_[p] :=
  factorValue p x r.1 * (r.2.map (factorValue p x)).prod

/-- The positive polynomial-residual objective `∑ ‖P(x)‖`. -/
noncomputable def polyLoss (x : ℕ → ℤ_[p]) (rs : List PolyResidual) : ℝ :=
  (rs.map fun r => ‖residualValue p x r‖).sum

/-- The decision problem over `ℤ_p`: some point has objective at most the bound. -/
def PolyRegressionLang : Language (List PolyResidual × ℕ) :=
  fun inst => ∃ x : ℕ → ℤ_[p], polyLoss p x inst.1 ≤ inst.2

end Semantics

/-! ### Multilinear residuals of degree at most three -/

/-- The coordinate indices of the variable terms of a factor. -/
def factorVars (r : Row) : List ℕ :=
  r.filterMap fun
    | .positive (v + 1) => some v
    | .negative (v + 1) => some v
    | _ => none

/-- At most three affine factors whose coordinate sets are pairwise disjoint: the product
is then a multilinear polynomial of total degree at most three. -/
def MultilinearDeg3 (r : PolyResidual) : Prop :=
  r.2.length ≤ 2 ∧ (r.1 :: r.2).Pairwise fun f g => ∀ v ∈ factorVars f, v ∉ factorVars g

/-- The problem restricted to multilinear residuals of degree at most three. -/
def PolyRegressionLangML (p : ℕ) [Fact p.Prime] : Language (List PolyResidual × ℕ) :=
  fun inst => (∀ r ∈ inst.1, MultilinearDeg3 r) ∧ PolyRegressionLang p inst

/-! ### Encoding -/

/-- A factor clause, marked as the first factor of its residual or not. -/
def factorClause (first : Bool) (r : Row) : Clause ℕ :=
  .positive (if first then 0 else 1) :: r

/-- The clauses of a residual. -/
def residualClauses (r : PolyResidual) : Formula ℕ :=
  factorClause true r.1 :: r.2.map (factorClause false)

/-- An instance as a formula: the factor clauses, then the bound clause `[T]`. -/
def polyFormula (rs : List PolyResidual) (T : ℕ) : Formula ℕ :=
  rs.flatMap residualClauses ++ [[.positive T]]

/-- Regroup factor clauses into residuals, from the right: the result holds the later
factors still waiting for their first factor, and the completed residuals. -/
def parse : Formula ℕ → Option (List Row × List PolyResidual)
  | [] => some ([], [])
  | c :: rest =>
      match c with
      | .positive 0 :: f => (parse rest).map fun pr => ([], (f, pr.1) :: pr.2)
      | .positive 1 :: f => (parse rest).map fun pr => (f :: pr.1, pr.2)
      | _ => none

/-- Recover an instance from its formula. -/
def decodePoly (F : Formula ℕ) : Option (List PolyResidual × ℕ) :=
  match F.getLast? with
  | some [.positive T] =>
      (parse F.dropLast).bind fun pr => if pr.1 = [] then some (pr.2, T) else none
  | _ => none

theorem parse_later (fs : List Row) (rest : Formula ℕ) :
    parse (fs.map (factorClause false) ++ rest) =
      (parse rest).map fun pr => (fs ++ pr.1, pr.2) := by
  induction fs with
  | nil => simp
  | cons f fs ih =>
      simp only [List.map_cons, List.cons_append, factorClause, Bool.false_eq_true, if_false]
      rw [parse]
      rw [ih, Option.map_map]
      rfl

theorem parse_residuals (rs : List PolyResidual) :
    parse (rs.flatMap residualClauses) = some ([], rs) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      rw [List.flatMap_cons, residualClauses, List.cons_append, factorClause, if_pos rfl,
        parse, parse_later, ih]
      simp

theorem decodePoly_polyFormula (rs : List PolyResidual) (T : ℕ) :
    decodePoly (polyFormula rs T) = some (rs, T) := by
  simp [decodePoly, polyFormula, parse_residuals]

/-- Polynomial-residual instances under the unary-index CNF encoding. -/
def polyUnaryEncoding : Computability.FinEncoding (List PolyResidual × ℕ) where
  Γ := CNF.Unary.Sym
  encode x := CNF.Unary.encode (polyFormula x.1 x.2)
  decode syms := (CNF.Unary.decode syms).bind decodePoly
  decode_encode x := by simp [CNF.Unary.decode_encode, decodePoly_polyFormula]
  ΓFin := inferInstance

/-- Polynomial-residual instances under the binary CNF encoding. -/
def polyBinaryEncoding : Computability.FinEncoding (List PolyResidual × ℕ) where
  Γ := Bool
  encode x := Formula.encode (polyFormula x.1 x.2)
  decode bits := (Formula.decode bits).bind decodePoly
  decode_encode x := by simp [decodePoly_polyFormula]
  ΓFin := inferInstance

/-- The multilinear degree-three problem with the unary-index encoding. -/
def encodedUnaryPolyML (p : ℕ) [Fact p.Prime] : EncodedLanguage (List PolyResidual × ℕ) where
  encoding := polyUnaryEncoding
  accepts := PolyRegressionLangML p

/-- The multilinear degree-three problem with the binary encoding. -/
def encodedPolyML (p : ℕ) [Fact p.Prime] : EncodedLanguage (List PolyResidual × ℕ) where
  encoding := polyBinaryEncoding
  accepts := PolyRegressionLangML p

end PhdThesisLean.PolynomialResidualLanguage
