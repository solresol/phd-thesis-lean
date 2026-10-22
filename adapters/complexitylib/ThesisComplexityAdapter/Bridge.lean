/- SPDX-License-Identifier: Apache-2.0 -/

module

public import Mathlib.Computability.TuringMachine.Computable
public import Complexity.Computability.Complexity.Reduction.ManyOne
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime

/-!
A narrow interface boundary, not a machine simulation. The stable library's
`LeanNPHardness.FinEncoding.toEncoding` supplies the source interface when its
alphabet is Bool. No stable-library source is imported or copied here.
-/
@[expose] public section

namespace ThesisComplexityAdapter

open Computability

variable {α β : Type}

/-- A left-inverse decoder supplies the injectivity required by Complexitylib. -/
def binaryEmbedding (e : Encoding α Bool) : α ↪ List Bool where
  toFun := e.encode
  inj' := e.encode_injective

@[simp] theorem binaryEmbedding_apply (e : Encoding α Bool) (a : α) :
    binaryEmbedding e a = e.encode a := rfl

/-- The interface conversion preserves the exact input-size measure. -/
@[simp] theorem binaryEmbedding_length (e : Encoding α Bool) (a : α) :
    (binaryEmbedding e a).length = (e.encode a).length := rfl

@[simp] theorem decode_binaryEmbedding (e : Encoding α Bool) (a : α) :
    e.decode (binaryEmbedding e a) = some a := e.decode_encode a

/-- The missing simulation theorem, stated as a proposition rather than assumed globally.
It includes all TM2 programs computing the given typed function in polynomial time.
A proof must construct a finite-state binary multitape machine with polynomial
bounds, cleared work tapes and restored heads, using the exact encodings below. -/
def SimulationObligation (ea : Encoding α Bool) (eb : Encoding β Bool) : Prop :=
  ∀ f : α → β, Turing.TM2ComputableInPolyTime ea.encode eb.encode f →
    Turing.MultiTapeTM.ComputableTidilyInPolyTime f
      (binaryEmbedding ea) (binaryEmbedding eb)

/-- Only conditional transfer of a reduction witness. The simulation argument is
an explicit local hypothesis; this theorem does not discharge it or assert hardness. -/
theorem reduction_of_simulation
    (ea : Encoding α Bool) (eb : Encoding β Bool)
    (simulate : SimulationObligation ea eb)
    (A : Set α) (B : Set β) (f : α → β)
    (hf : Turing.TM2ComputableInPolyTime ea.encode eb.encode f)
    (hmem : ∀ a, a ∈ A ↔ f a ∈ B) :
    Cslib.Complexity.ManyOneReducibleBy
      (fun g => Turing.MultiTapeTM.ComputableTidilyInPolyTime g
        (binaryEmbedding ea) (binaryEmbedding eb)) A B :=
  ⟨f, simulate f hf, hmem⟩

/-- A concrete smoke test on binary words, with no machine claim. -/
def wordEncoding : Encoding (List Bool) Bool where
  encode := id
  decode := some
  decode_encode _ := rfl

example (xs : List Bool) : binaryEmbedding wordEncoding xs = xs := rfl
example (xs : List Bool) : wordEncoding.decode (binaryEmbedding wordEncoding xs) = some xs := rfl

end ThesisComplexityAdapter
