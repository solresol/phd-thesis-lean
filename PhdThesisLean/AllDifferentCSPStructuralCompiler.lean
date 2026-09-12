import PhdThesisLean.AllDifferentCSPBinaryHeader

namespace PhdThesisLean.AllDifferentCSPMachine

open Computability Turing
open PhdThesisLean.AllDifferentCSPEncoding
open LeanNPHardness.MachineComposition

/-!
# Complete structural preprocessing in the original Boolean encoding

Compose the internally computed row tally, binary outer header, raw reversal,
and checked Boolean framing with the existing source and section machines.
This constructs the exact structural view from the actual compiler input.
Canonical symbol relabelling, edge deduplication, objective emission, and
composition with prime selection remain later compiler obligations.
-/

/-- From the complete payload, compute its count and stage the original raw
encoding; both passes run internally in the composed finite machine. -/
noncomputable def structuralRawComputableInPolyTime :
    @TM2ComputableInPolyTime AllDifferentCSPEncoding.RuntimeStructuralView
      AllDifferentCSPEncoding.RuntimeStructuralView RuntimeStructuralView.payloadFinEncoding
      RuntimeStructuralView.rawFinEncoding id := by
  let composed := compositionComputableInPolyTime _ _ _ _ _
    structuralRowCountCheckedComputableInPolyTime structuralBinaryHeaderComputableInPolyTime
  exact { composed with
    outputsFun := fun view => by
      simpa [Function.comp_def] using composed.outputsFun view }

/-- The exact raw structural view is constructed from the actual Boolean
compiler input; neither row count nor variable header is supplied separately. -/
noncomputable def runtimeCompilerStructuralRawComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeSystem AllDifferentCSPEncoding.RuntimeStructuralView
      RuntimeCompilerInput.finEncoding RuntimeStructuralView.rawFinEncoding
      AllDifferentCSPEncoding.RuntimeStructuralView.ofRuntimeSystem := by
  let composed := compositionComputableInPolyTime _ _ _ _ _
    runtimeCompilerStructuralPayloadComputableInPolyTime structuralRawComputableInPolyTime
  exact { composed with
    outputsFun := fun C => by
      simpa [Function.comp_def] using composed.outputsFun C }

/-- Complete structural preprocessing from Boolean compiler input to the
original Boolean structural encoding, with a checked polynomial time bound. -/
noncomputable def runtimeCompilerStructuralViewComputableInPolyTime :
    @TM2ComputableInPolyTime RuntimeSystem AllDifferentCSPEncoding.RuntimeStructuralView
      RuntimeCompilerInput.finEncoding RuntimeStructuralView.finEncoding
      AllDifferentCSPEncoding.RuntimeStructuralView.ofRuntimeSystem := by
  let composed := compositionComputableInPolyTime _ _ _ _ _
    runtimeCompilerStructuralRawComputableInPolyTime runtimeStructuralViewFramingComputableInPolyTime
  exact { composed with
    outputsFun := fun C => by
      simpa [Function.comp_def] using composed.outputsFun C }

#print axioms structuralRawComputableInPolyTime
#print axioms runtimeCompilerStructuralRawComputableInPolyTime
#print axioms runtimeCompilerStructuralViewComputableInPolyTime

end PhdThesisLean.AllDifferentCSPMachine
