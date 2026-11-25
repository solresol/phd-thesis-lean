import PhdThesisLean.RationalRecordParser
import PhdThesisLean.RationalRegressionInternal

/-!
# Every accepted original record supplies a compatible arithmetic source

The rectangular grouping is performed on the stored fractions themselves.
Thus acceptance supplies the internal checker's typed column-count contract,
while preserving signs, unreduced fields, repeated rows and all multiplicities.
-/
namespace PhdThesisLean.RationalRecordSource

open LeanNPHardness RationalVerifierBounds
open RationalCertificateBroadcast (Row)
open RationalRegressionInternal (Source)
set_option backward.isDefEq.respectTransparency false

abbrev Input := Source × Fraction
def flat (rs : List Row) : List Fraction := rs.flatMap (fun row => row.1 :: row.2)

theorem exists_rows (r d : ℕ) (xs : List Fraction) (h : xs.length = r*(d+1)) :
    ∃ rs : List Row, rs.length = r ∧ (∀ row ∈ rs, row.2.length = d) ∧ flat rs = xs := by
  induction r generalizing xs with
  | zero =>
      have : xs = [] := by simpa using h
      subst xs
      exact ⟨[],rfl,by simp,rfl⟩
  | succ r ih =>
      cases xs with
      | nil => simp at h
      | cons x xs =>
          have hs : xs.length = d + r*(d+1) := by
            simp only [List.length_cons] at h
            nlinarith
          have hd : d ≤ xs.length := by omega
          obtain ⟨rs,hr,hc,he⟩ := ih (xs.drop d) (by simp [List.length_drop,hs])
          refine ⟨(x,xs.take d)::rs,by simp [hr],?_,?_⟩
          · intro row hrow
            rcases List.mem_cons.mp hrow with rfl | hrow
            · simp [List.length_take,hd]
            · exact hc row hrow
          · change x :: (xs.take d ++ flat rs) = x :: xs
            rw [he,List.take_append_drop]

theorem flat_fractionRows (rs : List Row) :
    RationalRectangularFields.flatFields (RationalRectangularFields.fractionRows rs) =
      (flat rs).map Fraction.encode := by
  simp [RationalRectangularFields.flatFields,RationalRectangularFields.fractionRows,
    flat,List.flatMap_map,List.map_flatMap]

/-- The actual retained parser word, before its final physical reordering. -/
noncomputable def wire (x : Input) : List RationalRecordParser.Cell :=
  RationalRecordValidation.outputEncoding.encode
    (((RationalCertificateBroadcast.listEncoding RationalCertificateBroadcast.rowEncoding).encode
      x.1.val.2).map RationalRectangularFields.rowCell ++ [.dataEnd],
      RationalCertificateTail.resultEncoding.encode (x.1.val.1,x.2))

theorem wire_ne_nil (x : Input) : wire x ≠ [] := by
  simp [wire,RationalRecordValidation.outputEncoding,LeanNPHardness.PairEncoding.finEncoding,
    RationalRectangularFields.outputEncoding,RationalTailAssembly.outputEncoding]

/-- Literal fraction preservation and compatibility for every successful raw
parse, not just words generated from a rational matrix. -/
theorem exists_source (bits : List Bool) (h : RationalRecordValidation.Validated bits) :
    ∃ x : Input, RationalRecordParser.output bits = wire x := by
  obtain ⟨r,d,xs,B,cert,he,hr,hd,hc,hcert⟩ :=
    (RationalRecordValidation.validated_iff bits).1 h
  obtain ⟨rs,hlen,hrows,hflat⟩ := exists_rows r d xs hc
  let src : Source := ⟨(cert,rs),by intro row hm; rw [hrows row hm,hcert]⟩
  refine ⟨(src,B),?_⟩
  rw [RationalRecordParser.output_eq,ite_eq_left h]
  have hg : RationalRecordValidation.prepared bits =
      (((RationalCertificateBroadcast.listEncoding RationalCertificateBroadcast.rowEncoding).encode
        rs).map RationalRectangularFields.rowCell ++ [.dataEnd],d,
        B.encode ++ BinaryNatLists.encodeNat cert.length ++ cert.flatMap Fraction.encode) := by
    simp only [RationalRecordValidation.prepared,he,
      RationalRecordData.output_encode r d xs _ hd hr,RationalRecordRouting.prepare]
    rw [← hflat,← flat_fractionRows]
    have hout := RationalRectangularFields.output_fractionRows r d rs
      (B.encode ++ BinaryNatLists.encodeNat cert.length ++ cert.flatMap Fraction.encode) hlen hrows
    simp only [RationalRectangularFields.wire] at hout
    rw [hout,
      RationalRectangularFields.rowsWire_fractionRows,
      RationalRecordRouting.split_internalRows]
  change RationalRecordValidation.outputEncoding.encode _ = wire (src,B)
  simp only [RationalRecordValidation.output,hg,← hcert,
    RationalCertificateTail.output_encode,RationalCertificateTail.result_encode]
  rfl

theorem exists_source_iff (bits : List Bool) :
    (∃ x : Input, RationalRecordParser.output bits = wire x) ↔
      RationalRecordValidation.Validated bits := by
  constructor
  · rintro ⟨x,hx⟩
    exact (RationalRecordParser.output_success_iff bits).1 (by rw [hx]; exact wire_ne_nil x)
  · exact exists_source bits

theorem output_original {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (β : Fin d → ℚ) (hr : 0 < r) :
    RationalRecordParser.output (RationalWitnessEncoding.encodeInput A y B ++
      RationalWitnessEncoding.encodeRats (List.ofFn β)) =
        wire (RationalRegressionInternal.regressionSource A y β,Fraction.ofRat B) :=
  RationalRecordParser.output_original A y B β hr

#print axioms exists_rows
#print axioms exists_source
#print axioms exists_source_iff
#print axioms output_original

end PhdThesisLean.RationalRecordSource
