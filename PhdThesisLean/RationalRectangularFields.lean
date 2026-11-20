import PhdThesisLean.RationalCountedList
import PhdThesisLean.RationalRegressionInternal

/-!
# Rectangular validation and response/coefficient separation

The counted-field parser has already validated fraction words. This component
checks their rectangular shape against runtime dimensions, preserves the suffix,
and emits the observation rows used by the internal checker. Empty fields reject.
The companion finite machine charges all count restoration, copying and cleanup.
-/
namespace PhdThesisLean.RationalRectangularFields

set_option backward.isDefEq.respectTransparency false
open RationalVerifierBounds

inductive Cell
  | response (b : Bool) | coefficient (b : Bool) | fieldEnd | rowEnd | dataEnd | tail (b : Bool)
  deriving DecidableEq, Fintype, Repr

abbrev Bits := List (Option Bool)
abbrev Result := Option (List Cell)
abbrev Row := List Bool × List (List Bool)

def add (xs : List Cell) (r : Result) : Result := r.map (xs ++ ·)
def tag (response : Bool) : Bool → Cell := if response then Cell.response else Cell.coefficient
def close (response : Bool) : List Cell := if response then [] else [.fieldEnd]

def scan (response : Bool) (next : Bits → Result) : Bits → Result
  | [] => none
  | none :: bs => add (close response) (next bs)
  | some b :: bs => add [tag response b] (scan response next bs)

def field (response : Bool) (next : Bits → Result) : Bits → Result
  | some b :: bs => add [tag response b] (scan response next bs)
  | _ => none

def fields : ℕ → (Bits → Result) → Bits → Result
  | 0, next, bs => next bs
  | n+1, next, bs => field false (fields n next) bs

def tail : Bits → Result
  | [] => some []
  | none :: _ => none
  | some b :: bs => add [.tail b] (tail bs)

def ending : Bits → Result
  | none :: bs => add [.dataEnd] (tail bs)
  | _ => none

def rows : ℕ → ℕ → Bits → Result
  | 0, _, bs => ending bs
  | r+1, d, bs => field true (fields d (fun bs => add [.rowEnd] (rows r d bs))) bs

def render (saved : List Cell) (result : Result) : List Cell :=
  match result with | none => [] | some out => saved.reverse ++ out

def output (r d : ℕ) (bs : Bits) : List Cell := render [] (rows r d bs)

def wire (xs : List (List Bool)) : Bits := RationalCountedFields.wire xs
def rowWire (row : Row) : List Cell :=
  row.1.map Cell.response ++
    row.2.flatMap (fun f => f.map Cell.coefficient ++ [.fieldEnd]) ++ [.rowEnd]
def rowsWire (rs : List Row) : List Cell := rs.flatMap rowWire
def flatFields (rs : List Row) : List (List Bool) := rs.flatMap (fun row => row.1 :: row.2)

@[simp] theorem add_none (xs : List Cell) : add xs none = none := rfl
@[simp] theorem add_some (xs ys : List Cell) : add xs (some ys) = some (xs ++ ys) := rfl
theorem add_assoc (xs ys : List Cell) (r : Result) :
    add xs (add ys r) = add (xs ++ ys) r := by cases r <;> simp [List.append_assoc]
@[simp] theorem render_none (saved : List Cell) : render saved none = [] := rfl
@[simp] theorem render_some (saved out : List Cell) : render saved (some out) = saved.reverse ++ out := rfl

theorem render_add (saved xs : List Cell) (r : Result) :
    render saved (add xs r) = render (xs.reverse ++ saved) r := by
  cases r <;> simp [render, List.reverse_append, List.append_assoc]

theorem scan_wire (response : Bool) (next : Bits → Result) (bs : List Bool) (rest : Bits) :
    scan response next (bs.map some ++ none :: rest) =
      add (bs.map (tag response) ++ close response) (next rest) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [scan, ih, add_assoc]

theorem field_wire (response : Bool) (next : Bits → Result)
    (bs : List Bool) (rest : Bits) (hb : bs ≠ []) :
    field response next (bs.map some ++ none :: rest) =
      add (bs.map (tag response) ++ close response) (next rest) := by
  cases bs with
  | nil => contradiction
  | cons b bs => simp [field, scan_wire, add_assoc]

theorem scan_success_iff (response : Bool) (next : Bits → Result) (bs : Bits) (out : List Cell) :
    scan response next bs = some out ↔ ∃ (word : List Bool) (rest : Bits) (result : List Cell),
      bs = word.map some ++ none :: rest ∧ next rest = some result ∧
        out = word.map (tag response) ++ close response ++ result := by
  induction bs generalizing out with
  | nil => simp [scan]
  | cons b bs ih =>
      cases b with
      | none =>
          constructor
          · intro h
            cases hn : next bs with
            | none => simp [scan, hn] at h
            | some result =>
                simp [scan, hn] at h
                exact ⟨[], bs, result, rfl, hn, h.symm⟩
          · rintro ⟨word, rest, result, he, hn, rfl⟩
            cases word with
            | nil => cases he; simp [scan, hn]
            | cons x xs => simp at he
      | some b =>
          constructor
          · intro h
            cases hs : scan response next bs with
            | none => simp [scan, hs] at h
            | some result =>
                obtain ⟨word, rest, result', he, hn, ho⟩ := (ih result).1 hs
                simp [scan, hs] at h
                exact ⟨b :: word, rest, result', by simp [he], hn, by simp [← h, ho]⟩
          · rintro ⟨word, rest, result, he, hn, rfl⟩
            cases word with
            | nil => simp at he
            | cons x xs =>
                simp only [List.map_cons, List.cons_append, List.cons.injEq,
                  Option.some.injEq] at he
                rcases he with ⟨rfl, rfl⟩
                simp [scan, scan_wire, hn]

theorem field_success_iff (response : Bool) (next : Bits → Result) (bs : Bits) (out : List Cell) :
    field response next bs = some out ↔ ∃ (word : List Bool) (rest : Bits) (result : List Cell),
      word ≠ [] ∧ bs = word.map some ++ none :: rest ∧ next rest = some result ∧
        out = word.map (tag response) ++ close response ++ result := by
  constructor
  · intro h
    cases bs with
    | nil => simp [field] at h
    | cons b bs =>
        cases b with
        | none => simp [field] at h
        | some b =>
            have hs : scan response next (some b :: bs) = some out := h
            obtain ⟨word, rest, result, he, hn, ho⟩ := (scan_success_iff _ _ _ _).1 hs
            refine ⟨word, rest, result, ?_, he, hn, ho⟩
            intro hw; simp [hw] at he
  · rintro ⟨word, rest, result, hw, rfl, hn, rfl⟩
    simp [field_wire response next word rest hw, hn, List.append_assoc]

theorem fields_success_iff (n : ℕ) (next : Bits → Result) (bs : Bits) (out : List Cell) :
    fields n next bs = some out ↔ ∃ (fs : List (List Bool)) (rest : Bits) (result : List Cell),
      fs.length = n ∧ (∀ f ∈ fs, f ≠ []) ∧ bs = wire fs ++ rest ∧
        next rest = some result ∧
        out = fs.flatMap (fun f => f.map Cell.coefficient ++ [.fieldEnd]) ++ result := by
  induction n generalizing bs out with
  | zero =>
      constructor
      · intro h; exact ⟨[], bs, out, rfl, by simp, rfl, h, rfl⟩
      · rintro ⟨fs, rest, result, hn, _, rfl, h, rfl⟩
        have : fs = [] := by simpa using hn
        simpa [this, fields, wire, RationalCountedFields.wire] using h
  | succ n ih =>
      rw [fields, field_success_iff]
      constructor
      · rintro ⟨f, rest, result, hf, rfl, h, rfl⟩
        obtain ⟨fs, rest', result', hn, hfs, rfl, hnext, rfl⟩ := (ih _ _).1 h
        refine ⟨f :: fs, rest', result', by simp [hn], by simp_all, ?_, hnext, ?_⟩
        · simp [wire, RationalCountedFields.wire, List.append_assoc]
        · simp [tag, close, List.append_assoc]
      · rintro ⟨fs, rest, result, hn, hfs, rfl, hnext, rfl⟩
        cases fs with
        | nil => simp at hn
        | cons f fs =>
            refine ⟨f, wire fs ++ rest,
              fs.flatMap (fun f => f.map Cell.coefficient ++ [.fieldEnd]) ++ result,
              hfs f (by simp), ?_, ?_, ?_⟩
            · simp [wire, RationalCountedFields.wire, List.append_assoc]
            · exact (ih _ _).2 ⟨fs, rest, result, by simpa using hn,
                by intro f hf; exact hfs f (by simp [hf]), rfl, hnext, rfl⟩
            · simp [tag, close, List.append_assoc]

theorem tail_success_iff (bs : Bits) (out : List Cell) :
    tail bs = some out ↔ ∃ ts : List Bool, bs = ts.map some ∧ out = ts.map Cell.tail := by
  induction bs generalizing out with
  | nil => simp [tail]
  | cons b bs ih =>
      cases b with
      | none =>
          constructor
          · simp [tail]
          · rintro ⟨ts, he, _⟩
            cases ts <;> simp at he
      | some b =>
          constructor
          · intro h
            cases ht : tail bs with
            | none => simp [tail, ht] at h
            | some result =>
                obtain ⟨ts, rfl, rfl⟩ := (ih _).1 ht
                simp [tail, ht] at h
                exact ⟨b :: ts, rfl, h.symm⟩
          · rintro ⟨ts, he, rfl⟩
            cases ts with
            | nil => simp at he
            | cons t ts =>
                simp only [List.map_cons, List.cons.injEq, Option.some.injEq] at he
                rcases he with ⟨rfl, rfl⟩
                simp [tail, (ih _).2 ⟨ts, rfl, rfl⟩]

theorem rows_success_iff (r d : ℕ) (bs : Bits) (out : List Cell) :
    rows r d bs = some out ↔ ∃ rs : List Row, ∃ ts : List Bool,
      rs.length = r ∧ (∀ row ∈ rs, row.1 ≠ [] ∧ row.2.length = d ∧ ∀ f ∈ row.2, f ≠ []) ∧
      bs = wire (flatFields rs) ++ none :: ts.map some ∧
      out = rowsWire rs ++ .dataEnd :: ts.map Cell.tail := by
  induction r generalizing bs out with
  | zero =>
      constructor
      · intro h
        cases bs with
        | nil => simp [rows, ending] at h
        | cons b bs =>
            cases b with
            | some b => simp [rows, ending] at h
            | none =>
                cases ht : tail bs with
                | none => simp [rows, ending, ht] at h
                | some result =>
                    obtain ⟨ts, rfl, rfl⟩ := (tail_success_iff _ _).1 ht
                    simp [rows, ending, ht] at h
                    exact ⟨[], ts, rfl, by simp, rfl, h.symm⟩
      · rintro ⟨rs, ts, hn, _, rfl, rfl⟩
        have : rs = [] := by simpa using hn
        simp [this, flatFields, wire, RationalCountedFields.wire, rowsWire, rows, ending,
          (tail_success_iff _ _).2 ⟨ts, rfl, rfl⟩]
  | succ r ih =>
      rw [rows, field_success_iff]
      constructor
      · rintro ⟨f, rest, result, hf, rfl, h, rfl⟩
        obtain ⟨fs, rest', result', hn, hfs, rfl, hnext, rfl⟩ := (fields_success_iff _ _ _ _).1 h
        cases hr : rows r d rest' with
        | none => simp [hr] at hnext
        | some result =>
            simp [hr] at hnext
            obtain ⟨rs, ts, hlen, hrows, rfl, rfl⟩ := (ih _ _).1 hr
            refine ⟨(f, fs) :: rs, ts, by simp [hlen], ?_, ?_, ?_⟩
            · simp only [List.mem_cons]
              intro row hrow
              rcases hrow with rfl | hrow
              · exact ⟨hf, hn, hfs⟩
              · exact hrows row hrow
            · simp [flatFields, wire, RationalCountedFields.wire, List.append_assoc]
            · simp [← hnext, rowsWire, rowWire, tag, close, List.append_assoc]
      · rintro ⟨rs, ts, hn, hrows, rfl, rfl⟩
        cases rs with
        | nil => simp at hn
        | cons row rs =>
            obtain ⟨hf, hd, hfs⟩ := hrows row (by simp)
            have hi := (ih _ _).2 ⟨rs, ts, by simpa using hn,
              by intro x hx; exact hrows x (by simp [hx]), rfl, rfl⟩
            refine ⟨row.1, wire row.2 ++ wire (flatFields rs) ++ none :: ts.map some,
              row.2.flatMap (fun f => f.map Cell.coefficient ++ [.fieldEnd]) ++
                .rowEnd :: (rowsWire rs ++ .dataEnd :: ts.map Cell.tail), hf, ?_, ?_, ?_⟩
            · simp [flatFields, wire, RationalCountedFields.wire, List.append_assoc]
            · exact (fields_success_iff _ _ _ _).2 ⟨row.2,
                wire (flatFields rs) ++ none :: ts.map some,
                .rowEnd :: (rowsWire rs ++ .dataEnd :: ts.map Cell.tail), hd, hfs,
                by simp [List.append_assoc], by simp [hi], rfl⟩
            · simp [rowsWire, rowWire, tag, close, List.append_assoc]

theorem output_success_iff (r d : ℕ) (bs : Bits) : output r d bs ≠ [] ↔
    ∃ rs : List Row, ∃ ts : List Bool, rs.length = r ∧
      (∀ row ∈ rs, row.1 ≠ [] ∧ row.2.length = d ∧ ∀ f ∈ row.2, f ≠ []) ∧
      bs = wire (flatFields rs) ++ none :: ts.map some := by
  constructor
  · intro h
    cases hr : rows r d bs with
    | none => simp [output, hr, render] at h
    | some out =>
        obtain ⟨rs, ts, hn, hv, he, _⟩ := (rows_success_iff _ _ _ _).1 hr
        exact ⟨rs, ts, hn, hv, he⟩
  · rintro ⟨rs, ts, hn, hv, he⟩
    have hr := (rows_success_iff _ _ _ _).2 ⟨rs, ts, hn, hv, he, rfl⟩
    simp [output, hr, render]

theorem flatFields_length (d : ℕ) (rs : List Row)
    (h : ∀ row ∈ rs, row.2.length = d) : (flatFields rs).length = rs.length * (d+1) := by
  induction rs with
  | nil => simp [flatFields]
  | cons row rs ih =>
      have hr := h row (by simp)
      have hi := ih (by intro x hx; exact h x (by simp [hx]))
      simp only [flatFields, List.flatMap_cons, List.length_append, List.length_cons] at hi ⊢
      rw [hr, hi]
      ring


theorem count_none_map (xs : List Bool) : (xs.map some).count none = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- Count actual field delimiters, independent of the numerical headers. -/
theorem wire_count_none (fs : List (List Bool)) : (wire fs).count none = fs.length := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      simp only [wire, RationalCountedFields.wire, List.flatMap_cons] at ih ⊢
      simp [List.count_append, ih, count_none_map]

theorem exists_rows_of_length (r d : ℕ) (fs : List (List Bool))
    (hlen : fs.length = r*(d+1)) (hne : ∀ f ∈ fs, f ≠ []) :
    ∃ rs : List Row, rs.length = r ∧
      (∀ row ∈ rs, row.1 ≠ [] ∧ row.2.length = d ∧ ∀ f ∈ row.2, f ≠ []) ∧
      flatFields rs = fs := by
  induction r generalizing fs with
  | zero =>
      have : fs = [] := by simpa using hlen
      subst fs
      exact ⟨[], rfl, by simp, rfl⟩
  | succ r ih =>
      cases fs with
      | nil => simp at hlen
      | cons f fs =>
          have hsize : fs.length = d + r*(d+1) := by
            simp only [List.length_cons] at hlen
            nlinarith
          have hd : d ≤ fs.length := by omega
          obtain ⟨rs, hr, hs, he⟩ := ih (fs.drop d)
            (by simp [List.length_drop, hsize])
            (by intro x hx; exact hne x (by simp [List.mem_of_mem_drop hx]))
          refine ⟨(f,fs.take d) :: rs, by simp [hr], ?_, ?_⟩
          · intro row hrow
            simp only [List.mem_cons] at hrow
            rcases hrow with rfl | hrow
            · exact ⟨hne f (by simp), by simp [List.length_take, hd],
                by intro x hx; exact hne x (by simp [List.mem_of_mem_take hx])⟩
            · exact hs row hrow
          · change f :: (fs.take d ++ flatFields rs) = f :: fs
            rw [he, List.take_append_drop]

/-- On parsed nonempty fields, acceptance is exactly the rectangular count
identity. The machine does not assume this identity or multiply unary counters. -/
theorem output_fields_success_iff (r d : ℕ) (fs : List (List Bool)) (ts : List Bool)
    (hne : ∀ f ∈ fs, f ≠ []) :
    output r d (wire fs ++ none :: ts.map some) ≠ [] ↔ fs.length = r*(d+1) := by
  constructor
  · intro h
    obtain ⟨rs, tail, hr, hv, he⟩ := (output_success_iff _ _ _).1 h
    have hc := congrArg (List.count none) he
    simp only [List.count_append, List.count_cons, beq_self_eq_true, ↓reduceIte] at hc
    rw [wire_count_none, wire_count_none, count_none_map, count_none_map] at hc
    have hlen := flatFields_length d rs (by intro row hrow; exact (hv row hrow).2.1)
    rw [hr] at hlen
    omega
  · intro h
    obtain ⟨rs, hr, hv, he⟩ := exists_rows_of_length r d fs h hne
    exact (output_success_iff _ _ _).2 ⟨rs, ts, hr, hv, by rw [he]⟩

theorem output_fields_nil_iff (r d : ℕ) (fs : List (List Bool)) (ts : List Bool)
    (hne : ∀ f ∈ fs, f ≠ []) :
    output r d (wire fs ++ none :: ts.map some) = [] ↔ fs.length ≠ r*(d+1) := by
  simpa using not_congr (output_fields_success_iff r d fs ts hne)

def fractionRows (rs : List RationalCertificateBroadcast.Row) : List Row :=
  rs.map fun row => (row.1.encode, row.2.map Fraction.encode)

def rowCell : Option RationalCertificateBroadcast.Machine.RowCell → Cell
  | none => .rowEnd
  | some (.inl b) => .response b
  | some (.inr none) => .fieldEnd
  | some (.inr (some b)) => .coefficient b

/-- The row output is exactly the existing internal observation encoding,
with a fixed alphabet renaming. Fraction bytes are never normalized. -/
theorem rowsWire_fractionRows (rs : List RationalCertificateBroadcast.Row) :
    rowsWire (fractionRows rs) =
      ((RationalCertificateBroadcast.listEncoding RationalCertificateBroadcast.rowEncoding).encode rs).map rowCell := by
  induction rs with
  | nil => rfl
  | cons row rs ih =>
      simp only [fractionRows, List.map_cons, rowsWire, List.flatMap_cons,
        RationalCertificateBroadcast.listEncoding, RationalCertificateBroadcast.frames,
        List.map_cons, List.flatMap_cons, List.map_append] at ih ⊢
      congr 1
      simp [rowWire, RationalCertificateBroadcast.frame, RationalCertificateBroadcast.rowEncoding,
        LeanNPHardness.PairEncoding.finEncoding, RationalNorm.fractionEncoding,
        RationalNormList.encoding, RationalSum.fields, RationalSum.field,
        List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def, rowCell]

theorem output_fractionRows (r d : ℕ) (rs : List RationalCertificateBroadcast.Row) (ts : List Bool)
    (hr : rs.length = r) (hd : ∀ row ∈ rs, row.2.length = d) :
    output r d (wire (flatFields (fractionRows rs)) ++ none :: ts.map some) =
      rowsWire (fractionRows rs) ++ .dataEnd :: ts.map Cell.tail := by
  have hn (f : Fraction) : f.encode ≠ [] := by simp [Fraction.encode, SmithEncoding.encodeInt]
  have h := (rows_success_iff _ _ _ _).2 ⟨fractionRows rs, ts, by simpa [fractionRows] using hr,
    by
      intro row hrow
      simp only [fractionRows] at hrow
      obtain ⟨q, hq, he⟩ := List.mem_map.mp hrow
      subst row
      refine ⟨hn _, by simpa using hd q hq, ?_⟩
      intro f hf
      obtain ⟨f, _, rfl⟩ := List.mem_map.mp hf
      exact hn f,
    rfl, rfl⟩
  simp [output, h, render]

theorem flatFields_observations {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) :
    flatFields (fractionRows (RationalCertificateBroadcast.observations A y)) =
      (RationalWitnessEncoding.inputEntries A y).map RationalWitnessEncoding.encodeRat := by
  simp [flatFields, fractionRows, RationalCertificateBroadcast.observations,
    RationalWitnessEncoding.inputEntries, List.flatMap_def,
    List.map_ofFn, List.map_flatten, Function.comp_def, RationalNorm.ofRat_encode]

/-- Directly identifies the preceding counted-list parser's data output and
this component's response/coefficient output for the thesis rational record. -/
theorem output_original_data {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (ts : List Bool) :
    output r d (RationalCountedList.output
      (RationalWitnessEncoding.encodeRats (RationalWitnessEncoding.inputEntries A y) ++ ts)) =
      ((RationalCertificateBroadcast.listEncoding RationalCertificateBroadcast.rowEncoding).encode
        (RationalCertificateBroadcast.observations A y)).map rowCell ++ .dataEnd :: ts.map Cell.tail := by
  rw [RationalCountedList.output_encodeRats_append, ← flatFields_observations]
  have h := output_fractionRows r d (RationalCertificateBroadcast.observations A y) ts
    (by simp [RationalCertificateBroadcast.observations])
    (by
      intro row hrow
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
      simp)
  simpa only [rowsWire_fractionRows, wire] using h

theorem rowsWire_length (rs : List Row) : (rowsWire rs).length = (wire (flatFields rs)).length := by
  induction rs with
  | nil => rfl
  | cons row rs ih =>
      have hc : (row.2.flatMap (fun f => f.map Cell.coefficient ++ [.fieldEnd])).length =
          (wire row.2).length := by
        simp [wire, RationalCountedFields.wire, List.length_flatMap]
      simp only [rowsWire, List.flatMap_cons] at ih ⊢
      simp [rowWire, flatFields, wire, RationalCountedFields.wire,
        List.length_flatMap] at hc ih ⊢
      omega

theorem output_length_le (r d : ℕ) (bs : Bits) : (output r d bs).length ≤ bs.length := by
  cases hr : rows r d bs with
  | none => simp [output, hr]
  | some out =>
      obtain ⟨rs, ts, _, _, rfl, rfl⟩ := (rows_success_iff _ _ _ _).1 hr
      simp [output, hr, rowsWire_length]


#print axioms output_success_iff
#print axioms output_fields_success_iff
#print axioms output_fields_nil_iff
#print axioms rowsWire_fractionRows
#print axioms output_length_le
#print axioms output_original_data

end PhdThesisLean.RationalRectangularFields
