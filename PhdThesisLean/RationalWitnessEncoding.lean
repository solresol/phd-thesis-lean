import PhdThesisLean.RationalWitnessBounds
import PhdThesisLean.SmithEncoding

/-!
# Polynomial-length binary rational certificates

Signs, binary magnitudes, positive denominators, length frames, dimensions,
targets and thresholds are charged. This file proves a certificate-length
bound, not a polynomial-time machine for parsing or checking certificates.
-/

namespace PhdThesisLean.RationalWitnessEncoding

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Matrix
open LeanNPHardness RationalWitnesses RationalWitnessBounds

/-- Signed numerator followed by a framed positive binary denominator. -/
def encodeRat (q : ℚ) : List Bool :=
  SmithEncoding.encodeInt q.num ++ BinaryNatLists.encodeNat q.den

def decodeRatPrefix (bits : List Bool) : Option (ℚ × List Bool) := do
  let (z, tail) ← SmithEncoding.decodeIntPrefix bits
  let (n, rest) ← BinaryNatLists.decodeNatPrefix tail
  if n = 0 then none else pure ((z : ℚ) / n, rest)

@[simp]
theorem decodeRatPrefix_encode_append (q : ℚ) (rest : List Bool) :
    decodeRatPrefix (encodeRat q ++ rest) = some (q, rest) := by
  simp [encodeRat, decodeRatPrefix, List.append_assoc, Rat.num_div_den]

theorem encodeRat_length (q : ℚ) : (encodeRat q).length = 2 * ratBits q + 3 := by
  simp [encodeRat, SmithEncoding.encodeInt_length, BinaryNatLists.natWireSize,
    BinaryNatLists.encodeNat_length_eq_size, ratBits]
  omega

def encodeRats (qs : List ℚ) : List Bool :=
  BinaryNatLists.encodeNat qs.length ++ qs.flatMap encodeRat

def decodeRats : ℕ → List Bool → Option (List ℚ × List Bool)
  | 0, bits => some ([], bits)
  | n + 1, bits => do
      let (q, tail) ← decodeRatPrefix bits
      let (qs, rest) ← decodeRats n tail
      pure (q :: qs, rest)

@[simp]
theorem decodeRats_encode_append (qs : List ℚ) (rest : List Bool) :
    decodeRats qs.length (qs.flatMap encodeRat ++ rest) = some (qs, rest) := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp [decodeRats, List.append_assoc, ih]

def decodeRatsPrefix (bits : List Bool) : Option (List ℚ × List Bool) := do
  let (n, tail) ← BinaryNatLists.decodeNatPrefix bits
  decodeRats n tail

@[simp]
theorem decodeRatsPrefix_encode_append (qs : List ℚ) (rest : List Bool) :
    decodeRatsPrefix (encodeRats qs ++ rest) = some (qs, rest) := by
  simp [decodeRatsPrefix, encodeRats, List.append_assoc]

theorem encodeRats_injective : Function.Injective encodeRats := by
  intro qs rs h
  have he := congrArg (fun bits => decodeRatsPrefix (bits ++ [])) h
  rw [decodeRatsPrefix_encode_append, decodeRatsPrefix_encode_append] at he
  exact congrArg Prod.fst (Option.some.inj he)

theorem encodeRats_length (qs : List ℚ) :
    (encodeRats qs).length = 2 * qs.length.size + 1 +
      (qs.map (fun q => 2 * ratBits q + 3)).sum := by
  simp [encodeRats, List.length_flatMap, encodeRat_length, BinaryNatLists.natWireSize,
    BinaryNatLists.encodeNat_length_eq_size]

theorem payload_le_encodeRats (qs : List ℚ) :
    (qs.map ratBits).sum ≤ (encodeRats qs).length := by
  rw [encodeRats_length]
  apply le_trans _ (Nat.le_add_left _ _)
  exact List.sum_le_sum (by intro q hq; omega)

theorem count_le_encodeRats (qs : List ℚ) : qs.length ≤ (encodeRats qs).length := by
  rw [encodeRats_length]
  apply le_trans _ (Nat.le_add_left _ _)
  have h : qs.length ≤ (qs.map (fun q => 2 * ratBits q + 3)).sum := by
    induction qs with
    | nil => simp
    | cons q qs ih => simp only [List.length_cons, List.map_cons, List.sum_cons]; omega
  exact h

/-- Row-major data, with each row's target first. Repetitions are retained. -/
def inputEntries {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) : List ℚ :=
  (List.ofFn fun i => y i :: List.ofFn (A i)).flatten

theorem inputEntries_length {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) :
    (inputEntries A y).length = r * (d + 1) := by
  simp [inputEntries, List.length_flatten, List.map_ofFn, List.sum_ofFn]

theorem inputEntries_bits {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) :
    ((inputEntries A y).map ratBits).sum = dataBits (inputData A y) := by
  simp [inputEntries, List.map_flatten, List.sum_flatten, List.map_ofFn, List.sum_ofFn,
    dataBits, Fintype.sum_prod_type, Fintype.sum_option, inputData]

/-- Binary dimensions, framed rational data, and a rational threshold. -/
def encodeInput {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ)
    (B : ℚ) : List Bool :=
  BinaryNatLists.encodeNat r ++ BinaryNatLists.encodeNat d ++
    encodeRats (inputEntries A y) ++ encodeRat B

theorem input_size_bounds {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) (hr : 0 < r) :
    d ≤ (encodeInput A y B).length ∧
      dataBits (inputData A y) ≤ (encodeInput A y B).length := by
  have he : (encodeRats (inputEntries A y)).length ≤ (encodeInput A y B).length := by
    simp only [encodeInput, List.length_append]
    omega
  have hc := count_le_encodeRats (inputEntries A y)
  rw [inputEntries_length] at hc
  have hd : d ≤ r * (d + 1) := by nlinarith
  exact ⟨hd.trans (hc.trans he), by
    rw [← inputEntries_bits]
    exact (payload_le_encodeRats _).trans he⟩

theorem encodeRats_length_le (qs : List ℚ) (h : ℕ)
    (hq : ∀ q ∈ qs, q.num.natAbs.size ≤ h ∧ q.den.size ≤ h) :
    (encodeRats qs).length ≤ qs.length * (4 * h + 5) + 1 := by
  have hs : qs.length.size ≤ qs.length := Nat.size_le.mpr qs.length.lt_two_pow_self
  have hb : (qs.map (fun q => 2 * ratBits q + 3)).sum ≤ qs.length * (4 * h + 3) := by
    calc
      _ ≤ (qs.map (fun _ => 4 * h + 3)).sum := by
        apply List.sum_le_sum
        intro q hmem
        have := hq q hmem
        simp only [ratBits]
        omega
      _ = _ := by simp
  rw [encodeRats_length]
  nlinarith

/-- A complete dense certificate has cubic length in the actual binary input.
Only the positive row count is needed to charge the number of coordinates;
rank-zero and repeated/conflicting data remain covered. -/
theorem exists_global_minimizer_encoding (p : ℕ) [Fact p.Prime] {r d : ℕ}
    (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) (B : ℚ) (hr : 0 < r) :
    ∃ β : Fin d → ℚ,
      (∀ β', loss p A y β ≤ loss p A y β') ∧
      (encodeRats (List.ofFn β)).length ≤
        12 * (encodeInput A y B).length ^ 3 + 9 * (encodeInput A y B).length + 1 := by
  let L := (encodeInput A y B).length
  have hd : d ≤ L := (input_size_bounds A y B hr).1
  have hdata : dataBits (inputData A y) ≤ L := (input_size_bounds A y B hr).2
  have hrank : A.rank ≤ L := (by simpa using A.rank_le_card_width : A.rank ≤ d).trans hd
  have hsize : A.rank.size ≤ L :=
    (Nat.size_le.mpr A.rank.lt_two_pow_self).trans hrank
  have hb : A.rank * (2 * dataBits (inputData A y) + A.rank.size) + 1 ≤ 3 * L ^ 2 + 1 := by
    have := Nat.mul_le_mul hrank (show 2 * dataBits (inputData A y) + A.rank.size ≤ 3 * L by omega)
    nlinarith
  obtain ⟨β, hmin, hβ⟩ := exists_global_minimizer_bits p A y
  refine ⟨β, hmin, ?_⟩
  have he := encodeRats_length_le (List.ofFn β) (3 * L ^ 2 + 1) (by
    intro q hq
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
    exact ⟨(hβ i).1.trans hb, (hβ i).2.trans hb⟩)
  simp only [List.length_ofFn] at he
  have hm := Nat.mul_le_mul_right (4 * (3 * L ^ 2 + 1) + 5) hd
  change (encodeRats (List.ofFn β)).length ≤ 12 * L ^ 3 + 9 * L + 1
  nlinarith

/-- The threshold language can restrict its existential quantifier to the
proved polynomial-size certificates. This does not yet establish NP membership. -/
theorem threshold_iff_short_certificate (p : ℕ) [Fact p.Prime] {r d : ℕ}
    (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) (B : ℚ) (hr : 0 < r) :
    (∃ β, loss p A y β ≤ B) ↔
      ∃ β, loss p A y β ≤ B ∧ (encodeRats (List.ofFn β)).length ≤
        12 * (encodeInput A y B).length ^ 3 + 9 * (encodeInput A y B).length + 1 := by
  constructor
  · rintro ⟨β, hβ⟩
    obtain ⟨γ, hmin, hlen⟩ := exists_global_minimizer_encoding p A y B hr
    exact ⟨γ, (hmin β).trans hβ, hlen⟩
  · rintro ⟨β, hβ, _⟩
    exact ⟨β, hβ⟩

theorem rows_le_input_length {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ)
    (y : Fin r → ℚ) (B : ℚ) : r ≤ (encodeInput A y B).length := by
  have hc := count_le_encodeRats (inputEntries A y)
  rw [inputEntries_length] at hc
  have hr : r ≤ r * (d + 1) := by nlinarith
  simp only [encodeInput, List.length_append]
  omega

theorem affineData_bits {r d : ℕ} (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) :
    dataBits (inputData (RegularisedCandidates.affineDesign A) y) =
      dataBits (inputData A y) + 2 * r := by
  simp [dataBits, Fintype.sum_prod_type, Fintype.sum_option, inputData,
    RegularisedCandidates.affineDesign, ContactTheorem.augment, Fin.sum_univ_succ,
    ratBits, Finset.sum_add_distrib]
  omega

/-- The affine certificate is bounded in the original input length, before
adding the column of ones. Its first coefficient is the free intercept. -/
theorem exists_affine_minimizer_encoding (p : ℕ) [Fact p.Prime] {r d : ℕ}
    (A : Matrix (Fin r) (Fin d) ℚ) (y : Fin r → ℚ) (B : ℚ) (hr : 0 < r) :
    ∃ c : ℚ, ∃ β : Fin d → ℚ,
      (∀ c' : ℚ, ∀ β' : Fin d → ℚ,
        (∑ i, padicNorm p (y i - ((A *ᵥ β) i + c))) ≤
          ∑ i, padicNorm p (y i - ((A *ᵥ β') i + c'))) ∧
      (encodeRats (List.ofFn (Fin.cons c β))).length ≤
        28 * ((encodeInput A y B).length + 1) ^ 3 +
          9 * ((encodeInput A y B).length + 1) + 1 := by
  let L := (encodeInput A y B).length
  let C : Matrix (Fin r) (Fin (d + 1)) ℚ := RegularisedCandidates.affineDesign A
  have hd : d + 1 ≤ L + 1 := Nat.add_le_add_right (input_size_bounds A y B hr).1 1
  have hrows : r ≤ L := rows_le_input_length A y B
  have hdata : dataBits (inputData C y) ≤ 3 * (L + 1) := by
    rw [show C = RegularisedCandidates.affineDesign A from rfl, affineData_bits]
    have := (input_size_bounds A y B hr).2
    change dataBits (inputData A y) ≤ L at this
    omega
  have hrank : C.rank ≤ L + 1 := C.rank_le_width.trans hd
  have hsize : C.rank.size ≤ L + 1 :=
    (Nat.size_le.mpr C.rank.lt_two_pow_self).trans hrank
  have hb : C.rank * (2 * dataBits (inputData C y) + C.rank.size) + 1 ≤
      7 * (L + 1) ^ 2 + 1 := by
    have := Nat.mul_le_mul hrank
      (show 2 * dataBits (inputData C y) + C.rank.size ≤ 7 * (L + 1) by omega)
    nlinarith
  obtain ⟨θ, hmin, hθ⟩ := exists_global_minimizer_bits p C y
  have hcons : Fin.cons (θ 0) (fun i => θ i.succ) = θ := by
    ext i
    exact Fin.cases rfl (fun _ => rfl) i
  refine ⟨θ 0, fun i => θ i.succ, ?_, ?_⟩
  · intro c' β'
    rw [← loss_affineDesign, hcons, ← loss_affineDesign]
    exact hmin _
  · rw [hcons]
    have he := encodeRats_length_le (List.ofFn θ) (7 * (L + 1) ^ 2 + 1) (by
      intro q hq
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
      exact ⟨(hθ i).1.trans hb, (hθ i).2.trans hb⟩)
    simp only [List.length_ofFn] at he
    have hm := Nat.mul_le_mul_right (4 * (7 * (L + 1) ^ 2 + 1) + 5) hd
    change (encodeRats (List.ofFn θ)).length ≤ 28 * (L + 1) ^ 3 + 9 * (L + 1) + 1
    nlinarith

#print axioms decodeRatPrefix_encode_append
#print axioms decodeRatsPrefix_encode_append
#print axioms encodeRats_injective
#print axioms encodeRat_length
#print axioms input_size_bounds
#print axioms encodeRats_length_le
#print axioms exists_global_minimizer_encoding
#print axioms threshold_iff_short_certificate
#print axioms affineData_bits
#print axioms exists_affine_minimizer_encoding

end PhdThesisLean.RationalWitnessEncoding
