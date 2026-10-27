import SparseIrred.UpperBounds.Section4.BinaryFieldPow

/-!
# Uniform polynomial-time binary finite-field interface

The characteristic and dense modulus are parameters of every operation. All
outputs use exactly the canonical coefficient encoding of the uniform machine.
The Cobham proofs apply to all raw bit strings, and the semantic theorems apply
to every validated field presentation, including characteristic two.
-/

namespace SparseIrred.UpperBounds.Section4

open Polynomial Complexity SparseDiv SparseDiv.StringArith SparseGcd SparseGcd.TermsStr

def fieldAddStr (p h a b : List Bool) : List Bool :=
  vectorAddStr p (fieldTemplateStr h) a b
def fieldNegStr (p h a : List Bool) : List Bool := vectorNegStr p (fieldTemplateStr h) a
def fieldSubStr (p h a b : List Bool) : List Bool := fieldAddStr p h a (fieldNegStr p h b)
def fieldZeroFlagStr (h a : List Bool) : List Bool := Cobham.eqFlag a (fieldZeroStr h)

theorem cobham_fieldAddStr_comp {n : ℕ} {p h a b : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (hh : Cobham h) (ha : Cobham a) (hb : Cobham b) :
    Cobham fun v ↦ fieldAddStr (p v) (h v) (a v) (b v) :=
  cobham_vectorAddStr_comp hp (cobham_fieldTemplateStr_comp hh) ha hb

theorem cobham_fieldNegStr_comp {n : ℕ} {p h a : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (hh : Cobham h) (ha : Cobham a) :
    Cobham fun v ↦ fieldNegStr (p v) (h v) (a v) :=
  cobham_vectorNegStr_comp hp (cobham_fieldTemplateStr_comp hh) ha

theorem cobham_fieldSubStr_comp {n : ℕ} {p h a b : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (hh : Cobham h) (ha : Cobham a) (hb : Cobham b) :
    Cobham fun v ↦ fieldSubStr (p v) (h v) (a v) (b v) :=
  cobham_fieldAddStr_comp hp hh ha (cobham_fieldNegStr_comp hp hh hb)

theorem cobham_fieldZeroFlagStr_comp {n : ℕ} {h a : (Fin n → List Bool) → List Bool}
    (hh : Cobham h) (ha : Cobham a) :
    Cobham fun v ↦ fieldZeroFlagStr (h v) (a v) :=
  Cobham.eqFlag_mem ha (cobham_fieldZeroStr_comp hh)

theorem fieldAddStr_length (p h a b : List Bool) :
    (fieldAddStr p h a b).length ≤ (2 * p.length + 2) * h.length := by
  have hl := vectorAddStr_length p (fieldTemplateStr h) a b
  rw [fieldTemplateStr_blocks, List.length_dropLast] at hl
  exact hl.trans (Nat.mul_le_mul_left _ ((Nat.sub_le _ _).trans (blocks_length_le_input h)))

theorem fieldNegStr_length (p h a : List Bool) :
    (fieldNegStr p h a).length ≤ (2 * p.length + 2) * h.length := by
  have hl := vectorNegStr_length p (fieldTemplateStr h) a
  rw [fieldTemplateStr_blocks, List.length_dropLast] at hl
  exact hl.trans (Nat.mul_le_mul_left _ ((Nat.sub_le _ _).trans (blocks_length_le_input h)))

theorem fieldSubStr_length (p h a b : List Bool) :
    (fieldSubStr p h a b).length ≤ (2 * p.length + 2) * h.length :=
  fieldAddStr_length _ _ _ _

theorem fieldPowStr_length (p h a e : List Bool) :
    (fieldPowStr p h a e).length ≤ (2 * p.length + 2) * h.length :=
  fieldPowAux_length _ _ _ _

theorem fieldNormalizeStr_length (p h a : List Bool) :
    (fieldNormalizeStr p h a).length ≤ (2 * p.length + 2) * h.length :=
  fieldMulStr_length _ _ _ _

theorem fieldInvStr_length (p h a : List Bool) :
    (fieldInvStr p h a).length ≤ (2 * p.length + 2) * h.length := by
  rcases caseBit₀_cases (Cobham.eqFlag a (fieldZeroStr h)) (fieldZeroStr h)
    (fieldPowStr p h a (subBits (fieldCardStr p h) (encNat 2))) with hs | hs
  · have hz := fieldZeroStr_length h
    change (caseBit₀ _ _ _).length ≤ _
    rw [hs]
    nlinarith
  · change (caseBit₀ _ _ _).length ≤ _
    rw [hs]
    exact fieldPowStr_length _ _ _ _

theorem fieldAddStr_encoded (c : FieldCode) [Fact c.Valid] (x y : c.Carrier) :
    fieldAddStr (encNat c.characteristic) (encodeNumerals c.modulus)
        (encodeNumerals (c.encodeElement x)) (encodeNumerals (c.encodeElement y)) =
      encodeNumerals (c.encodeElement (x + y)) := by
  unfold fieldAddStr
  rw [show fieldTemplateStr (encodeNumerals c.modulus) =
    frame (c.modulus.map encNat).dropLast from fieldTemplateStr_frame _]
  exact vectorAddStr_encoded c _ c.template_length x y

theorem fieldNegStr_encoded (c : FieldCode) [Fact c.Valid] (x : c.Carrier) :
    fieldNegStr (encNat c.characteristic) (encodeNumerals c.modulus)
        (encodeNumerals (c.encodeElement x)) = encodeNumerals (c.encodeElement (-x)) := by
  unfold fieldNegStr
  rw [show fieldTemplateStr (encodeNumerals c.modulus) =
    frame (c.modulus.map encNat).dropLast from fieldTemplateStr_frame _]
  exact vectorNegStr_encoded c _ c.template_length x

theorem fieldSubStr_encoded (c : FieldCode) [Fact c.Valid] (x y : c.Carrier) :
    fieldSubStr (encNat c.characteristic) (encodeNumerals c.modulus)
        (encodeNumerals (c.encodeElement x)) (encodeNumerals (c.encodeElement y)) =
      encodeNumerals (c.encodeElement (x - y)) := by
  rw [fieldSubStr, fieldNegStr_encoded, fieldAddStr_encoded, sub_eq_add_neg]

theorem fieldZeroFlagStr_encoded (c : FieldCode) [Fact c.Valid] [DecidableEq c.Carrier]
    (x : c.Carrier) :
    fieldZeroFlagStr (encodeNumerals c.modulus) (encodeNumerals (c.encodeElement x)) =
      [decide (x = 0)] := by
  classical
  unfold fieldZeroFlagStr
  rw [fieldZeroStr_encoded]
  by_cases hx : x = 0
  · simp [hx, SparseDiv.StringArith.eqFlag_self]
  · have hc := fun he ↦ hx (c.scalar_encoding_injective he)
    rcases Cobham.eqFlag_flag (encodeNumerals (c.encodeElement x))
      (encodeNumerals (c.encodeElement 0)) with h | h
    · exact (hc ((Cobham.eqFlag_eq_true_iff _ _).mp h)).elim
    · simpa [hx] using h

/-- The canonical binary scalar encoding used by all field operations. -/
noncomputable def FieldCode.scalarCode (c : FieldCode) [Fact c.Valid] (x : c.Carrier) : List Bool :=
  encodeNumerals (c.encodeElement x)

theorem fieldAddStr_mem_FPn :
    Cobham.FPn (fun v : Fin 4 → List Bool ↦ fieldAddStr (v 0) (v 1) (v 2) (v 3)) :=
  Cobham.cobham_iff_FPn.mp (cobham_fieldAddStr_comp (.proj 0) (.proj 1) (.proj 2) (.proj 3))

theorem fieldMulStr_mem_FPn :
    Cobham.FPn (fun v : Fin 4 → List Bool ↦ fieldMulStr (v 0) (v 1) (v 2) (v 3)) :=
  Cobham.cobham_iff_FPn.mp cobham_fieldMulStr

theorem fieldPowStr_mem_FPn :
    Cobham.FPn (fun v : Fin 4 → List Bool ↦ fieldPowStr (v 0) (v 1) (v 2) (v 3)) :=
  Cobham.cobham_iff_FPn.mp cobham_fieldPowStr

theorem fieldInvStr_mem_FPn :
    Cobham.FPn (fun v : Fin 3 → List Bool ↦ fieldInvStr (v 0) (v 1) (v 2)) :=
  Cobham.cobham_iff_FPn.mp (cobham_fieldInvStr_comp (.proj 0) (.proj 1) (.proj 2))

theorem fieldNormalizeStr_mem_FPn :
    Cobham.FPn (fun v : Fin 3 → List Bool ↦ fieldNormalizeStr (v 0) (v 1) (v 2)) :=
  Cobham.cobham_iff_FPn.mp (cobham_fieldNormalizeStr_comp (.proj 0) (.proj 1) (.proj 2))

/-- Canonicalize every natural-number block without changing the lenient list decoding. -/
def canonicalNumeralBlocks (s : List Bool) : List Bool := mapBlocks canonBits s

theorem canonicalNumeralBlocks_eq (s : List Bool) :
    canonicalNumeralBlocks s = encodeNumerals (decodeNumerals s) := by
  simp only [canonicalNumeralBlocks, mapBlocks, encodeNumerals, decodeNumerals,
    List.map_map, canonBits, Function.comp_def]
  rfl

/-- Total scalar normalization, including completely malformed binary strings. -/
def fieldDecodeNormalizeStr (p h a : List Bool) : List Bool :=
  fieldNormalizeStr p h (canonicalNumeralBlocks a)

theorem cobham_fieldDecodeNormalizeStr_comp {n : ℕ} {p h a : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (hh : Cobham h) (ha : Cobham a) :
    Cobham fun v ↦ fieldDecodeNormalizeStr (p v) (h v) (a v) :=
  cobham_fieldNormalizeStr_comp hp hh (TermsStr.cobham_mapBlocks_comp
    (F := fun b _ ↦ canonBits b) (cobham_canonBits_comp (.proj 0)) ha)

theorem fieldDecodeNormalizeStr_correct (c : FieldCode) [Fact c.Valid] (a : List Bool) :
    fieldDecodeNormalizeStr (encNat c.characteristic) (encodeNumerals c.modulus) a =
      c.scalarCode (c.element (decodeNumerals a)) := by
  rw [fieldDecodeNormalizeStr, canonicalNumeralBlocks_eq, fieldNormalizeStr_encoded]
  rfl

theorem fieldDecodeNormalizeStr_length (p h a : List Bool) :
    (fieldDecodeNormalizeStr p h a).length ≤ (2 * p.length + 2) * h.length :=
  fieldNormalizeStr_length _ _ _

end SparseIrred.UpperBounds.Section4
