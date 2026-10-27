import SparseIrred.UpperBounds.Section4.BinaryFieldMul

/-! # Binary exponentiation, field cardinality, and inversion for presented finite fields -/

namespace SparseIrred.UpperBounds.Section4

open Polynomial Complexity SparseDiv SparseDiv.StringArith SparseGcd SparseGcd.TermsStr

def fieldPowAux (p h a : List Bool) : List Bool → List Bool
  | [] => fieldOneStr p h
  | false :: e => fieldMulStr p h (fieldPowAux p h a e) (fieldPowAux p h a e)
  | true :: e => fieldMulStr p h
      (fieldMulStr p h (fieldPowAux p h a e) (fieldPowAux p h a e)) a

def fieldPowStr (p h a e : List Bool) : List Bool := fieldPowAux p h a e

theorem fieldPowAux_length (p h a e : List Bool) :
    (fieldPowAux p h a e).length ≤ (2 * p.length + 2) * h.length := by
  cases e with
  | nil => exact fieldConstStr_length _ _ _
  | cons bit e => cases bit <;> exact fieldMulStr_length _ _ _ _

theorem recNotation_fieldPow (e : List Bool) (v : Fin 3 → List Bool) :
    recNotation (fun u : Fin 3 → List Bool ↦ fieldOneStr (u 0) (u 1))
      (fun w : Fin 5 → List Bool ↦ fieldMulStr (w 2) (w 3) (w 1) (w 1))
      (fun w : Fin 5 → List Bool ↦
        fieldMulStr (w 2) (w 3) (fieldMulStr (w 2) (w 3) (w 1) (w 1)) (w 4)) e v =
      fieldPowAux (v 0) (v 1) (v 2) e := by
  induction e with
  | nil => rfl
  | cons bit e ih =>
      cases bit
      · change fieldMulStr (v 0) (v 1) (recNotation _ _ _ e v) (recNotation _ _ _ e v) = _
        rw [ih]
        rfl
      · change fieldMulStr (v 0) (v 1)
          (fieldMulStr (v 0) (v 1) (recNotation _ _ _ e v) (recNotation _ _ _ e v)) (v 2) = _
        rw [ih]
        rfl

theorem cobham_fieldPowStr :
    Cobham fun v : Fin 4 → List Bool ↦ fieldPowStr (v 0) (v 1) (v 2) (v 3) := by
  have hg : Cobham fun u : Fin 3 → List Bool ↦ fieldOneStr (u 0) (u 1) :=
    cobham_fieldOneStr_comp (.proj 0) (.proj 1)
  have h₀ : Cobham fun w : Fin 5 → List Bool ↦ fieldMulStr (w 2) (w 3) (w 1) (w 1) :=
    cobham_fieldMulStr_comp (.proj 2) (.proj 3) (.proj 1) (.proj 1)
  have h₁ : Cobham fun w : Fin 5 → List Bool ↦
      fieldMulStr (w 2) (w 3) (fieldMulStr (w 2) (w 3) (w 1) (w 1)) (w 4) :=
    cobham_fieldMulStr_comp (.proj 2) (.proj 3)
      (cobham_fieldMulStr_comp (.proj 2) (.proj 3) (.proj 1) (.proj 1)) (.proj 4)
  have hr : Cobham fun u : Fin 4 → List Bool ↦
      Cobham.polyLen (2 * Polynomial.X ^ 2 + 2 * Polynomial.X) (u 1 ++ u 2) :=
    Cobham.polyLen_mem _ (Cobham.appendFn (.proj 1) (.proj 2))
  have hrec := Cobham.boundedRec hg h₀ h₁ hr (by
    intro e v
    rw [recNotation_fieldPow]
    have hl := fieldPowAux_length (v 0) (v 1) (v 2) e
    change (fieldPowAux (v 0) (v 1) (v 2) e).length ≤
      (Cobham.polyLen (2 * Polynomial.X ^ 2 + 2 * Polynomial.X) (v 0 ++ v 1)).length
    simp only [Cobham.polyLen_length, List.length_append,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_ofNat]
    nlinarith)
  refine (Cobham.comp hrec
    (gs := fun i (v : Fin 4 → List Bool) ↦ ![v 3, v 0, v 1, v 2] i)
    (by intro i; fin_cases i; exact .proj 3; exact .proj 0; exact .proj 1; exact .proj 2)).of_eq ?_
  intro v
  rw [recNotation_fieldPow]
  rfl

theorem cobham_fieldPowStr_comp {n : ℕ} {p h a e : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (hh : Cobham h) (ha : Cobham a) (he : Cobham e) :
    Cobham fun v ↦ fieldPowStr (p v) (h v) (a v) (e v) := by
  exact (Cobham.comp cobham_fieldPowStr
    (gs := fun i v ↦ ![p v, h v, a v, e v] i)
    (by intro i; fin_cases i; exact hp; exact hh; exact ha; exact he)).of_eq fun _ ↦ rfl

theorem fieldPowStr_encoded (c : FieldCode) [Fact c.Valid] (x : c.Carrier) (e : List Bool) :
    fieldPowStr (encNat c.characteristic) (encodeNumerals c.modulus)
        (encodeNumerals (c.encodeElement x)) e =
      encodeNumerals (c.encodeElement (x ^ decNat e)) := by
  unfold fieldPowStr
  induction e with
  | nil => rw [fieldPowAux, fieldOneStr_encoded]; change _ = encodeNumerals (c.encodeElement (x ^ 0)); rw [pow_zero]
  | cons bit e ih =>
      cases bit
      · rw [fieldPowAux, ih, fieldMulStr_encoded]
        congr 2
        simp only [decNat_cons, Bool.false_eq_true, ↓reduceIte, zero_add]
        ring
      · rw [fieldPowAux, ih, fieldMulStr_encoded, fieldMulStr_encoded]
        congr 2
        simp only [decNat_cons, ↓reduceIte]
        ring

/-- Compute `p^d` from the explicit dense modulus header. -/
def fieldCardStr (p h : List Bool) : List Bool :=
  canonBits (prodStr (mapBlocks (fun _ ↦ p) (fieldTemplateStr h)))

theorem cobham_fieldCardStr_comp {n : ℕ} {p h : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (hh : Cobham h) : Cobham fun v ↦ fieldCardStr (p v) (h v) := by
  have hm := TermsStr.cobham_mapBlocks_comp (F := fun _ v ↦ p v)
    (TermsStr.cobham_tail_comp hp) (cobham_fieldTemplateStr_comp hh)
  exact cobham_canonBits_comp ((Cobham.comp cobham_prodStr (fun _ : Fin 1 ↦ hm)).of_eq
    (fun _ ↦ rfl))

theorem fieldCardStr_encoded (c : FieldCode) [Fact c.Valid] :
    fieldCardStr (encNat c.characteristic) (encodeNumerals c.modulus) =
      encNat (Fintype.card c.Carrier) := by
  unfold fieldCardStr
  rw [encodeNumerals, fieldTemplateStr_frame, mapBlocks_frame]
  rw [List.map_const']
  have he : List.replicate (c.modulus.map encNat).dropLast.length (encNat c.characteristic) =
      (List.replicate c.degree c.characteristic).map encNat := by
    rw [c.template_length, List.map_replicate]
  rw [he, canonBits, decNat_prodStr, List.prod_replicate, c.card_carrier]

def fieldInvStr (p h a : List Bool) : List Bool :=
  caseBit₀ (Cobham.eqFlag a (fieldZeroStr h)) (fieldZeroStr h)
    (fieldPowStr p h a (subBits (fieldCardStr p h) (encNat 2)))

theorem cobham_fieldInvStr_comp {n : ℕ} {p h a : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (hh : Cobham h) (ha : Cobham a) :
    Cobham fun v ↦ fieldInvStr (p v) (h v) (a v) :=
  Cobham.iteFn (Cobham.eqFlag_mem ha (cobham_fieldZeroStr_comp hh)) (cobham_fieldZeroStr_comp hh)
    (cobham_fieldPowStr_comp hp hh ha
      (cobham_subBits_comp (cobham_fieldCardStr_comp hp hh) (.const _)))

theorem finiteField_pow_card_sub_two {K : Type*} [Field K] [Fintype K] (x : K) (hx : x ≠ 0) :
    x ^ (Fintype.card K - 2) = x⁻¹ := by
  apply mul_right_cancel₀ hx
  rw [inv_mul_cancel₀ hx, ← pow_succ]
  have hd : Fintype.card K - 2 + 1 = Fintype.card K - 1 := by
    have := Fintype.one_lt_card (α := K)
    omega
  rw [hd, FiniteField.pow_card_sub_one_eq_one x hx]

theorem fieldInvStr_encoded (c : FieldCode) [Fact c.Valid] (x : c.Carrier) :
    fieldInvStr (encNat c.characteristic) (encodeNumerals c.modulus)
        (encodeNumerals (c.encodeElement x)) = encodeNumerals (c.encodeElement x⁻¹) := by
  unfold fieldInvStr
  rw [fieldZeroStr_encoded]
  by_cases hx : x = 0
  · subst x
    rw [SparseDiv.StringArith.eqFlag_self]
    simp
  · have hc : encodeNumerals (c.encodeElement x) ≠ encodeNumerals (c.encodeElement 0) :=
      fun h ↦ hx (c.scalar_encoding_injective h)
    have hflag : Cobham.eqFlag (encodeNumerals (c.encodeElement x))
        (encodeNumerals (c.encodeElement 0)) = [false] := by
      rcases Cobham.eqFlag_flag (encodeNumerals (c.encodeElement x))
        (encodeNumerals (c.encodeElement 0)) with h | h
      · exact (hc ((Cobham.eqFlag_eq_true_iff _ _).mp h)).elim
      · exact h
    rw [hflag, caseBit₀_cons, Bool.cond_false, fieldCardStr_encoded,
      fieldPowStr_encoded, decNat_subBits, decNat_encNat, decNat_encNat,
      finiteField_pow_card_sub_two x hx]

end SparseIrred.UpperBounds.Section4
