import SparseIrred.UpperBounds.Section4.BinaryPrimePolynomial

/-! # Polynomial-time preflight and coefficient-vector validation on all raw inputs -/

namespace SparseIrred.UpperBounds.Section4

open Complexity SparseDiv SparseDiv.StringArith

def preflightStructuralStr (s : List Bool) : List Bool :=
  andBit (canonicalInputFlag s)
    (structuralHeaderStr (inputPrimeStr s) (canonicalNumeralsStr (inputModulusStr s)))

theorem cobham_preflightStructuralStr {n : ℕ} {s : (Fin n → List Bool) → List Bool}
    (hs : Cobham s) : Cobham fun v ↦ preflightStructuralStr (s v) :=
  Cobham.andFn (cobham_canonicalInputFlag hs)
    (cobham_structuralHeaderStr (cobham_canonBits_comp (cobham_pairFst_comp hs))
      (cobham_canonicalNumeralsStr (cobham_pairFst_comp (cobham_pairSnd_comp hs))))

theorem canonicalInputFlag_eq (s : List Bool) :
    canonicalInputFlag s = [decide ((Input.decode s).encode = s)] := by
  rcases Cobham.eqFlag_flag (canonicalInputStr s) s with h | h
  · change canonicalInputFlag s = [true] at h
    have he := (canonicalInputFlag_correct s).mp h
    simpa only [he, decide_true] using h
  · have he : (Input.decode s).encode ≠ s := by
      intro he
      have ht := (canonicalInputFlag_correct s).mpr he
      change Cobham.eqFlag (canonicalInputStr s) s = [true] at ht
      rw [h] at ht
      contradiction
    change canonicalInputFlag s = [false] at h
    simpa only [he, decide_false] using h

theorem preflightStructuralStr_correct (s : List Bool) :
    preflightStructuralStr s =
      [decide ((Input.decode s).encode = s) && (Input.decode s).field.structuralFlag] := by
  rw [preflightStructuralStr, canonicalInputFlag_eq]
  have hp : inputPrimeStr s = encNat (Input.decode s).field.characteristic := rfl
  have hm : canonicalNumeralsStr (inputModulusStr s) =
      encodeNumerals (Input.decode s).field.modulus := by
    simp only [canonicalNumeralsStr, mapBlocks, inputModulusStr, Input.decode,
      encodeNumerals, decodeNumerals, List.map_map, Function.comp_def]
    rfl
  rw [hp, hm, structuralHeaderStr_correct, andBit_single]

def coefficientShapeStr (p degree coefficient : List Bool) : List Bool :=
  andBit (binaryEq (blockCountStr coefficient) degree [true] [false])
    (allDigitsBelowStr p coefficient)

theorem cobham_coefficientShapeStr {n : ℕ}
    {p d a : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (hd : Cobham d) (ha : Cobham a) :
    Cobham fun v ↦ coefficientShapeStr (p v) (d v) (a v) :=
  Cobham.andFn (cobham_binaryEq (cobham_blockCountStr ha) hd (.const _) (.const _))
    (cobham_allDigitsBelowStr hp ha)

theorem coefficientShapeStr_encoded (p d : ℕ) (a : List ℕ) :
    coefficientShapeStr (encNat p) (encNat d) (encodeNumerals a) =
      [decide (a.length = d) && a.all (fun b ↦ decide (b < p))] := by
  unfold coefficientShapeStr
  rw [show blockCountStr (encodeNumerals a) = encNat a.length by
    simp [encodeNumerals, blockCountStr_frame]]
  rw [allDigitsBelowStr_frame]
  by_cases he : a.length = d <;> simp [binaryEq, andBit_single, he]

def coefficientCanonicalStr (s : List Bool) : List Bool :=
  let canonical := canonicalInputStr s
  allBlocksStr (fun term ↦ coefficientShapeStr (inputPrimeStr canonical)
    (primePolynomialDegreeStr (inputModulusStr canonical)) (pairFst term))
    (inputTermsStr canonical)

theorem cobham_coefficientCanonicalStr {n : ℕ} {s : (Fin n → List Bool) → List Bool}
    (hs : Cobham s) : Cobham fun v ↦ coefficientCanonicalStr (s v) := by
  unfold coefficientCanonicalStr
  dsimp only
  have hcore : Cobham fun v : Fin 3 → List Bool ↦
      allBlocksStr (fun term ↦ coefficientShapeStr (v 0) (v 1) (pairFst term)) (v 2) := by
    apply cobham_allBlocksStr
      (test := fun v : Fin 3 → List Bool ↦ fun term ↦
        coefficientShapeStr (v 0) (v 1) (pairFst term))
      (s := fun v : Fin 3 → List Bool ↦ v 2) _ (.proj 2)
    exact cobham_coefficientShapeStr (.proj 1) (.proj 2) (cobham_pairFst_comp (.proj 0))
  have hc := cobham_canonicalInputStr hs
  have hp : Cobham fun v ↦ inputPrimeStr (canonicalInputStr (s v)) :=
    cobham_canonBits_comp (cobham_pairFst_comp hc)
  have hd : Cobham fun v ↦ primePolynomialDegreeStr (inputModulusStr (canonicalInputStr (s v))) :=
    cobham_primePolynomialDegreeStr (cobham_pairFst_comp (cobham_pairSnd_comp hc))
  have ht : Cobham fun v ↦ inputTermsStr (canonicalInputStr (s v)) :=
    cobham_pairSnd_comp (cobham_pairSnd_comp hc)
  convert Cobham.comp₃ hcore hp hd ht using 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  rfl

/-- The main-stage shape check agrees with canonical coefficient-vector validity
even on raw strings, after only the inexpensive structural header condition. -/
theorem coefficientCanonicalStr_correct (s : List Bool)
    (hc : (Input.decode s).field.Structural) :
    coefficientCanonicalStr s = [true] ↔
      ∀ t ∈ (Input.decode s).terms, (Input.decode s).field.CanonicalElement t.1 := by
  unfold coefficientCanonicalStr
  rw [canonicalInputStr_eq]
  let x := Input.decode s
  change allBlocksStr (fun term ↦ coefficientShapeStr (inputPrimeStr x.encode)
    (primePolynomialDegreeStr (inputModulusStr x.encode)) (pairFst term))
    (inputTermsStr x.encode) = [true] ↔ _
  have hp : inputPrimeStr x.encode = encNat x.field.characteristic := by
    simp [inputPrimeStr, Input.encode, canonBits]
  have hm : inputModulusStr x.encode = encodeNumerals x.field.modulus := by
    simp [inputModulusStr, Input.encode]
  have ht : inputTermsStr x.encode = frame (x.terms.map encodeTerm) := by
    simp [inputTermsStr, Input.encode]
  rw [hp, hm, ht, primePolynomialDegreeStr_correct _ hc, allBlocksStr_frame]
  simp only [List.cons.injEq, and_true, List.all_map]
  rw [List.all_eq_true]
  constructor
  · intro h t ht
    have hh := h t ht
    simp only [Function.comp_def, encodeTerm, pairFst_pair, coefficientShapeStr_encoded,
      List.headD_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hh
    exact hh
  · intro h t ht
    have hh := h t ht
    simp only [Function.comp_def, encodeTerm, pairFst_pair, coefficientShapeStr_encoded,
      List.headD_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    exact hh

theorem coefficientCanonicalStr_flag (s : List Bool) :
    ∃ b : Bool, coefficientCanonicalStr s = [b] := by
  unfold coefficientCanonicalStr
  dsimp only
  let test := fun term ↦ coefficientShapeStr (inputPrimeStr (canonicalInputStr s))
    (primePolynomialDegreeStr (inputModulusStr (canonicalInputStr s))) (pairFst term)
  let ts := inputTermsStr (canonicalInputStr s)
  have he : allBlocksStr test ts = allBlocksStr test (frame (blocks ts)) := by
    simp [allBlocksStr, foldBlocks, blocks_frame]
  change ∃ b, allBlocksStr test ts = [b]
  rw [he, allBlocksStr_frame]
  exact ⟨_, rfl⟩

theorem coefficientCanonicalStr_eq_decide (s : List Bool)
    (hc : (Input.decode s).field.Structural)
    [Decidable (∀ t ∈ (Input.decode s).terms, (Input.decode s).field.CanonicalElement t.1)] :
    coefficientCanonicalStr s =
      [decide (∀ t ∈ (Input.decode s).terms, (Input.decode s).field.CanonicalElement t.1)] := by
  obtain ⟨b, hb⟩ := coefficientCanonicalStr_flag s
  rw [hb]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simpa only [hb, List.cons.injEq, and_true, decide_eq_true_eq] using
    coefficientCanonicalStr_correct s hc

end SparseIrred.UpperBounds.Section4
