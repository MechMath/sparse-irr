import SparseIrred.UpperBounds.Section4.BinaryAddressPolynomial
import SparseIrred.UpperBounds.Section4.BinarySparseMetadata
import SparseIrred.UpperBounds.Section4.BinaryMatrixEntries
import SparseIrred.UpperBounds.Section4.BinaryControl
import SparseIrred.UpperBounds.Section4.BinaryInputView
import SparseIrred.UpperBounds.Section4.BinaryInputValidation

/-! # The final stage, implemented entirely by verified binary routines -/

namespace SparseIrred.UpperBounds.Section4

open Polynomial Complexity SparseDiv SparseDiv.StringArith

set_option backward.isDefEq.respectTransparency false

def extensionSylvesterStr (p h terms query : List Bool) : List Bool :=
  sylvesterEntryStr (sparseCoefficientStr p h terms) (sparseDerivativeCoefficientStr p h terms)
    (sparseDegreeStr false p h terms) (sparseDegreeStr true p h terms) (fieldZeroStr h) query

def extensionCompanionStr (p h terms query : List Bool) : List Bool :=
  companionEntryStr (sparseCoefficientStr p h terms) (fieldMulStr p h) (fieldNegStr p h)
    (sparseDegreeStr false p h terms) (sparseLeadingInverseStr p h terms)
    (fieldZeroStr h) (fieldOneStr p h) query

def extensionInstructionStr (p h terms addr : List Bool) : List Bool :=
  polynomialInstructionStr (extensionSylvesterStr p h terms) (extensionCompanionStr p h terms)
    (sparseDegreeStr false p h terms) (sparseDegreeStr true p h terms)
    (fieldCardStr p h) (fieldZeroStr h) (fieldOneStr p h)
    (fieldNegStr p h (fieldOneStr p h)) addr

theorem cobham_extensionSylvesterStr {n : ℕ} {p h t q : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (hh : Cobham h) (ht : Cobham t) (hq : Cobham q) :
    Cobham fun u ↦ extensionSylvesterStr (p u) (h u) (t u) (q u) :=
  cobham_sylvesterEntryStr
    (fun _ hi ↦ cobham_sparseCoefficientStr_comp hp hh ht hi)
    (fun _ hi ↦ cobham_sparseDerivativeCoefficientStr hp hh ht hi)
    (cobham_sparseDegreeStr false hp hh ht) (cobham_sparseDegreeStr true hp hh ht)
    (cobham_fieldZeroStr_comp hh) hq

theorem cobham_extensionCompanionStr {n : ℕ} {p h t q : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (hh : Cobham h) (ht : Cobham t) (hq : Cobham q) :
    Cobham fun u ↦ extensionCompanionStr (p u) (h u) (t u) (q u) :=
  cobham_companionEntryStr
    (fun _ hi ↦ cobham_sparseCoefficientStr_comp hp hh ht hi)
    (fun _ _ ha hb ↦ cobham_fieldMulStr_comp hp hh ha hb)
    (fun _ ha ↦ cobham_fieldNegStr_comp hp hh ha)
    (cobham_sparseDegreeStr false hp hh ht) (cobham_sparseLeadingInverseStr hp hh ht)
    (cobham_fieldZeroStr_comp hh) (cobham_fieldOneStr_comp hp hh) hq

theorem cobham_extensionInstructionStr {n : ℕ} {p h t a : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (hh : Cobham h) (ht : Cobham t) (ha : Cobham a) :
    Cobham fun u ↦ extensionInstructionStr (p u) (h u) (t u) (a u) :=
  cobham_polynomialInstructionStr
    (fun _ hq ↦ cobham_extensionSylvesterStr hp hh ht hq)
    (fun _ hq ↦ cobham_extensionCompanionStr hp hh ht hq)
    (cobham_sparseDegreeStr false hp hh ht) (cobham_sparseDegreeStr true hp hh ht)
    (cobham_fieldCardStr_comp hp hh) (cobham_fieldZeroStr_comp hh)
    (cobham_fieldOneStr_comp hp hh)
    (cobham_fieldNegStr_comp hp hh (cobham_fieldOneStr_comp hp hh)) ha

theorem extensionSylvesterStr_encoded (c : FieldCode) [Fact c.Valid] [DecidableEq c.Carrier]
    (ts : SparseTerms) (i j : ℕ) :
    extensionSylvesterStr (encNat c.characteristic) (encodeNumerals c.modulus)
      (frame (ts.map encodeTerm)) (pair (encNat i) (encNat j)) =
      c.scalarCode (coefficientSylvesterEntry (c.sparsePolynomial ts) i j) := by
  simp only [extensionSylvesterStr, sparseDegreeStr_encoded, Bool.false_eq_true, ↓reduceIte,
    fieldZeroStr_encoded]
  exact sylvesterEntryStr_correct _ c.scalarCode _ _
    (sparseCoefficientStr_encoded c ts) (sparseDerivativeCoefficientStr_encoded c ts) i j

theorem extensionCompanionStr_encoded (c : FieldCode) [Fact c.Valid] [DecidableEq c.Carrier]
    (ts : SparseTerms) (i j : Fin (c.sparsePolynomial ts).natDegree) :
    extensionCompanionStr (encNat c.characteristic) (encodeNumerals c.modulus)
      (frame (ts.map encodeTerm)) (pair (encNat i.val) (encNat j.val)) =
      c.scalarCode (coefficientCompanion (c.sparsePolynomial ts) i j) := by
  simp only [extensionCompanionStr, sparseDegreeStr_encoded, Bool.false_eq_true, ↓reduceIte,
    sparseLeadingInverseStr_encoded, fieldZeroStr_encoded, fieldOneStr_encoded]
  exact companionEntryStr_correct _ c.scalarCode _ _ _
    (sparseCoefficientStr_encoded c ts) (fieldMulStr_encoded c) (fieldNegStr_encoded c) i j

theorem extensionInstructionStr_encoded (c : FieldCode) [Fact c.Valid] [DecidableEq c.Carrier]
    (ts : SparseTerms)
    (a : PolynomialAddress (c.sparsePolynomial ts).natDegree (c.sparsePolynomial ts).derivative.natDegree) :
    extensionInstructionStr (encNat c.characteristic) (encodeNumerals c.modulus)
      (frame (ts.map encodeTerm)) (polynomialAddressCode _ _ a) =
      ((polynomialProgram (c.sparsePolynomial ts)).instruction a).binaryCode
        (polynomialAddressCode _ _) (DecisionScalar.binaryCode c.scalarCode) := by
  simp only [extensionInstructionStr, sparseDegreeStr_encoded, Bool.false_eq_true, ↓reduceIte,
    fieldCardStr_encoded, fieldZeroStr_encoded, fieldOneStr_encoded, fieldNegStr_encoded]
  refine polynomialInstructionStr_eq (c.sparsePolynomial ts) c.scalarCode
    (extensionSylvesterStr (encNat c.characteristic) (encodeNumerals c.modulus) (frame (ts.map encodeTerm)))
    (extensionCompanionStr (encNat c.characteristic) (encodeNumerals c.modulus) (frame (ts.map encodeTerm)))
    ?_ ?_ a
  · intro i j
    exact extensionSylvesterStr_encoded c ts i.val j.val
  · exact extensionCompanionStr_encoded c ts

def extensionAdvanceStr (p h terms cfg : List Bool) : List Bool :=
  binaryStackStep (extensionInstructionStr p h terms)
    (binaryDecisionAdd (fieldAddStr p h))
    (binaryDecisionMul (fieldMulStr p h) (fieldZeroFlagStr h)) cfg

theorem cobham_extensionAdvanceStr {n : ℕ} {p h t c : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (hh : Cobham h) (ht : Cobham t) (hc : Cobham c) :
    Cobham fun u ↦ extensionAdvanceStr (p u) (h u) (t u) (c u) := by
  have lift {m : ℕ} {f : (Fin n → List Bool) → List Bool} (hf : Cobham f)
      (v : Fin n → Fin m) : Cobham fun u : Fin m → List Bool ↦ f (fun i ↦ u (v i)) :=
    (Cobham.comp hf (fun i ↦ Cobham.proj (v i))).of_eq (fun _ ↦ rfl)
  apply cobham_binaryStackStep (n := n)
    (instruction := fun u ↦ extensionInstructionStr (p u) (h u) (t u))
    (add := fun u ↦ binaryDecisionAdd (fieldAddStr (p u) (h u)))
    (mul := fun u ↦ binaryDecisionMul (fieldMulStr (p u) (h u)) (fieldZeroFlagStr (h u)))
  · exact cobham_extensionInstructionStr (lift hp Fin.succ) (lift hh Fin.succ)
      (lift ht Fin.succ) (.proj 0)
  · apply cobham_binaryDecisionAdd
    · exact cobham_fieldAddStr_comp (lift hp (fun i ↦ i.succ.succ.succ.succ))
        (lift hh (fun i ↦ i.succ.succ.succ.succ)) (.proj 0) (.proj 1)
    · exact .proj 0
    · exact .proj 1
  · apply cobham_binaryDecisionMul
    · exact cobham_fieldMulStr_comp (lift hp (fun i ↦ i.succ.succ.succ.succ))
        (lift hh (fun i ↦ i.succ.succ.succ.succ)) (.proj 0) (.proj 1)
    · exact cobham_fieldZeroFlagStr_comp (lift hh (fun i ↦ i.succ.succ.succ)) (.proj 0)
    · exact .proj 0
    · exact .proj 1
  · exact hc

theorem extensionAdvanceStr_encoded (c : FieldCode) [Fact c.Valid] [DecidableEq c.Carrier]
    (ts : SparseTerms) (cfg : EntryConfig
      (PolynomialAddress (c.sparsePolynomial ts).natDegree (c.sparsePolynomial ts).derivative.natDegree)
      (DecisionScalar c.Carrier)) :
    extensionAdvanceStr (encNat c.characteristic) (encodeNumerals c.modulus)
      (frame (ts.map encodeTerm)) (cfg.framedEncode (polynomialAddressCode _ _)
        (DecisionScalar.binaryCode c.scalarCode)) =
      ((polynomialProgram (c.sparsePolynomial ts)).step cfg).framedEncode (polynomialAddressCode _ _)
        (DecisionScalar.binaryCode c.scalarCode) := by
  apply binaryStackStep_correct
  · exact extensionInstructionStr_encoded c ts
  · exact binaryDecisionAdd_correct c.scalarCode _ (fieldAddStr_encoded c)
  · exact binaryDecisionMul_correct c.scalarCode _ _ (fieldMulStr_encoded c)
      (fieldZeroFlagStr_encoded c)

def binaryExtensionStage : BinaryStageRoutines where
  initial _ := binaryEval [true, false, false] [false]
  advance s cfg := extensionAdvanceStr (binaryInputPrime s) (binaryInputModulus s) (binaryInputTerms s) cfg
  accept s v := andBit (coefficientCanonicalStr s) (binaryDecisionAsBool v)
  initial_cobham := .const _
  advance_cobham := cobham_extensionAdvanceStr (cobham_binaryInputPrime (.proj 0))
    (cobham_binaryInputModulus (.proj 0)) (cobham_binaryInputTerms (.proj 0)) (.proj 1)
  accept_cobham := Cobham.andFn (cobham_coefficientCanonicalStr (.proj 0))
    (cobham_binaryDecisionAsBool (.proj 1))

/-- Every final-stage binary operation now has an implementation and a proof;
there is no local-step implementation premise in this realization theorem. -/
theorem binaryExtensionStage_realization (s : List Bool) (h : (primeStage s).answer = true)
    (h' : (modulusStage s h).answer = true) :
    BinaryStageRealization s binaryExtensionStage (sparseStage s h h') (sparseConfigCode s h h') := by
  classical
  let c := (Input.decode s).field
  let ts := (Input.decode s).terms
  letI : Fact c.Valid := ⟨validFieldOfStages s h h'⟩
  apply binaryStageRealization_of_encoded s binaryExtensionStage (sparseStage s h h')
    (polynomialAddressCode _ _) (DecisionScalar.binaryCode c.scalarCode)
  · rfl
  · intro cfg
    change extensionAdvanceStr (binaryInputPrime s) (binaryInputModulus s) (binaryInputTerms s)
      (cfg.framedEncode (polynomialAddressCode _ _) (DecisionScalar.binaryCode c.scalarCode)) = _
    rw [binaryInputPrime_eq, binaryInputModulus_eq, binaryInputTerms_eq]
    exact extensionAdvanceStr_encoded c ts cfg
  · intro v
    change andBit (coefficientCanonicalStr s) (binaryDecisionAsBool (v.binaryCode c.scalarCode)) =
      [decide (∀ t ∈ ts, c.CanonicalElement t.1) && v.asBool]
    rw [binaryDecisionAsBool_correct, coefficientCanonicalStr_eq_decide s
      (validFieldOfStages s h h').structural, andBit_single]

end SparseIrred.UpperBounds.Section4
