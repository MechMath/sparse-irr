import SparseIrred.UpperBounds.Section4.BinaryAddressPrime
import SparseIrred.UpperBounds.Section4.BinaryControl
import SparseIrred.UpperBounds.Section4.BinaryFieldPrimeCanonical
import SparseIrred.UpperBounds.Section4.BinaryInputValidation
import SparseIrred.UpperBounds.Section4.BinaryInputView

/-! # The fully implemented trial-division and syntax-validation stage -/

namespace SparseIrred.UpperBounds.Section4

open Complexity SparseDiv SparseDiv.StringArith

def binaryFirstInitial (s : List Bool) : List Bool :=
  binaryEval (binaryOrRange (encNat 0) (binaryInputPrime s)) [false]

def binaryFirstAdvanceStack (s cfg : List Bool) : List Bool :=
  binaryStackStep (primeInstructionStr (binaryInputPrime s))
    (binaryDecisionAdd (primeAddStr (encNat 2)))
    (binaryDecisionMul (primeMulStr (encNat 2)) isZeroBits) cfg

def binaryFirstAccept (s value : List Bool) : List Bool :=
  andBit (preflightStructuralStr s) (notBit (binaryDecisionAsBool value))

theorem cobham_binaryFirstInitial {n : ℕ} {s : (Fin n → List Bool) → List Bool}
    (hs : Cobham s) : Cobham fun v ↦ binaryFirstInitial (s v) :=
  cobham_binaryEval (cobham_binaryOrRange (.const (encNat 0)) (cobham_binaryInputPrime hs)) (.const [false])

theorem cobham_binaryFirstAdvanceStack {n : ℕ} {s c : (Fin n → List Bool) → List Bool}
    (hs : Cobham s) (hc : Cobham c) : Cobham fun v ↦ binaryFirstAdvanceStack (s v) (c v) := by
  apply cobham_binaryStackStep (n := n)
    (instruction := fun v ↦ primeInstructionStr (binaryInputPrime (s v)))
    (add := fun _ ↦ binaryDecisionAdd (primeAddStr (encNat 2)))
    (mul := fun _ ↦ binaryDecisionMul (primeMulStr (encNat 2)) isZeroBits)
  · have hst : Cobham fun u : Fin (n + 1) → List Bool ↦ s (Fin.tail u) :=
      (Cobham.comp hs (fun i ↦ .proj i.succ)).of_eq (fun _ ↦ rfl)
    exact cobham_primeInstructionStr (cobham_binaryInputPrime hst) (.proj 0)
  · apply cobham_binaryDecisionAdd
    · exact cobham_primeAddStr_comp (.const (encNat 2)) (.proj 0) (.proj 1)
    · exact .proj 0
    · exact .proj 1
  · apply cobham_binaryDecisionMul
    · exact cobham_primeMulStr_comp (.const (encNat 2)) (.proj 0) (.proj 1)
    · exact cobham_isZeroBits_comp (.proj 0)
    · exact .proj 0
    · exact .proj 1
  · exact hc

theorem cobham_binaryFirstAccept {n : ℕ} {s v : (Fin n → List Bool) → List Bool}
    (hs : Cobham s) (hv : Cobham v) : Cobham fun u ↦ binaryFirstAccept (s u) (v u) :=
  Cobham.andFn (cobham_preflightStructuralStr hs) (Cobham.notFn (cobham_binaryDecisionAsBool hv))

/-- All preflight operations, including trial-division instructions, are actual binary functions. -/
def firstStageRoutines : BinaryStageRoutines where
  initial := binaryFirstInitial
  advance := binaryFirstAdvanceStack
  accept := binaryFirstAccept
  initial_cobham := cobham_binaryFirstInitial (.proj 0)
  advance_cobham := cobham_binaryFirstAdvanceStack (.proj 0) (.proj 1)
  accept_cobham := cobham_binaryFirstAccept (.proj 0) (.proj 1)

theorem binaryFirstInitial_correct (s : List Bool) :
    binaryFirstInitial s =
      (EntryConfig.eval (primeDivisorInitial (Input.decode s).field.characteristic) []).framedEncode
        (primeAddressCode (Input.decode s).field.characteristic)
        (DecisionScalar.binaryCode (fun a : ZMod 2 ↦ encNat a.val)) := by
  simp [binaryFirstInitial, binaryInputPrime_eq, binaryEval, primeDivisorInitial,
    primeAddressCode, OrAddress.binaryCode, EntryConfig.framedEncode, encodeFramedStack,
    binaryOrRange, ← binaryFields_encNat]

theorem binaryFirstAdvanceStack_correct (s : List Bool)
    (c : EntryConfig (PrimeAddress (Input.decode s).field.characteristic) (DecisionScalar (ZMod 2))) :
    binaryFirstAdvanceStack s (c.framedEncode (primeAddressCode (Input.decode s).field.characteristic)
      (DecisionScalar.binaryCode (fun a : ZMod 2 ↦ encNat a.val))) =
      ((primeDivisorProgram (Input.decode s).field.characteristic).step c).framedEncode
        (primeAddressCode (Input.decode s).field.characteristic)
        (DecisionScalar.binaryCode (fun a : ZMod 2 ↦ encNat a.val)) := by
  rw [binaryFirstAdvanceStack, binaryInputPrime_eq]
  apply binaryStackStep_correct
  · exact primeInstructionStr_eq _
  · exact binaryDecisionAdd_correct _ _ (primeAddStr_encoded 2)
  · exact binaryDecisionMul_correct _ _ _ (primeMulStr_encoded 2) (isZeroBits_encNat_zmod_val 2)

theorem binaryFirstAccept_correct (s : List Bool) (v : DecisionScalar (ZMod 2)) :
    binaryFirstAccept s (v.binaryCode (fun a : ZMod 2 ↦ encNat a.val)) = [preflightOutput s v] := by
  rw [binaryFirstAccept, preflightStructuralStr_correct, binaryDecisionAsBool_correct]
  cases h : v.asBool <;> simp [preflightOutput, notBit, caseBit₀, andBit_single, h]

end SparseIrred.UpperBounds.Section4
