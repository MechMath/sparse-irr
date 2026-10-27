import SparseIrred.UpperBounds.Machine.StreamingBinarySilence
import SparseIrred.UpperBounds.Machine.StreamingBinaryMod
import SparseIrred.UpperBounds.Machine.StreamingBinaryTerm
import SparseIrred.UpperBounds.Machine.StreamingBinaryCompare
import SparseIrred.UpperBounds.Machine.StreamingBinaryCore
import SparseIrred.UpperBounds.Machine.StreamingBinaryEvalDerivative

/-! # All arithmetic and enumeration subroutines preserve the output stream -/

namespace SparseIrred.UpperBounds.Machine

open Complexity BinaryRoutine

theorem binaryModReset_silent : RoutineSilent binaryModReset :=
  ((routineSilent_copy _ _ _).seq (routineSilent_pred _)).seq (routineSilent_clear _)
theorem binaryModBody_silent : RoutineSilent binaryModBody :=
  binaryModReset_silent.branchZero ((routineSilent_pred _).seq (routineSilent_succ _)) _
theorem binaryModLoop_silent : RoutineSilent binaryModLoop := binaryModBody_silent.binaryFor _ _

theorem framedModReset_silent (k : ℕ) : RoutineSilent (framedModReset k) :=
  ((routineSilent_copy _ _ _).seq (routineSilent_pred _)).seq (routineSilent_clear _)
theorem framedModBody_silent (k : ℕ) : RoutineSilent (framedModBody k) :=
  (framedModReset_silent k).branchZero ((routineSilent_pred _).seq (routineSilent_succ _)) _
theorem framedModLoop_silent (k : ℕ) : RoutineSilent (framedModLoop k) :=
  (framedModBody_silent k).binaryFor _ _
theorem framedModInit_silent (k : ℕ) : RoutineSilent (framedModInit k) :=
  ((routineSilent_clear _).seq (routineSilent_clear _)).seq
    ((routineSilent_copy _ _ _).seq (routineSilent_pred _))
theorem framedMod_silent (k : ℕ) : RoutineSilent (framedMod k) :=
  (framedModInit_silent k).seq (framedModLoop_silent k)

theorem binaryPowClean_silent (k : ℕ) : RoutineSilent (binaryPowClean k) :=
  ((routineSilent_clear _).seq (routineSilent_clear _)).seq (routineSilent_clear _)
theorem binaryPowBody_silent (k : ℕ) : RoutineSilent (binaryPowBody k) :=
  ((routineSilent_mulAdd _ _ _ _ _).seq (framedMod_silent _)).seq (binaryPowClean_silent _)
theorem binaryPowLoop_silent (k : ℕ) : RoutineSilent (binaryPowLoop k) :=
  (binaryPowBody_silent k).binaryFor _ _
theorem binaryPowInit_silent (k : ℕ) : RoutineSilent (binaryPowInit k) :=
  ((routineSilent_set _ _).seq (framedMod_silent _)).seq
    ((binaryPowClean_silent _).seq (routineSilent_clear _))
theorem binaryPow_silent (k : ℕ) : RoutineSilent (binaryPow k) :=
  (binaryPowInit_silent k).seq (binaryPowLoop_silent k)

theorem binaryTermFinish_silent (k : ℕ) : RoutineSilent (binaryTermFinish k) :=
  ((routineSilent_mulAdd _ _ _ _ _).seq (framedMod_silent _)).seq (binaryPowClean_silent _)
theorem binaryTerm_silent (k : ℕ) : RoutineSilent (binaryTerm k) :=
  (binaryPow_silent _).seq (binaryTermFinish_silent _)

theorem comparePred_silent : RoutineSilent comparePred :=
  routineSilent_identity.branchZero (routineSilent_pred _) _
theorem compareInit_silent (reverse : Bool) : RoutineSilent (compareInit reverse) :=
  (routineSilent_clear _).seq (routineSilent_copy _ _ _)
theorem compareLoop_silent (reverse : Bool) : RoutineSilent (compareLoop reverse) :=
  comparePred_silent.binaryFor _ _
theorem compareFinish_silent : RoutineSilent compareFinish :=
  ((routineSilent_clear _).branchZero (routineSilent_set _ _) _).seq
    ((routineSilent_clear _).seq (routineSilent_clear _))
theorem binaryLtCore_silent (reverse : Bool) : RoutineSilent (binaryLtCore reverse) :=
  ((compareInit_silent reverse).seq (compareLoop_silent reverse)).seq compareFinish_silent
theorem binaryLt70_silent : RoutineSilent binaryLt70 := binaryLtCore_silent false
theorem compareInvert_silent : RoutineSilent compareInvert :=
  (routineSilent_set _ _).branchZero (routineSilent_clear _) _
theorem binaryEq70_silent : RoutineSilent binaryEq70 :=
  binaryLt70_silent.seq (((binaryLtCore_silent true).seq compareInvert_silent).branchZero
    (routineSilent_clear _) _)

theorem coreInner_silent {cell : BinaryRoutine 70} (h : RoutineSilent cell) :
    RoutineSilent (coreInner cell) := h.binaryFor _ _
theorem coreRow_silent {cell : BinaryRoutine 70} (h : RoutineSilent cell) :
    RoutineSilent (coreRow cell) := (coreInner_silent h).seq (routineSilent_clear _)
theorem coreEnumeration_silent {cell : BinaryRoutine 70} (h : RoutineSilent cell) :
    RoutineSilent (coreEnumeration cell) := (coreRow_silent h).binaryFor _ _

theorem binaryAccLoad_silent (negative : Bool) : RoutineSilent (binaryAccLoad negative) :=
  (routineSilent_copy _ _ _).seq (routineSilent_add _ _ _)
theorem binaryAccStore_silent (negative : Bool) : RoutineSilent (binaryAccStore negative) :=
  (routineSilent_copy _ _ _).seq ((routineSilent_clear _).seq ((routineSilent_clear _).seq
    ((routineSilent_clear _).seq (routineSilent_clear _))))
theorem binaryAccumulate_silent (negative : Bool) : RoutineSilent (binaryAccumulate negative) :=
  ((binaryAccLoad_silent negative).seq (framedMod_silent _)).seq (binaryAccStore_silent negative)
theorem binarySignedTerm_silent : RoutineSilent binarySignedTerm :=
  (binaryTerm_silent _).seq ((binaryAccumulate_silent false).branchZero
    (binaryAccumulate_silent true) _)
theorem binaryDerivativePrepare_silent : RoutineSilent binaryDerivativePrepare :=
  (routineSilent_mulAdd _ _ _ _ _).seq ((routineSilent_copy _ _ _).seq
    ((routineSilent_clear _).seq (routineSilent_pred _)))
theorem binarySignedDerivative_silent : RoutineSilent binarySignedDerivative :=
  routineSilent_identity.branchZero (binaryDerivativePrepare_silent.seq binarySignedTerm_silent) _
theorem binarySignedEvalTerm_silent (deriv : Bool) : RoutineSilent (binarySignedEvalTerm deriv) := by
  cases deriv
  · exact binarySignedTerm_silent
  · exact binarySignedDerivative_silent

end SparseIrred.UpperBounds.Machine
