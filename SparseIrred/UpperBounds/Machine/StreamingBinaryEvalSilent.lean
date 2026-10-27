import SparseIrred.UpperBounds.Machine.StreamingBinaryEval
import SparseIrred.UpperBounds.Machine.StreamingBinaryArithmeticSilent

/-! # The sparse evaluation core never appends intermediate output -/

namespace SparseIrred.UpperBounds.Machine

open Complexity BinaryRoutine

theorem binaryEvalLoadTerm_silent : RoutineSilent binaryEvalLoadTerm := by
  apply (routineSilent_clearRegisters _).seq
  intro v
  simp [seqList, seq, binaryCopy, identity, emitBits]

theorem binaryEvalStoreTerm_silent : RoutineSilent binaryEvalStoreTerm :=
  ((routineSilent_copy _ _ _).seq (routineSilent_copy _ _ _)).seq
    (routineSilent_clearRegisters _)

theorem binaryEvalTermStep_silent (deriv : Bool) : RoutineSilent (binaryEvalTermStep deriv) :=
  binaryEvalLoadTerm_silent.seq ((binarySignedEvalTerm_silent deriv).seq binaryEvalStoreTerm_silent)

theorem binaryEvalInit_silent : RoutineSilent binaryEvalInit :=
  (routineSilent_clearRegisters _).seq (routineSilent_copy _ _ _)

theorem binaryEvalProbe_silent : RoutineSilent binaryEvalProbe :=
  (routineSilent_clear _).seq ((routineSilent_copy _ _ _).seq (routineSilent_pred _))

theorem binaryEvalEqualityLoad_silent : RoutineSilent binaryEvalEqualityLoad :=
  (routineSilent_clear _).seq ((routineSilent_copy _ _ _).seq (routineSilent_copy _ _ _))

theorem binaryEvalFinish_silent : RoutineSilent binaryEvalFinish :=
  (binaryEvalEqualityLoad_silent.seq binaryEq70_silent).seq (routineSilent_copy _ _ _)

theorem binarySparseEvalBody_silent (deriv : Bool) : RoutineSilent (binarySparseEvalBody deriv) :=
  binaryEvalProbe_silent.seq
    (routineSilent_identity.branchZero (parseTerm70_silent.seq (binaryEvalTermStep_silent deriv)) _)

theorem binarySparseEval_silent (deriv : Bool) : RoutineSilent (binarySparseEval deriv) :=
  binaryEvalInit_silent.seq
    (((binarySparseEvalBody_silent deriv).binaryFor 21 22).seq binaryEvalFinish_silent)

end SparseIrred.UpperBounds.Machine
