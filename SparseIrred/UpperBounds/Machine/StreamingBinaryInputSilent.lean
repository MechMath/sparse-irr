import SparseIrred.UpperBounds.Machine.StreamingBinaryInput
import SparseIrred.UpperBounds.Machine.StreamingBinaryUnpack
import SparseIrred.UpperBounds.Machine.StreamingBinarySilence

/-! # Bit readers and integer decoders do not emit output -/

namespace SparseIrred.UpperBounds.Machine
open Complexity BinaryRoutine

theorem inputDivTwoBody_silent (k : ℕ) : RoutineSilent (inputDivTwoBody k) :=
  (routineSilent_succ _).branchZero ((routineSilent_clear _).seq (routineSilent_succ _)) _

theorem inputDivTwoLoop_silent (k : ℕ) : RoutineSilent (inputDivTwoLoop k) :=
  (inputDivTwoBody_silent k).binaryFor _ _

theorem inputPopBit_silent (k : ℕ) : RoutineSilent (inputPopBit k) :=
  (inputDivTwoLoop_silent k).seq ((routineSilent_copy _ _ _).seq
    ((routineSilent_clear _).seq (routineSilent_clear _)))

theorem inputReadReset_silent (k : ℕ) : RoutineSilent (inputReadReset k) :=
  (routineSilent_clear _).seq ((routineSilent_clear _).seq
    ((routineSilent_clear _).seq (routineSilent_clear _)))

theorem inputReadBit_silent (k : ℕ) : RoutineSilent (inputReadBit k) :=
  (inputReadReset_silent k).seq (inputPopBit_silent k)

theorem unpackActive_silent : RoutineSilent unpackActive :=
  (inputReadBit_silent _).seq
    ((routineSilent_identity.branchZero (routineSilent_add _ _ _) _).seq
      ((routineSilent_copy _ _ _).seq ((routineSilent_add _ _ _).seq
        ((routineSilent_clear _).seq (routineSilent_clear _)))))

theorem unpackBody_silent : RoutineSilent unpackBody :=
  (routineSilent_copy _ _ _).seq ((routineSilent_pred _).seq
    ((routineSilent_identity.branchZero unpackActive_silent _).seq (routineSilent_clear _)))

theorem unpackLoop_silent : RoutineSilent unpackLoop := unpackBody_silent.binaryFor _ _

theorem unpackInit_silent : RoutineSilent unpackInit :=
  (routineSilent_clearRegisters _).seq
    ((routineSilent_set _ _).seq (routineSilent_copy _ _ _))

theorem unpackInput_silent : RoutineSilent unpackInput := unpackInit_silent.seq unpackLoop_silent

end SparseIrred.UpperBounds.Machine
