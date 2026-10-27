import SparseIrred.UpperBounds.Machine.StreamingBinaryInputFrameLoop
import SparseIrred.UpperBounds.Machine.StreamingBinaryInputSilent

/-! # Framed input decoding emits no output bits -/
namespace SparseIrred.UpperBounds.Machine
open Complexity BinaryRoutine

theorem frameInputReadPair_silent (k : ℕ) : RoutineSilent (frameInputReadPair k) :=
  (inputReadBit_silent _).seq ((routineSilent_copy _ _ _).seq (inputReadBit_silent _))

theorem frameInputAddPower_silent (k : ℕ) : RoutineSilent (frameInputAddPower k) :=
  routineSilent_add _ _ _

theorem frameInputDoublePower_silent (k : ℕ) : RoutineSilent (frameInputDoublePower k) :=
  (routineSilent_copy _ _ _).seq ((routineSilent_add _ _ _).seq (routineSilent_clear _))

theorem frameInputProcess_silent (k : ℕ) : RoutineSilent (frameInputProcess k) :=
  ((frameInputDoublePower_silent k).branchZero (routineSilent_set _ _) _).branchZero
    ((frameInputAddPower_silent k).seq (frameInputDoublePower_silent k)) _

theorem frameInputBody_silent (k : ℕ) : RoutineSilent (frameInputBody k) :=
  ((frameInputReadPair_silent k).seq ((frameInputProcess_silent k).seq
    ((routineSilent_clear _).seq (routineSilent_clear _)))).branchZero routineSilent_identity _

theorem frameInputLoop_silent (k : ℕ) : RoutineSilent (frameInputLoop k) :=
  (frameInputBody_silent k).binaryFor _ _

theorem frameInputClear_silent (k : ℕ) : RoutineSilent (frameInputClear k) := by
  apply (inputReadReset_silent _).seq
  exact (routineSilent_clear _).seq ((routineSilent_clear _).seq
    ((routineSilent_clear _).seq ((routineSilent_clear _).seq
      ((routineSilent_clear _).seq ((routineSilent_clear _).seq
        ((routineSilent_clear _).seq ((routineSilent_clear _).seq routineSilent_identity)))))))

theorem frameInputInit_silent (k : ℕ) : RoutineSilent (frameInputInit k) :=
  (frameInputClear_silent k).seq ((routineSilent_set _ _).seq (routineSilent_copy _ _ _))

theorem frameInput_silent (k : ℕ) : RoutineSilent (frameInput k) :=
  (frameInputInit_silent k).seq (frameInputLoop_silent k)

end SparseIrred.UpperBounds.Machine
