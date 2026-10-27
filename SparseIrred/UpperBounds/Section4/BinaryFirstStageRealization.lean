import SparseIrred.UpperBounds.Section4.BinaryFirstStage

/-! # Unconditional realization of the first uniform stage -/

namespace SparseIrred.UpperBounds.Section4

open Complexity SparseDiv

set_option backward.isDefEq.respectTransparency false

theorem firstStageRoutines_realization (s : List Bool) :
    BinaryStageRealization s firstStageRoutines (primeStage s) (primeConfigCode s) :=
  binaryStageRealization_of_encoded s firstStageRoutines (primeStage s)
    (primeAddressCode (Input.decode s).field.characteristic)
    (DecisionScalar.binaryCode (fun a : ZMod 2 ↦ encNat a.val))
    (binaryFirstInitial_correct s) (binaryFirstAdvanceStack_correct s) (binaryFirstAccept_correct s)

end SparseIrred.UpperBounds.Section4
