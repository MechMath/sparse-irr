import SparseIrred.UpperBounds.Machine.StreamingBinaryEvalDerivative
import SparseIrred.UpperBounds.Machine.StreamingBinaryWorkspace

/-! # Workspace and register transfer routines for the sparse evaluator -/

set_option maxHeartbeats 1600000

namespace SparseIrred.UpperBounds.Machine

open Complexity BinaryRoutine

/-- Shared arithmetic workspace before an ordinary or derivative term call. -/
def evalArithmeticRegisters : List (Fin 70) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

/-- Disposable evaluation workspace; the cursor, modulus, base, accumulators,
and outer-loop controller occupy registers 16 through 22. -/
def evalDisposableRegisters : List (Fin 70) :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
   23, 24, 25, 26, 27, 28, 29, 30, 31]

/-- Copy the parsed term and persistent accumulators into the shared arithmetic workspace. -/
def binaryEvalLoadTerm : BinaryRoutine 70 :=
  seq (clearRegisters evalArithmeticRegisters)
    (seqList [binaryCopy 17 1 5, binaryCopy 18 6 5, binaryCopy 27 7 5,
      binaryCopy 26 9 5, binaryCopy 28 10 5, binaryCopy 19 11 5, binaryCopy 20 12 5])

/-- Return both residues to the persistent state and reuse all disposable work tapes. -/
def binaryEvalStoreTerm : BinaryRoutine 70 :=
  seq (seq (binaryCopy 11 19 5) (binaryCopy 12 20 5))
    (clearRegisters evalDisposableRegisters)

theorem binaryEvalLoadTerm_sound : binaryEvalLoadTerm.Sound := by
  apply (clearRegisters_sound _).seq
  apply seqList_sound
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact binaryCopy_sound _ _ _

theorem binaryEvalStoreTerm_sound : binaryEvalStoreTerm.Sound :=
  ((binaryCopy_sound _ _ _).seq (binaryCopy_sound _ _ _)).seq (clearRegisters_sound _)

theorem binaryEvalLoadTerm_requires (v : BinaryValues 70) : binaryEvalLoadTerm.requires v := by
  refine ⟨clearRegisters_requires _ _, ?_⟩
  simp [seqList, seq, binaryCopy, identity, emitBits, clearRegisters_effect,
    evalArithmeticRegisters]

/-- Loading the arithmetic workspace preserves all registers from 13 onward. -/
theorem binaryEvalLoadTerm_effect (v : BinaryValues 70) :
    binaryEvalLoadTerm.effect v =
      signedTermValues (v 18) (v 17) (v 27) 0 (v 26) (v 28) (v 19) (v 20) 0
        (fun j ↦ v (j.natAdd 13)) := by
  dsimp only [binaryEvalLoadTerm, seqList, seq, binaryCopy, identity, emitBits]
  conv_lhs => simp [clearRegisters_effect, evalArithmeticRegisters]
  rw [signedTermValues_eq]
  funext j
  fin_cases j <;>
    simp [clearRegisters_effect, Fin.append, Fin.addCases]

end SparseIrred.UpperBounds.Machine
