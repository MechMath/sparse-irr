import SparseIrred.UpperBounds.Machine.StreamingBinaryEvalControls
import SparseIrred.UpperBounds.Machine.StreamingBinaryCompare

/-! # Initialization, end-of-table detection, and the actual residue-equality test -/

namespace SparseIrred.UpperBounds.Machine

open Complexity BinaryRoutine

def evalInitRegisters : List (Fin 70) :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
   19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]

def binaryEvalInit : BinaryRoutine 70 :=
  seq (clearRegisters evalInitRegisters) (binaryCopy 16 22 5)

def binaryEvalProbe : BinaryRoutine 70 :=
  seq (clear 5) (seq (binaryCopy 16 0 5) (binaryPred 0))

def binaryEvalEqualityLoad : BinaryRoutine 70 :=
  seq (clear 5) (seq (binaryCopy 19 0 5) (binaryCopy 20 1 5))

/-- Compare the canonical residues and place the actual zero flag in register 31. -/
def binaryEvalFinish : BinaryRoutine 70 :=
  seq (seq binaryEvalEqualityLoad binaryEq70) (binaryCopy 2 31 5)

theorem binaryEvalInit_sound : binaryEvalInit.Sound :=
  (clearRegisters_sound _).seq (binaryCopy_sound _ _ _)

theorem binaryEvalProbe_sound : binaryEvalProbe.Sound :=
  (clear_sound _).seq ((binaryCopy_sound _ _ _).seq (binaryPred_sound _))

theorem binaryEvalEqualityLoad_sound : binaryEvalEqualityLoad.Sound :=
  (clear_sound _).seq ((binaryCopy_sound _ _ _).seq (binaryCopy_sound _ _ _))

theorem binaryEvalFinish_sound : binaryEvalFinish.Sound :=
  (binaryEvalEqualityLoad_sound.seq binaryEq70_sound).seq (binaryCopy_sound _ _ _)

theorem binaryEvalInit_requires (v : BinaryValues 70) : binaryEvalInit.requires v := by
  refine ⟨clearRegisters_requires _ _, ?_⟩
  simp [binaryCopy, clearRegisters_effect, evalInitRegisters]

theorem binaryEvalInit_effect (v : BinaryValues 70) (j : Fin 70) :
    binaryEvalInit.effect v j =
      if j = 22 then v 16 else if j ∈ evalInitRegisters then 0 else v j := by
  simp [binaryEvalInit, seq, binaryCopy, clearRegisters_effect, evalInitRegisters,
    Function.update_apply]

theorem binaryEvalProbe_requires (v : BinaryValues 70) (hv : 0 < v 16) :
    binaryEvalProbe.requires v := by simp [binaryEvalProbe, seq, clear, binaryCopy, binaryPred, hv]

theorem binaryEvalProbe_effect (v : BinaryValues 70) (j : Fin 70) :
    binaryEvalProbe.effect v j = if j = 0 then v 16 - 1 else if j = 5 then 0 else v j := by
  simp [binaryEvalProbe, seq, clear, binaryCopy, binaryPred, Function.update_apply]

theorem binaryEvalEqualityLoad_requires (v : BinaryValues 70) :
    binaryEvalEqualityLoad.requires v := by simp [binaryEvalEqualityLoad, seq, clear, binaryCopy]

theorem binaryEvalEqualityLoad_effect (v : BinaryValues 70) :
    binaryEvalEqualityLoad.effect v =
      compareValues (v 19) (v 20) (v 2) (v 3) (v 4) (fun j ↦ v (j.natAdd 6)) := by
  dsimp only [binaryEvalEqualityLoad, seq, clear, binaryCopy]
  conv_lhs => simp
  funext j
  fin_cases j <;> simp [compareValues, framedModInput, Fin.append, Fin.addCases]

theorem binaryEvalFinish_requires (v : BinaryValues 70) : binaryEvalFinish.requires v := by
  refine ⟨⟨binaryEvalEqualityLoad_requires v, ?_⟩, ?_⟩
  · rw [binaryEvalEqualityLoad_effect]
    exact binaryEq70_requires _ _ _ _ _ _
  · change (binaryCopy 2 31 5).requires (binaryEq70.effect (binaryEvalEqualityLoad.effect v))
    rw [binaryEvalEqualityLoad_effect, binaryEq70_effect]
    simp [binaryCopy, compareValues, framedModInput, Fin.append, Fin.addCases]

/-- The final machine computes a literal zero/one flag and preserves the caller's live registers. -/
theorem binaryEvalFinish_effect (v : BinaryValues 70) (j : Fin 70) (hj : 6 ≤ j.val) :
    binaryEvalFinish.effect v j = if j = 31 then (if v 19 = v 20 then 1 else 0) else v j := by
  change (binaryCopy 2 31 5).effect (binaryEq70.effect (binaryEvalEqualityLoad.effect v)) j = _
  rw [binaryEvalEqualityLoad_effect, binaryEq70_effect]
  simp only [binaryCopy, Function.update_apply]
  by_cases heq : j = 31
  · simp [heq, compareValues, framedModInput, Fin.append, Fin.addCases]
  · simp only [heq, ↓reduceIte]
    let i : Fin 64 := ⟨j.val - 6, by have := j.isLt; omega⟩
    have hi : i.natAdd 6 = j := Fin.ext (by simp [i]; omega)
    rw [← hi]
    exact Fin.append_right _ _ _

end SparseIrred.UpperBounds.Machine
