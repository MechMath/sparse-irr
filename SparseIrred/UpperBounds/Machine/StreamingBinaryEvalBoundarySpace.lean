import SparseIrred.UpperBounds.Machine.StreamingBinaryEvalBoundary
import SparseIrred.UpperBounds.Machine.StreamingBinaryCompareSpace

/-! # Linear-width workspace for evaluator initialization and its final test -/
namespace SparseIrred.UpperBounds.Machine
open Complexity BinaryRoutine

theorem binaryEvalInit_space {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (hv : ∀ j i, v j i ≤ W j) : SpaceBoundByWidthAt binaryEvalInit S v W := by
  apply SpaceBoundByWidthAt.seq
  · exact clearRegisters_space _ hv
  · apply SpaceBoundByWidthAt.binaryCopy
    · intro j; exact (clearRegisters_effect_le _ _ _).trans (hv j _)
    · intro j; exact (clearRegisters_effect_le _ _ _).trans (hv j _)

theorem binaryEvalProbe_space {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (hpos : ∀ j, 0 < v j 16) (hv : ∀ j i, v j i ≤ W j) :
    SpaceBoundByWidthAt binaryEvalProbe S v W := by
  apply SpaceBoundByWidthAt.seq
  · exact SpaceBoundByWidthAt.clear _ (fun j ↦ hv j _)
  · apply SpaceBoundByWidthAt.seq
    · apply SpaceBoundByWidthAt.binaryCopy
      · intro j; simpa [clear] using hv j 16
      · intro j; simpa [clear] using hv j 0
    · apply SpaceBoundByWidthAt.binaryPred
      intro j
      simp [binaryCopy, clear]
      have := hv j 16
      have := hpos j
      omega

theorem binaryEvalEqualityLoad_values_le (v : BinaryValues 70) (W : ℕ)
    (hv : ∀ i, v i ≤ W) (i : Fin 70) : binaryEvalEqualityLoad.effect v i ≤ W := by
  have h1 := values_update_le (5 : Fin 70) hv (Nat.zero_le W)
  have h2 := values_update_le (0 : Fin 70) h1 (h1 19)
  exact values_update_le 1 h2 (h2 20) i

theorem binaryEvalEqualityLoad_space {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (hv : ∀ j i, v j i ≤ W j) : SpaceBoundByWidthAt binaryEvalEqualityLoad S v W := by
  apply SpaceBoundByWidthAt.seq
  · exact SpaceBoundByWidthAt.clear _ (fun j ↦ hv j _)
  · apply SpaceBoundByWidthAt.seq
    · apply SpaceBoundByWidthAt.binaryCopy
      · intro j; simpa [clear] using hv j 19
      · intro j; simpa [clear] using hv j 0
    · apply SpaceBoundByWidthAt.binaryCopy
      · intro j; simpa [clear, binaryCopy] using hv j 20
      · intro j; simpa [clear, binaryCopy] using hv j 1

theorem binaryEvalFinish_space {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (hW : ∀ j, 1 ≤ W j) (hv : ∀ j i, v j i ≤ W j) :
    SpaceBoundByWidthAt binaryEvalFinish S v W := by
  have h5 : ∀ j, binaryEvalEqualityLoad.effect (v j) 5 = 0 := by
    intro j
    simp [binaryEvalEqualityLoad, seq, clear, binaryCopy]
  apply SpaceBoundByWidthAt.seq
  · apply SpaceBoundByWidthAt.seq
    · exact binaryEvalEqualityLoad_space hv
    · exact binaryEq70_space_of_scratchZero h5
        (fun j ↦ binaryEvalEqualityLoad_values_le (v j) (W j) (hv j))
  · apply SpaceBoundByWidthAt.binaryCopy
    · intro j
      change binaryEq70.effect (binaryEvalEqualityLoad.effect (v j)) 2 ≤ W j
      rw [binaryEq70_effect_of_scratchZero _ (h5 j)]
      change (if _ = _ then 1 else 0) ≤ W j
      have := hW j
      split_ifs <;> omega
    · intro j
      change binaryEq70.effect (binaryEvalEqualityLoad.effect (v j)) 31 ≤ W j
      have h := binaryEq70_extra (binaryEvalEqualityLoad.effect (v j)) (h5 j) (25 : Fin 64)
      change binaryEq70.effect (binaryEvalEqualityLoad.effect (v j)) 31 = _ at h
      rw [h]
      exact binaryEvalEqualityLoad_values_le (v j) (W j) (hv j) 31

end SparseIrred.UpperBounds.Machine
