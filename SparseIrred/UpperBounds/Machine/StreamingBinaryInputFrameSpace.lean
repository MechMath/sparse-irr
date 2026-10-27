import SparseIrred.UpperBounds.Machine.StreamingBinaryInputFrame

/-! # Linear binary-width space for the framed input reader -/

set_option maxHeartbeats 1200000

namespace SparseIrred.UpperBounds.Machine

open Complexity BinaryRoutine

theorem inputReadBit_values_le {k : ℕ} (v : BinaryValues (5 + k)) (W : ℕ)
    (hv : ∀ i, v i ≤ W) (i : Fin (5 + k)) : (inputReadBit k).effect v i ≤ W := by
  rw [inputReadBit_effect]
  refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) i
  · have hdiv := Nat.div_le_self (v (inputReg k 0)) 2
    have hmod := Nat.mod_le (v (inputReg k 0)) 2
    have hn := hv (inputReg k 0)
    fin_cases i <;> simp [Fin.append] <;> omega
  · simpa using hv (i.natAdd 5)

theorem binaryCopy_values_le {k : ℕ} (src dst scratch : Fin k) (v : BinaryValues k) (W : ℕ)
    (hv : ∀ i, v i ≤ W) (i : Fin k) : (binaryCopy src dst scratch).effect v i ≤ W := by
  simp only [binaryCopy, Function.update_apply]
  split_ifs <;> exact hv _

theorem frameInputReadPair_values_le {k : ℕ} (v : BinaryValues (5 + (8 + k))) (W : ℕ)
    (hv : ∀ i, v i ≤ W) (i : Fin (5 + (8 + k))) :
    (frameInputReadPair k).effect v i ≤ W := by
  apply inputReadBit_values_le
  exact binaryCopy_values_le _ _ _ _ _ (inputReadBit_values_le v W hv)

theorem frameInputReadPair_space {k : ℕ} {S W : ℕ → ℕ}
    {v : ℕ → BinaryValues (5 + (8 + k))} (hv : ∀ j i, v j i ≤ W j) :
    SpaceBoundByWidthAt (frameInputReadPair k) S v W := by
  apply SpaceBoundByWidthAt.seq (inputReadBit_space _ hv)
  apply SpaceBoundByWidthAt.seq
  · apply SpaceBoundByWidthAt.binaryCopy <;>
      exact fun j ↦ inputReadBit_values_le _ _ (hv j) _
  · apply inputReadBit_space
    exact fun j ↦ binaryCopy_values_le _ _ _ _ _ (inputReadBit_values_le _ _ (hv j))

theorem frameInputAddPower_values_le {k : ℕ} (v : BinaryValues (5 + (8 + k))) (W : ℕ)
    (hv : ∀ i, v i ≤ W) (i : Fin (5 + (8 + k))) :
    (frameInputAddPower k).effect v i ≤ 2 * W := by
  simp only [frameInputAddPower, add, Function.update_apply]
  split_ifs
  · have := hv (frameInputReg k 1)
    have := hv (frameInputReg k 2)
    omega
  · have := hv i
    omega

theorem frameInputAddPower_space {k : ℕ} {S W : ℕ → ℕ}
    {v : ℕ → BinaryValues (5 + (8 + k))} (hv : ∀ j i, v j i ≤ W j) :
    SpaceBoundByWidthAt (frameInputAddPower k) S v (fun j ↦ 2 * W j) := by
  apply SpaceBoundByWidthAt.add
  · intro j; have := hv j (frameInputReg k 2); omega
  · intro j
    have := hv j (frameInputReg k 1)
    have := hv j (frameInputReg k 2)
    omega

theorem frameInputDoublePower_space {k : ℕ} {S W : ℕ → ℕ}
    {v : ℕ → BinaryValues (5 + (8 + k))} (hv : ∀ j i, v j i ≤ W j) :
    SpaceBoundByWidthAt (frameInputDoublePower k) S v (fun j ↦ 2 * W j) := by
  apply SpaceBoundByWidthAt.seq
  · apply SpaceBoundByWidthAt.binaryCopy
    · intro j; have := hv j (frameInputReg k 2); omega
    · intro j; have := hv j (frameInputReg k 3); omega
  · apply SpaceBoundByWidthAt.seq
    · apply SpaceBoundByWidthAt.add
      · intro j
        simp [binaryCopy]
        have := hv j (frameInputReg k 2)
        omega
      · intro j
        simp [binaryCopy]
        have := hv j (frameInputReg k 2)
        omega
    · apply SpaceBoundByWidthAt.clear
      intro j
      simp [binaryCopy, add]
      have := hv j (frameInputReg k 2)
      omega

theorem frameInputProcess_space {k : ℕ} {S W : ℕ → ℕ}
    {v : ℕ → BinaryValues (5 + (8 + k))} (hv : ∀ j i, v j i ≤ W j) :
    SpaceBoundByWidthAt (frameInputProcess k) S v (fun j ↦ 4 * W j + 4) := by
  apply SpaceBoundByWidthAt.branchZero
  · apply SpaceBoundByWidthAt.branchZero
    · exact (frameInputDoublePower_space hv).mono (fun _ ↦ by omega)
    · apply SpaceBoundByWidthAt.set
      · intro j; have := hv j (frameInputReg k 5); omega
      · intro j; omega
  · apply SpaceBoundByWidthAt.seq
    · exact (frameInputAddPower_space hv).mono (fun _ ↦ by omega)
    · exact (frameInputDoublePower_space
        (fun j ↦ frameInputAddPower_values_le _ _ (hv j))).mono (fun _ ↦ by omega)

theorem frameInputProcess_preserves_read {k : ℕ} (v : BinaryValues (5 + (8 + k))) :
    (frameInputProcess k).effect v (inputReg (8 + k) 2) = v (inputReg (8 + k) 2) ∧
      (frameInputProcess k).effect v (frameInputReg k 0) = v (frameInputReg k 0) := by
  by_cases h0 : v (frameInputReg k 0) = 0 <;>
    by_cases h2 : v (inputReg (8 + k) 2) = 0 <;>
    simp [frameInputProcess, branchZero, h0, h2, frameInputDoublePower_effect,
      frameInputAddPower_effect, seq, clear, BinaryRoutine.set, addConst]

/-- Every internal bit-read, copy, addition, and cleanup prefix stays within
a constant multiple of the width of the incoming registers. -/
theorem frameInputBody_space {k : ℕ} {S W : ℕ → ℕ}
    {v : ℕ → BinaryValues (5 + (8 + k))} (hv : ∀ j i, v j i ≤ W j) :
    SpaceBoundByWidthAt (frameInputBody k) S v (fun j ↦ 4 * W j + 4) := by
  apply SpaceBoundByWidthAt.branchZero
  · apply SpaceBoundByWidthAt.seq
    · exact (frameInputReadPair_space hv).mono (fun _ ↦ by omega)
    · apply SpaceBoundByWidthAt.seq
      · exact frameInputProcess_space (fun j ↦ frameInputReadPair_values_le _ _ (hv j))
      · apply SpaceBoundByWidthAt.seq
        · apply SpaceBoundByWidthAt.clear
          intro j
          rw [(frameInputProcess_preserves_read _).1]
          have := frameInputReadPair_values_le _ _ (hv j) (inputReg (8 + k) 2)
          omega
        · apply SpaceBoundByWidthAt.clear
          intro j
          simp only [clear, Function.update_apply, frameInputReg_ne_inputReg, ite_false]
          rw [(frameInputProcess_preserves_read _).2]
          have := frameInputReadPair_values_le _ _ (hv j) (frameInputReg k 0)
          omega
  · exact SpaceBoundByWidthAt.identity

end SparseIrred.UpperBounds.Machine
