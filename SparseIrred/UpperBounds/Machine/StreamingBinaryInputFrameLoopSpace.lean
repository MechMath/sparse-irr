import SparseIrred.UpperBounds.Machine.StreamingBinaryInputFrameLoop
import SparseIrred.UpperBounds.Machine.StreamingBinaryInputFrameSpace
import SparseIrred.UpperBounds.Machine.StreamingMachineLinear

/-! # Reusable linear-width workspace for complete framed-word decoding -/

set_option maxHeartbeats 1200000

namespace SparseIrred.UpperBounds.Machine

open Complexity BinaryRoutine SparseDiv SparseDiv.StringArith

theorem pow_length_le_packedInput (x : List Bool) : 2 ^ x.length ≤ packedInput x := by
  apply Nat.lt_size.mp
  rw [packedInput_size]
  omega

theorem packedInput_le_twice_of_length_le (x y : List Bool) (h : x.length ≤ y.length) :
    packedInput x ≤ 2 * packedInput y := by
  have hx := Nat.lt_size_self (packedInput x)
  rw [packedInput_size, pow_succ] at hx
  have hxy := Nat.pow_le_pow_right (show 1 ≤ 2 by decide) h
  have hy := pow_length_le_packedInput y
  nlinarith

theorem decNat_le_packedInput_of_length_le (x y : List Bool) (h : x.length ≤ y.length) :
    decNat x ≤ packedInput y := by
  exact (decNat_lt_two_pow_length x).le.trans
    ((Nat.pow_le_pow_right (by decide) h).trans (pow_length_le_packedInput y))

theorem frameInputValues_le {k : ℕ} (n acc power done i limit W : ℕ) (extra : Fin k → ℕ)
    (hn : n ≤ W) (ha : acc ≤ W) (hp : power ≤ W) (hd : done ≤ W)
    (hi : i ≤ W) (hl : limit ≤ W) (he : ∀ j, extra j ≤ W) (j : Fin (5 + (8 + k))) :
    frameInputValues n acc power done i limit extra j ≤ W := by
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
  · change frameInputValues _ _ _ _ _ _ _ (inputReg (8 + k) j) ≤ _
    fin_cases j <;> simp <;> assumption
  · refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
    · change frameInputValues _ _ _ _ _ _ _ (frameInputReg k j) ≤ _
      fin_cases j <;> simp <;> assumption
    · simpa using he j

theorem frameInputStage_le {k : ℕ} (payload rest : List Bool) (limit processed counter W : ℕ)
    (extra : Fin k → ℕ) (hinput : packedInput (pair payload rest) ≤ W)
    (hlimit : limit ≤ W) (hcounter : counter ≤ limit) (he : ∀ j, extra j ≤ W)
    (j : Fin (5 + (8 + k))) :
    frameInputStage payload rest limit processed counter extra j ≤ 2 * W := by
  have hlen : payload.length ≤ (pair payload rest).length := by rw [pair_length]; omega
  have hW : 0 < W := (packedInput_pos _).trans_le hinput
  have hWW : W ≤ 2 * W := by omega
  unfold frameInputStage
  split_ifs with hi
  · apply frameInputValues_le
    · have hlength : (delimit (payload.drop processed) ++ rest).length ≤
          (pair payload rest).length := by
        simp only [List.length_append, delimit_length, List.length_drop, pair_length]
        omega
      exact (packedInput_le_twice_of_length_le _ _ hlength).trans (Nat.mul_le_mul_left 2 hinput)
    · exact (decNat_le_packedInput_of_length_le (payload.take processed) (pair payload rest)
        ((List.length_take_le _ _).trans (hi.trans hlen))).trans (hinput.trans hWW)
    · exact ((Nat.pow_le_pow_right (by decide) (hi.trans hlen)).trans
        (pow_length_le_packedInput _)).trans (hinput.trans hWW)
    · omega
    · omega
    · omega
    · intro j; have := he j; omega
  · apply frameInputValues_le
    · have hlength : rest.length ≤ (pair payload rest).length := by rw [pair_length]; omega
      exact (packedInput_le_twice_of_length_le _ _ hlength).trans (Nat.mul_le_mul_left 2 hinput)
    · exact (decNat_le_packedInput_of_length_le _ _ hlen).trans (hinput.trans hWW)
    · exact ((Nat.pow_le_pow_right (by decide) hlen).trans
        (pow_length_le_packedInput _)).trans (hinput.trans hWW)
    · omega
    · omega
    · omega
    · intro j; have := he j; omega

/-- The exponential loop budget costs only its binary width, and each body
execution reuses the same cells. -/
theorem frameInputLoop_space {k : ℕ} (payload rest : ℕ → List Bool) (limit : ℕ → ℕ)
    (extra : ℕ → Fin k → ℕ) (S W : ℕ → ℕ)
    (hinput : ∀ j, packedInput (pair (payload j) (rest j)) ≤ W j)
    (hlimit : ∀ j, limit j ≤ W j) (he : ∀ j i, extra j i ≤ W j) :
    SpaceBoundByWidthAt (frameInputLoop k) S
      (fun j ↦ frameInputStage (payload j) (rest j) (limit j) 0 0 (extra j)) W := by
  apply SpaceBoundByWidthAt.binaryFor_of_clamped_body
  · intro j; simpa using hlimit j
  · intro j count hc
    rw [frameInputLoop_values, frameInputStage_counter]
    have hcount : count < limit j := by simpa [binaryForCount] using hc
    exact hcount.le.trans (hlimit j)
  · apply spaceWidth_mul_add 8
    apply (frameInputBody_space (W := fun code ↦ 2 * W (Nat.unpair code).1) ?_).mono
      (fun _ ↦ by omega)
    intro code idx
    unfold binaryForClampedValues
    rw [frameInputLoop_values]
    apply frameInputStage_le _ _ _ _ _ _ _ (hinput _) (hlimit _) _ (he _)
    simp [binaryForCount]

theorem seqClears_space {k : ℕ} (indices : List (Fin k)) {S W : ℕ → ℕ}
    {v : ℕ → BinaryValues k} (hv : ∀ j i, v j i ≤ W j) :
    SpaceBoundByWidthAt (seqList (indices.map clear)) S v W := by
  induction indices generalizing v with
  | nil => exact SpaceBoundByWidthAt.identity
  | cons idx indices ih =>
    change SpaceBoundByWidthAt (seq (clear idx) (seqList (indices.map clear))) S v W
    apply SpaceBoundByWidthAt.seq (SpaceBoundByWidthAt.clear _ (fun j ↦ hv j idx))
    apply ih
    intro j i
    simp only [clear, Function.update_apply]
    split_ifs
    · omega
    · exact hv j i

theorem frameInputClear_space {k : ℕ} {S W : ℕ → ℕ}
    {v : ℕ → BinaryValues (5 + (8 + k))} (hv : ∀ j i, v j i ≤ W j) :
    SpaceBoundByWidthAt (frameInputClear k) S v W := by
  apply SpaceBoundByWidthAt.seq (inputReadReset_space _ hv)
  apply seqClears_space
    [frameInputReg k 0, frameInputReg k 1, frameInputReg k 2, frameInputReg k 3,
      frameInputReg k 4, frameInputReg k 5, frameInputReg k 6, frameInputReg k 7]
  intro j i
  rw [inputReadReset_effect]
  exact inputDivTwoValues_le _ 0 _ _ (hv j _) (Nat.zero_le _) (fun q ↦ hv j _) i

theorem frameInputInit_space {k : ℕ} {S W : ℕ → ℕ}
    {v : ℕ → BinaryValues (5 + (8 + k))} (hv : ∀ j i, v j i ≤ W j)
    (hW : ∀ j, 1 ≤ W j) : SpaceBoundByWidthAt (frameInputInit k) S v W := by
  apply SpaceBoundByWidthAt.seq (frameInputClear_space hv)
  apply SpaceBoundByWidthAt.seq
  · apply SpaceBoundByWidthAt.set
    · intro j; simp [frameInputClear_effect]
    · exact hW
  · apply SpaceBoundByWidthAt.binaryCopy
    · intro j
      simpa [frameInputClear_effect, BinaryRoutine.set, seq, clear, addConst]
        using hv j (inputReg (8 + k) 0)
    · intro j
      simp [frameInputClear_effect, BinaryRoutine.set, seq, clear, addConst]

/-- A complete frame decoder, including scratch initialization, satisfies a
linear binary-width space bound on every reachable machine prefix. -/
theorem frameInput_space {k : ℕ} {S W : ℕ → ℕ}
    {v : ℕ → BinaryValues (5 + (8 + k))} (payload rest : ℕ → List Bool)
    (hinput : ∀ j, v j (inputReg (8 + k) 0) = packedInput (pair (payload j) (rest j)))
    (hv : ∀ j i, v j i ≤ W j) : SpaceBoundByWidthAt (frameInput k) S v W := by
  apply SpaceBoundByWidthAt.seq
  · apply frameInputInit_space hv
    intro j
    have := packedInput_pos (pair (payload j) (rest j))
    have := hv j (inputReg (8 + k) 0)
    rw [hinput j] at this
    omega
  · have heq : (fun j ↦ (frameInputInit k).effect (v j)) =
        (fun j ↦ frameInputStage (payload j) (rest j) (v j (inputReg (8 + k) 0)) 0 0
          (fun i ↦ v j ((i.natAdd 8).natAdd 5))) := by
      funext j
      rw [frameInputInit_effect]
      simp [frameInputStage, hinput j, pair]
    rw [heq]
    apply frameInputLoop_space
    · intro j; rw [← hinput j]; exact hv j _
    · exact fun j ↦ hv j _
    · exact fun j i ↦ hv j _

/-- The decoder's final registers are bounded by twice the incoming numeric
envelope; this includes every preserved caller register. -/
theorem frameInput_values_le {k : ℕ} (v : BinaryValues (5 + (8 + k))) (W : ℕ)
    (payload rest : List Bool)
    (hinput : v (inputReg (8 + k) 0) = packedInput (pair payload rest))
    (hv : ∀ i, v i ≤ W) (j : Fin (5 + (8 + k))) :
    (frameInput k).effect v j ≤ 2 * W := by
  have hb := frameInputLoop_budget payload rest
  have hdone : ¬packedInput (pair payload rest) ≤ payload.length := by omega
  have h := frameInputStage_le payload rest (packedInput (pair payload rest))
    (packedInput (pair payload rest)) (packedInput (pair payload rest)) W
    (fun i ↦ v ((i.natAdd 8).natAdd 5))
    (by rw [← hinput]; exact hv _) (by rw [← hinput]; exact hv _) le_rfl
    (fun i ↦ hv _) j
  simp only [frameInputStage, hdone, ite_false] at h
  rw [frameInput_effect v payload rest hinput]
  exact h

end SparseIrred.UpperBounds.Machine
