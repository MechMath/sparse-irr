import SparseIrred.UpperBounds.Machine.StreamingBinaryCompare

/-! # Linear-width all-prefix space of the binary comparator machines -/

namespace SparseIrred.UpperBounds.Machine

open Complexity BinaryRoutine

theorem comparePred_space {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (hv : ∀ j, v j 3 ≤ W j) : SpaceBoundByWidthAt comparePred S v W := by
  apply spaceWidth_mul_add 1
  apply SpaceBoundByWidthAt.branchZero 3 SpaceBoundByWidthAt.identity
  apply SpaceBoundByWidthAt.binaryPred
  intro j; have := hv j; omega

theorem compareLoop_space (reverse : Bool) (left right flag : ℕ → ℕ)
    (extra : ℕ → Fin 64 → ℕ) (S W : ℕ → ℕ)
    (hl : ∀ j, left j ≤ W j) (hr : ∀ j, right j ≤ W j) :
    SpaceBoundByWidthAt (compareLoop reverse) S
      (fun j ↦ compareStage reverse (left j) (right j) (flag j) 0 (extra j)) W := by
  have hlim : ∀ j, (if reverse then right j else left j) ≤ W j := by
    cases reverse <;> simp <;> assumption
  have hother : ∀ j, (if reverse then left j else right j) ≤ W j := by
    cases reverse <;> simp <;> assumption
  apply SpaceBoundByWidthAt.binaryFor_of_clamped_body
  · intro j
    cases reverse <;> simpa [compareStage, compareLeft, compareValues, framedModInput,
      Fin.append, Fin.addCases] using hlim j
  · intro j count hc
    rw [compareLoop_values]
    have hcount : count < (if reverse then right j else left j) := by
      cases reverse <;> simpa [binaryForCount, compareLeft, compareStage, compareValues,
        framedModInput, Fin.append, Fin.addCases] using hc
    simpa [compareStage, compareValues, framedModInput, Fin.append, Fin.addCases]
      using hcount.le.trans (hlim j)
  · apply comparePred_space
    intro code
    unfold binaryForClampedValues
    rw [compareLoop_values]
    change (if reverse then left (Nat.unpair code).1 else right (Nat.unpair code).1) - _ ≤ _
    exact (Nat.sub_le _ _).trans (hother _)

theorem compareInit_space (reverse : Bool) (left right flag temp counter : ℕ → ℕ)
    (extra : ℕ → Fin 64 → ℕ) (S W : ℕ → ℕ)
    (hl : ∀ j, left j ≤ W j) (hr : ∀ j, right j ≤ W j)
    (ht : ∀ j, temp j ≤ W j) (hc : ∀ j, counter j ≤ W j) :
    SpaceBoundByWidthAt (compareInit reverse) S
      (fun j ↦ compareValues (left j) (right j) (flag j) (temp j) (counter j) (extra j)) W := by
  apply SpaceBoundByWidthAt.seq
  · apply SpaceBoundByWidthAt.clear
    intro j
    simpa [compareValues, framedModInput, Fin.append, Fin.addCases] using hc j
  · apply SpaceBoundByWidthAt.binaryCopy
    · intro j
      cases reverse
      · simpa [compareRight, clear, compareValues, framedModInput, Fin.append, Fin.addCases] using hr j
      · simpa [compareRight, clear, compareValues, framedModInput, Fin.append, Fin.addCases] using hl j
    · intro j
      simpa [clear, compareValues, framedModInput, Fin.append, Fin.addCases] using ht j

theorem compareFinish_space (left right flag temp counter : ℕ → ℕ)
    (extra : ℕ → Fin 64 → ℕ) (S W : ℕ → ℕ)
    (hf : ∀ j, flag j ≤ W j) (ht : ∀ j, temp j ≤ W j) (hc : ∀ j, counter j ≤ W j) :
    SpaceBoundByWidthAt compareFinish S
      (fun j ↦ compareValues (left j) (right j) (flag j) (temp j) (counter j) (extra j)) W := by
  apply spaceWidth_mul_add 1
  apply SpaceBoundByWidthAt.seq
  · apply SpaceBoundByWidthAt.branchZero
    · apply SpaceBoundByWidthAt.clear
      intro j
      simp [compareValues, framedModInput, Fin.append, Fin.addCases]
      have := hf j; omega
    · apply SpaceBoundByWidthAt.set
      · intro j
        simp [compareValues, framedModInput, Fin.append, Fin.addCases]
        have := hf j; omega
      · intro j; omega
  · apply SpaceBoundByWidthAt.seq
    · apply SpaceBoundByWidthAt.clear
      intro j
      by_cases h : temp j = 0 <;>
        simp [branchZero, clear, BinaryRoutine.set, seq, addConst, compareValues,
          framedModInput, Fin.append, Fin.addCases, h] <;> have := ht j <;> omega
    · apply SpaceBoundByWidthAt.clear
      intro j
      by_cases h : temp j = 0 <;>
        simp [branchZero, clear, BinaryRoutine.set, seq, addConst, compareValues,
          framedModInput, Fin.append, Fin.addCases, h] <;> have := hc j <;> omega

theorem binaryLtCore_space (reverse : Bool) (left right flag temp counter : ℕ → ℕ)
    (extra : ℕ → Fin 64 → ℕ) (S W : ℕ → ℕ)
    (hl : ∀ j, left j ≤ W j) (hr : ∀ j, right j ≤ W j)
    (hf : ∀ j, flag j ≤ W j) (ht : ∀ j, temp j ≤ W j) (hc : ∀ j, counter j ≤ W j) :
    SpaceBoundByWidthAt (binaryLtCore reverse) S
      (fun j ↦ compareValues (left j) (right j) (flag j) (temp j) (counter j) (extra j)) W := by
  have heq : (fun j ↦ (compareInit reverse).effect
      (compareValues (left j) (right j) (flag j) (temp j) (counter j) (extra j))) =
      (fun j ↦ compareStage reverse (left j) (right j) (flag j) 0 (extra j)) :=
    funext (fun j ↦ compareInit_effect _ _ _ _ _ _ _)
  apply SpaceBoundByWidthAt.seq
  · apply SpaceBoundByWidthAt.seq (compareInit_space reverse _ _ _ _ _ _ S W hl hr ht hc)
    rw [heq]
    exact compareLoop_space reverse _ _ _ _ S W hl hr
  · have heq' : (fun j ↦ (seq (compareInit reverse) (compareLoop reverse)).effect
        (compareValues (left j) (right j) (flag j) (temp j) (counter j) (extra j))) =
        (fun j ↦ compareStage reverse (left j) (right j) (flag j)
          (if reverse then right j else left j) (extra j)) := by
      funext j
      change (compareLoop reverse).effect ((compareInit reverse).effect _) = _
      rw [compareInit_effect, compareLoop_effect]
    rw [heq']
    apply compareFinish_space _ _ _ _ _ _ S W hf
    · intro j
      cases reverse <;> simp only [Bool.false_eq_true, ite_false, ite_true]
      · exact (Nat.sub_le _ _).trans (hr j)
      · exact (Nat.sub_le _ _).trans (hl j)
    · intro j; cases reverse <;> simp <;> first | exact hl j | exact hr j

theorem binaryLt70_space (left right flag temp counter : ℕ → ℕ)
    (extra : ℕ → Fin 64 → ℕ) (S W : ℕ → ℕ)
    (hl : ∀ j, left j ≤ W j) (hr : ∀ j, right j ≤ W j)
    (hf : ∀ j, flag j ≤ W j) (ht : ∀ j, temp j ≤ W j) (hc : ∀ j, counter j ≤ W j) :
    SpaceBoundByWidthAt binaryLt70 S
      (fun j ↦ compareValues (left j) (right j) (flag j) (temp j) (counter j) (extra j)) W :=
  binaryLtCore_space false left right flag temp counter extra S W hl hr hf ht hc

theorem compareInvert_space (left right flag temp counter : ℕ → ℕ)
    (extra : ℕ → Fin 64 → ℕ) (S W : ℕ → ℕ) (hf : ∀ j, flag j ≤ W j)
    (hW : ∀ j, 1 ≤ W j) :
    SpaceBoundByWidthAt compareInvert S
      (fun j ↦ compareValues (left j) (right j) (flag j) (temp j) (counter j) (extra j)) W := by
  apply SpaceBoundByWidthAt.branchZero
  · apply SpaceBoundByWidthAt.set
    · intro j; simpa [compareValues, framedModInput, Fin.append, Fin.addCases] using hf j
    · exact hW
  · apply SpaceBoundByWidthAt.clear
    intro j; simpa [compareValues, framedModInput, Fin.append, Fin.addCases] using hf j

/-- Equality is computed within one reusable linear-width workspace. -/
theorem binaryEq70_space (left right flag temp counter : ℕ → ℕ)
    (extra : ℕ → Fin 64 → ℕ) (S W : ℕ → ℕ)
    (hl : ∀ j, left j ≤ W j) (hr : ∀ j, right j ≤ W j)
    (hf : ∀ j, flag j ≤ W j) (ht : ∀ j, temp j ≤ W j) (hc : ∀ j, counter j ≤ W j) :
    SpaceBoundByWidthAt binaryEq70 S
      (fun j ↦ compareValues (left j) (right j) (flag j) (temp j) (counter j) (extra j)) W := by
  apply spaceWidth_mul_add 1
  have hle : ∀ j, left j ≤ 1 * W j + 1 := fun j ↦ by have := hl j; omega
  have hre : ∀ j, right j ≤ 1 * W j + 1 := fun j ↦ by have := hr j; omega
  have hflag : ∀ j, (if left j < right j then 1 else 0) ≤ 1 * W j + 1 := by
    intro j; split_ifs <;> omega
  apply SpaceBoundByWidthAt.seq
  · exact (binaryLt70_space _ _ _ _ _ _ S W hl hr hf ht hc).mono (fun _ ↦ by omega)
  · have heq : (fun j ↦ binaryLt70.effect
        (compareValues (left j) (right j) (flag j) (temp j) (counter j) (extra j))) =
        (fun j ↦ compareValues (left j) (right j) (if left j < right j then 1 else 0) 0 0 (extra j)) :=
      funext (fun j ↦ binaryLt70_effect _ _ _ _ _ _)
    rw [heq]
    apply SpaceBoundByWidthAt.branchZero
    · apply SpaceBoundByWidthAt.seq
      · exact binaryLtCore_space true _ _ _ _ _ _ S _ hle hre hflag
          (fun _ ↦ Nat.zero_le _) (fun _ ↦ Nat.zero_le _)
      · have heq' : (fun j ↦ (binaryLtCore true).effect
            (compareValues (left j) (right j) (if left j < right j then 1 else 0) 0 0 (extra j))) =
            (fun j ↦ compareValues (left j) (right j) (if right j < left j then 1 else 0) 0 0 (extra j)) :=
          funext (fun j ↦ binaryLtCore_effect true _ _ _ _ _ _)
        rw [heq']
        apply compareInvert_space
        · intro j; split_ifs <;> omega
        · intro j; omega
    · apply SpaceBoundByWidthAt.clear
      intro j
      simpa [compareValues, framedModInput, Fin.append, Fin.addCases] using hflag j

theorem binaryLt70_space_of_scratchZero {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (h5 : ∀ j, v j 5 = 0) (hv : ∀ j i, v j i ≤ W j) :
    SpaceBoundByWidthAt binaryLt70 S v W := by
  have heq : (fun j ↦ compareValues (v j 0) (v j 1) (v j 2) (v j 3) (v j 4)
      (fun i ↦ v j (i.natAdd 6))) = v := funext (fun j ↦ compareValues_repack _ (h5 j))
  rw [← heq]
  exact binaryLt70_space _ _ _ _ _ _ S W (fun j ↦ hv j 0) (fun j ↦ hv j 1)
    (fun j ↦ hv j 2) (fun j ↦ hv j 3) (fun j ↦ hv j 4)

theorem binaryEq70_space_of_scratchZero {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (h5 : ∀ j, v j 5 = 0) (hv : ∀ j i, v j i ≤ W j) :
    SpaceBoundByWidthAt binaryEq70 S v W := by
  have heq : (fun j ↦ compareValues (v j 0) (v j 1) (v j 2) (v j 3) (v j 4)
      (fun i ↦ v j (i.natAdd 6))) = v := funext (fun j ↦ compareValues_repack _ (h5 j))
  rw [← heq]
  exact binaryEq70_space _ _ _ _ _ _ S W (fun j ↦ hv j 0) (fun j ↦ hv j 1)
    (fun j ↦ hv j 2) (fun j ↦ hv j 3) (fun j ↦ hv j 4)

end SparseIrred.UpperBounds.Machine
