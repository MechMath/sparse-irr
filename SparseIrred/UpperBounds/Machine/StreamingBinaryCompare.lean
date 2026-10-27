import SparseIrred.UpperBounds.Machine.StreamingBinaryFramed
import SparseIrred.UpperBounds.Machine.StreamingMachineLinear

/-! # Deterministic comparison of binary registers in linear workspace -/

namespace SparseIrred.UpperBounds.Machine

open Complexity BinaryRoutine

abbrev compareValues (left right flag temp counter : ℕ) (extra : Fin 64 → ℕ) : BinaryValues 70 :=
  framedModInput left right flag temp counter extra

@[simp] theorem compareValues_three (left right flag temp counter : ℕ) (extra : Fin 64 → ℕ) :
    framedModInput left right flag temp counter extra (3 : Fin 70) = temp := rfl

def compareLeft (reverse : Bool) : Fin 70 := if reverse then 1 else 0
def compareRight (reverse : Bool) : Fin 70 := if reverse then 0 else 1

def comparePred : BinaryRoutine 70 := branchZero 3 identity (binaryPred 3)

def compareInit (reverse : Bool) : BinaryRoutine 70 :=
  seq (clear 4) (binaryCopy (compareRight reverse) 3 5)

def compareLoop (reverse : Bool) : BinaryRoutine 70 :=
  binaryFor comparePred 4 (compareLeft reverse)

def compareFinish : BinaryRoutine 70 :=
  seq (branchZero 3 (clear 2) (BinaryRoutine.set 2 1)) (seq (clear 3) (clear 4))

def binaryLtCore (reverse : Bool) : BinaryRoutine 70 :=
  seq (seq (compareInit reverse) (compareLoop reverse)) compareFinish

/-- Compare registers zero and one, returning a Boolean in register two. -/
def binaryLt70 : BinaryRoutine 70 := binaryLtCore false

def compareInvert : BinaryRoutine 70 := branchZero 2 (BinaryRoutine.set 2 1) (clear 2)

/-- Equality uses both strict comparisons, sharing the same scratch registers. -/
def binaryEq70 : BinaryRoutine 70 :=
  seq binaryLt70 (branchZero 2 (seq (binaryLtCore true) compareInvert) (clear 2))

theorem comparePred_sound : comparePred.Sound :=
  identity_sound.branchZero (binaryPred_sound _) _

theorem compareInit_sound (reverse : Bool) : (compareInit reverse).Sound :=
  (clear_sound _).seq (binaryCopy_sound _ _ _)

theorem compareLoop_sound (reverse : Bool) : (compareLoop reverse).Sound :=
  comparePred_sound.binaryFor _ _

theorem compareFinish_sound : compareFinish.Sound :=
  ((clear_sound _).branchZero (set_sound _ _) _).seq ((clear_sound _).seq (clear_sound _))

theorem binaryLtCore_sound (reverse : Bool) : (binaryLtCore reverse).Sound :=
  ((compareInit_sound reverse).seq (compareLoop_sound reverse)).seq compareFinish_sound

theorem binaryLt70_sound : binaryLt70.Sound := binaryLtCore_sound false

theorem binaryEq70_sound : binaryEq70.Sound :=
  binaryLt70_sound.seq (((binaryLtCore_sound true).seq
    ((set_sound _ _).branchZero (clear_sound _) _)).branchZero (clear_sound _) _)

private theorem compare_update (left right flag temp counter value : ℕ) (extra : Fin 64 → ℕ)
    (idx : Fin 6) :
    Function.update (compareValues left right flag temp counter extra) (modReg 64 idx) value =
      Fin.append (Function.update ![left, right, flag, temp, counter, 0] idx value) extra := by
  funext j
  refine Fin.addCases (m := 6) (n := 64) (fun j ↦ ?_) (fun j ↦ ?_) j
  · change Function.update (compareValues left right flag temp counter extra)
      (modReg 64 idx) value (modReg 64 j) = _
    by_cases h : j = idx
    · subst j
      rw [Function.update_self, Fin.append_left, Function.update_self]
    · have hne : modReg 64 j ≠ modReg 64 idx := fun heq ↦ h ((modReg_inj 64 j idx).mp heq)
      rw [Function.update_of_ne hne, Fin.append_left, Function.update_of_ne h]
      exact framedModInput_reg _ _ _ _ _ _ _
  · rw [Function.update_of_ne (extra_ne_modReg 64 idx j), Fin.append_right]
    exact framedModInput_extra _ _ _ _ _ _ _

theorem comparePred_requires (left right flag temp counter : ℕ) (extra : Fin 64 → ℕ) :
    comparePred.requires (compareValues left right flag temp counter extra) := by
  change if temp = 0 then True else 0 < temp
  split_ifs <;> omega

theorem comparePred_effect (left right flag temp counter : ℕ) (extra : Fin 64 → ℕ) :
    comparePred.effect (compareValues left right flag temp counter extra) =
      compareValues left right flag (temp - 1) counter extra := by
  by_cases ht : temp = 0
  · simp [comparePred, branchZero, identity, emitBits, compareValues, ht,
      framedModInput, Fin.append, Fin.addCases]
  · have hread : compareValues left right flag temp counter extra 3 = temp := rfl
    simp only [comparePred, branchZero, hread, ht, ite_false]
    change Function.update (compareValues left right flag temp counter extra) 3 (temp - 1) = _
    rw [show (3 : Fin 70) = modReg 64 3 from rfl, compare_update]
    congr 1
    funext j; fin_cases j <;> simp

def compareStage (reverse : Bool) (left right flag i : ℕ) (extra : Fin 64 → ℕ) : BinaryValues 70 :=
  compareValues left right flag ((if reverse then left else right) - i) i extra

theorem compareLoop_values (reverse : Bool) (left right flag count : ℕ) (extra : Fin 64 → ℕ) :
    binaryForValues comparePred 4 (compareStage reverse left right flag 0 extra) count =
      compareStage reverse left right flag count extra := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [binaryForValues, ih, binaryForStep]
    change Function.update (comparePred.effect (compareValues left right flag _ count extra))
      4 (count + 1) = _
    rw [comparePred_effect, show (4 : Fin 70) = modReg 64 4 from rfl, compare_update]
    unfold compareStage compareValues framedModInput
    congr 1
    funext j
    fin_cases j <;> simp
    omega

theorem compareLoop_requires (reverse : Bool) (left right flag : ℕ) (extra : Fin 64 → ℕ) :
    (compareLoop reverse).requires (compareStage reverse left right flag 0 extra) := by
  refine ⟨by cases reverse <;> decide, by cases reverse <;> simp [compareStage, compareLeft,
    compareValues, framedModInput, Fin.append, Fin.addCases], ?_⟩
  intro count hc
  rw [compareLoop_values]
  unfold compareStage
  refine ⟨comparePred_requires _ _ _ _ _ _, ?_, ?_⟩ <;>
    rw [comparePred_effect] <;>
    cases reverse <;> simp [compareStage, compareLeft, compareValues, framedModInput, Fin.append, Fin.addCases]

theorem compareLoop_effect (reverse : Bool) (left right flag : ℕ) (extra : Fin 64 → ℕ) :
    (compareLoop reverse).effect (compareStage reverse left right flag 0 extra) =
      compareStage reverse left right flag (if reverse then right else left) extra := by
  change binaryForValues comparePred 4 (compareStage reverse left right flag 0 extra)
    (binaryForCount 4 (compareLeft reverse) (compareStage reverse left right flag 0 extra)) = _
  have hcount : binaryForCount 4 (compareLeft reverse)
      (compareStage reverse left right flag 0 extra) = if reverse then right else left := by
    cases reverse <;> simp [binaryForCount, compareLeft, compareStage, compareValues,
      framedModInput, Fin.append, Fin.addCases]
  rw [hcount, compareLoop_values]

theorem compareInit_requires (reverse : Bool) (left right flag temp counter : ℕ)
    (extra : Fin 64 → ℕ) :
    (compareInit reverse).requires (compareValues left right flag temp counter extra) := by
  cases reverse <;> simp [compareInit, seq, clear, binaryCopy, compareRight, compareValues,
    framedModInput, Fin.append, Fin.addCases]

theorem compareInit_effect (reverse : Bool) (left right flag temp counter : ℕ)
    (extra : Fin 64 → ℕ) :
    (compareInit reverse).effect (compareValues left right flag temp counter extra) =
      compareStage reverse left right flag 0 extra := by
  funext j
  refine Fin.addCases (m := 6) (n := 64) (fun j ↦ ?_) (fun j ↦ ?_) j
  · fin_cases j <;> cases reverse <;>
      simp [compareInit, seq, clear, binaryCopy, compareRight, compareStage, compareValues,
        framedModInput, Fin.append, Fin.addCases]
  · have h3 : j.natAdd 6 ≠ (3 : Fin 70) := extra_ne_modReg 64 3 j
    have h4 : j.natAdd 6 ≠ (4 : Fin 70) := extra_ne_modReg 64 4 j
    cases reverse <;> simp [compareInit, seq, clear, binaryCopy, compareRight, compareStage,
      compareValues, h3, h4, Function.update_apply]

theorem compareFinish_effect (left right flag temp counter : ℕ) (extra : Fin 64 → ℕ) :
    compareFinish.effect (compareValues left right flag temp counter extra) =
      compareValues left right (if temp = 0 then 0 else 1) 0 0 extra := by
  funext j
  refine Fin.addCases (m := 6) (n := 64) (fun j ↦ ?_) (fun j ↦ ?_) j
  · fin_cases j <;> by_cases ht : temp = 0 <;>
      simp [compareFinish, seq, branchZero, clear, BinaryRoutine.set, addConst, compareValues,
        framedModInput, Fin.append, Fin.addCases, ht]
  · have h2 : j.natAdd 6 ≠ (2 : Fin 70) := extra_ne_modReg 64 2 j
    have h3 : j.natAdd 6 ≠ (3 : Fin 70) := extra_ne_modReg 64 3 j
    have h4 : j.natAdd 6 ≠ (4 : Fin 70) := extra_ne_modReg 64 4 j
    have hread : framedModInput left right flag temp counter extra 3 = temp := rfl
    by_cases ht : temp = 0 <;>
      simp [compareFinish, seq, branchZero, clear, BinaryRoutine.set, addConst, compareValues,
        h2, h3, h4, Function.update_apply, hread, ht]

theorem binaryLtCore_requires (reverse : Bool) (left right flag temp counter : ℕ)
    (extra : Fin 64 → ℕ) :
    (binaryLtCore reverse).requires (compareValues left right flag temp counter extra) := by
  refine ⟨⟨compareInit_requires _ _ _ _ _ _ _, ?_⟩, ?_⟩
  · rw [compareInit_effect]; exact compareLoop_requires _ _ _ _ _
  · simp [compareFinish, seq, branchZero, clear, BinaryRoutine.set, addConst]

theorem binaryLtCore_effect (reverse : Bool) (left right flag temp counter : ℕ)
    (extra : Fin 64 → ℕ) :
    (binaryLtCore reverse).effect (compareValues left right flag temp counter extra) =
      compareValues left right
        (if (if reverse then right else left) < (if reverse then left else right) then 1 else 0)
        0 0 extra := by
  change compareFinish.effect ((compareLoop reverse).effect ((compareInit reverse).effect _)) = _
  rw [compareInit_effect, compareLoop_effect]
  unfold compareStage
  rw [compareFinish_effect]
  congr 1
  split_ifs <;> omega

theorem binaryLt70_requires (left right flag temp counter : ℕ) (extra : Fin 64 → ℕ) :
    binaryLt70.requires (compareValues left right flag temp counter extra) :=
  binaryLtCore_requires false _ _ _ _ _ _

theorem binaryLt70_effect (left right flag temp counter : ℕ) (extra : Fin 64 → ℕ) :
    binaryLt70.effect (compareValues left right flag temp counter extra) =
      compareValues left right (if left < right then 1 else 0) 0 0 extra :=
  binaryLtCore_effect false _ _ _ _ _ _

theorem compareClearFlag_effect (left right flag temp counter : ℕ) (extra : Fin 64 → ℕ) :
    (clear (2 : Fin 70)).effect (compareValues left right flag temp counter extra) =
      compareValues left right 0 temp counter extra := by
  change Function.update _ (modReg 64 2) 0 = _
  rw [compare_update]
  congr 1
  funext j; fin_cases j <;> simp

theorem compareSetFlag_effect (left right flag temp counter value : ℕ) (extra : Fin 64 → ℕ) :
    (BinaryRoutine.set (2 : Fin 70) value).effect (compareValues left right flag temp counter extra) =
      compareValues left right value temp counter extra := by
  simp only [BinaryRoutine.set, seq, clear, addConst, Function.update_self,
    Nat.zero_add, Function.update_idem]
  rw [show (2 : Fin 70) = modReg 64 2 from rfl, compare_update]
  congr 1
  funext j; fin_cases j <;> simp

theorem compareInvert_effect (left right flag temp counter : ℕ) (extra : Fin 64 → ℕ) :
    compareInvert.effect (compareValues left right flag temp counter extra) =
      compareValues left right (if flag = 0 then 1 else 0) temp counter extra := by
  change (if flag = 0 then _ else _) = _
  split_ifs
  · exact compareSetFlag_effect _ _ _ _ _ _ _
  · exact compareClearFlag_effect _ _ _ _ _ _

theorem binaryEq70_requires (left right flag temp counter : ℕ) (extra : Fin 64 → ℕ) :
    binaryEq70.requires (compareValues left right flag temp counter extra) := by
  refine ⟨binaryLt70_requires _ _ _ _ _ _, ?_⟩
  rw [binaryLt70_effect]
  change if (if left < right then 1 else 0) = 0 then
    (binaryLtCore true).requires _ ∧ compareInvert.requires ((binaryLtCore true).effect _)
    else True
  by_cases h : left < right
  · simp [h]
  · simp only [h, ite_false, ite_true]
    refine ⟨binaryLtCore_requires true _ _ _ _ _ _, ?_⟩
    simp [compareInvert, branchZero, BinaryRoutine.set, seq, clear, addConst]

/-- Equality returns a literal zero or one while preserving both arguments
and all 64 caller-owned registers. -/
theorem binaryEq70_effect (left right flag temp counter : ℕ) (extra : Fin 64 → ℕ) :
    binaryEq70.effect (compareValues left right flag temp counter extra) =
      compareValues left right (if left = right then 1 else 0) 0 0 extra := by
  change (branchZero 2 _ _).effect (binaryLt70.effect _) = _
  rw [binaryLt70_effect]
  change (if (if left < right then 1 else 0) = 0 then
    compareInvert.effect ((binaryLtCore true).effect (compareValues left right _ 0 0 extra))
    else (clear (2 : Fin 70)).effect (compareValues left right _ 0 0 extra)) = _
  by_cases hlt : left < right
  · have hne : left ≠ right := by omega
    simp only [hlt, ite_true, one_ne_zero, ite_false, hne, compareClearFlag_effect]
  · simp only [hlt, ite_false, ite_true]
    rw [binaryLtCore_effect, compareInvert_effect]
    simp only [ite_true, ite_false]
    congr 1
    split_ifs <;> omega

theorem compareValues_repack (v : BinaryValues 70) (h5 : v 5 = 0) :
    compareValues (v 0) (v 1) (v 2) (v 3) (v 4) (fun j ↦ v (j.natAdd 6)) = v := by
  funext j
  refine Fin.addCases (m := 6) (n := 64) (fun j ↦ ?_) (fun j ↦ ?_) j
  · fin_cases j <;> simp [compareValues, framedModInput, Fin.append, Fin.addCases, h5]
  · exact framedModInput_extra _ _ _ _ _ _ _

theorem binaryLt70_requires_of_scratchZero (v : BinaryValues 70) (h5 : v 5 = 0) :
    binaryLt70.requires v := by
  have h := binaryLt70_requires (v 0) (v 1) (v 2) (v 3) (v 4) (fun j ↦ v (j.natAdd 6))
  rwa [compareValues_repack v h5] at h

theorem binaryEq70_requires_of_scratchZero (v : BinaryValues 70) (h5 : v 5 = 0) :
    binaryEq70.requires v := by
  have h := binaryEq70_requires (v 0) (v 1) (v 2) (v 3) (v 4) (fun j ↦ v (j.natAdd 6))
  rwa [compareValues_repack v h5] at h

theorem binaryLt70_effect_of_scratchZero (v : BinaryValues 70) (h5 : v 5 = 0) :
    binaryLt70.effect v =
      compareValues (v 0) (v 1) (if v 0 < v 1 then 1 else 0) 0 0
        (fun j ↦ v (j.natAdd 6)) := by
  have h := binaryLt70_effect (v 0) (v 1) (v 2) (v 3) (v 4) (fun j ↦ v (j.natAdd 6))
  rwa [compareValues_repack v h5] at h

theorem binaryEq70_effect_of_scratchZero (v : BinaryValues 70) (h5 : v 5 = 0) :
    binaryEq70.effect v =
      compareValues (v 0) (v 1) (if v 0 = v 1 then 1 else 0) 0 0
        (fun j ↦ v (j.natAdd 6)) := by
  have h := binaryEq70_effect (v 0) (v 1) (v 2) (v 3) (v 4) (fun j ↦ v (j.natAdd 6))
  rwa [compareValues_repack v h5] at h

theorem binaryLt70_extra (v : BinaryValues 70) (h5 : v 5 = 0) (j : Fin 64) :
    binaryLt70.effect v (j.natAdd 6) = v (j.natAdd 6) := by
  rw [binaryLt70_effect_of_scratchZero v h5]
  exact framedModInput_extra _ _ _ _ _ _ _

theorem binaryEq70_extra (v : BinaryValues 70) (h5 : v 5 = 0) (j : Fin 64) :
    binaryEq70.effect v (j.natAdd 6) = v (j.natAdd 6) := by
  rw [binaryEq70_effect_of_scratchZero v h5]
  exact framedModInput_extra _ _ _ _ _ _ _

end SparseIrred.UpperBounds.Machine
