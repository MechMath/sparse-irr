import SparseIrred.UpperBounds.Machine.StreamingBinaryInput

/-! # Constant-register unframing of the packed sparse input -/
set_option maxHeartbeats 1200000
namespace SparseIrred.UpperBounds.Machine
open Complexity BinaryRoutine SparseDiv

def frameInputReg (k : ℕ) (i : Fin 8) : Fin (5 + (8 + k)) := (i.castAdd k).natAdd 5

@[simp] theorem frameInputReg_inj (k : ℕ) (i j : Fin 8) :
    frameInputReg k i = frameInputReg k j ↔ i = j := by simp [frameInputReg]

@[simp] theorem inputReg_ne_frameInputReg (k : ℕ) (i : Fin 5) (j : Fin 8) :
    inputReg (8 + k) i ≠ frameInputReg k j := inputReg_ne_extra _ _ _

@[simp] theorem frameInputReg_ne_inputReg (k : ℕ) (i : Fin 5) (j : Fin 8) :
    frameInputReg k j ≠ inputReg (8 + k) i := (inputReg_ne_frameInputReg k i j).symm

/-- Scratch layout after the five bit-reader registers: saved bit, payload,
power of two, copy scratch, addition counter, done flag, outer counter, limit. -/
def frameInputValues {k : ℕ} (n acc power done i limit : ℕ) (extra : Fin k → ℕ) :
    BinaryValues (5 + (8 + k)) :=
  inputDivTwoValues n 0 (Fin.append ![0, acc, power, 0, 0, done, i, limit] extra)

@[simp] theorem frameInputValues_low {k : ℕ} (n acc power done i limit : ℕ)
    (extra : Fin k → ℕ) (j : Fin 5) :
    frameInputValues n acc power done i limit extra (inputReg (8 + k) j) = ![n, 0, 0, 0, 0] j := by
  simp [frameInputValues]

@[simp] theorem frameInputValues_frame {k : ℕ} (n acc power done i limit : ℕ)
    (extra : Fin k → ℕ) (j : Fin 8) :
    frameInputValues n acc power done i limit extra (frameInputReg k j) =
      ![0, acc, power, 0, 0, done, i, limit] j := by
  simp [frameInputValues, frameInputReg]

@[simp] theorem frameInputValues_extra {k : ℕ} (n acc power done i limit : ℕ)
    (extra : Fin k → ℕ) (j : Fin k) :
    frameInputValues n acc power done i limit extra ((j.natAdd 8).natAdd 5) = extra j := by
  simp [frameInputValues]

def frameInputReadPair (k : ℕ) : BinaryRoutine (5 + (8 + k)) :=
  seq (inputReadBit (8 + k)) (seq
    (binaryCopy (inputReg (8 + k) 2) (frameInputReg k 0) (inputReg (8 + k) 4))
    (inputReadBit (8 + k)))

def frameInputAddPower (k : ℕ) : BinaryRoutine (5 + (8 + k)) :=
  add (frameInputReg k 2) (frameInputReg k 1) (frameInputReg k 4)

def frameInputDoublePower (k : ℕ) : BinaryRoutine (5 + (8 + k)) :=
  seq (binaryCopy (frameInputReg k 2) (frameInputReg k 3) (inputReg (8 + k) 4))
    (seq (add (frameInputReg k 3) (frameInputReg k 2) (frameInputReg k 4))
      (clear (frameInputReg k 3)))

def frameInputProcess (k : ℕ) : BinaryRoutine (5 + (8 + k)) :=
  branchZero (frameInputReg k 0)
    (branchZero (inputReg (8 + k) 2) (frameInputDoublePower k)
      (set (frameInputReg k 5) 1))
    (seq (frameInputAddPower k) (frameInputDoublePower k))

def frameInputBody (k : ℕ) : BinaryRoutine (5 + (8 + k)) :=
  branchZero (frameInputReg k 5)
    (seq (frameInputReadPair k) (seq (frameInputProcess k)
      (seq (clear (inputReg (8 + k) 2)) (clear (frameInputReg k 0))))) identity

theorem frameInputReadPair_sound (k : ℕ) : (frameInputReadPair k).Sound :=
  (inputReadBit_sound _).seq ((binaryCopy_sound _ _ _).seq (inputReadBit_sound _))

theorem frameInputAddPower_sound (k : ℕ) : (frameInputAddPower k).Sound := add_sound _ _ _

theorem frameInputDoublePower_sound (k : ℕ) : (frameInputDoublePower k).Sound :=
  (binaryCopy_sound _ _ _).seq ((add_sound _ _ _).seq (clear_sound _))

theorem frameInputProcess_sound (k : ℕ) : (frameInputProcess k).Sound :=
  ((frameInputDoublePower_sound k).branchZero
    (set_sound _ _) _).branchZero
      ((frameInputAddPower_sound k).seq (frameInputDoublePower_sound k)) _

theorem frameInputBody_sound (k : ℕ) : (frameInputBody k).Sound :=
  ((frameInputReadPair_sound k).seq ((frameInputProcess_sound k).seq
    ((clear_sound _).seq (clear_sound _)))).branchZero identity_sound _

private theorem append_inputReg (k : ℕ) (v : Fin 5 → ℕ) (extra : Fin (8 + k) → ℕ) (i : Fin 5) :
    Fin.append v extra (inputReg (8 + k) i) = v i := Fin.append_left _ _ _

private theorem append_frameInputReg (k : ℕ) (v : Fin 5 → ℕ) (extra : Fin (8 + k) → ℕ) (i : Fin 8) :
    Fin.append v extra (frameInputReg k i) = extra (i.castAdd k) := Fin.append_right _ _ _

private theorem saved_update_extra (k : ℕ) (i : Fin k) :
    (i.natAdd 8).natAdd 5 ≠ frameInputReg k 0 := by
  intro h
  have hh := congrArg Fin.val h
  simp [frameInputReg] at hh

/-- Reading two tape bits leaves their Boolean values in the two scratch cells. -/
theorem frameInputReadPair_effect {k : ℕ} (b c : Bool) (x : List Bool)
    (acc power done i limit : ℕ) (extra : Fin k → ℕ) :
    (frameInputReadPair k).effect (frameInputValues (packedInput (b :: c :: x)) acc power done i limit extra) =
      Fin.append ![packedInput x, 0, if c then 1 else 0, 0, 0]
        (Fin.append ![if b then 1 else 0, acc, power, 0, 0, done, i, limit] extra) := by
  simp only [frameInputReadPair, seq, inputReadBit_effect, binaryCopy]
  simp only [frameInputValues_low, Matrix.cons_val_zero, packedInput_div_two,
    packedInput_mod_two, append_inputReg, Function.update_apply,
    inputReg_ne_frameInputReg, ↓reduceIte, Matrix.cons_val_two]
  funext j
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
  · change Fin.append _ _ (inputReg (8 + k) j) = Fin.append _ _ (inputReg (8 + k) j)
    simp only [append_inputReg]
  · refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
    · change Fin.append _ _ (frameInputReg k j) = Fin.append _ _ (frameInputReg k j)
      fin_cases j <;> simp [append_frameInputReg, frameInputValues, frameInputReg]
    · simp [saved_update_extra, frameInputValues]

@[simp] theorem frameInput_extra_ne_reg (k : ℕ) (i : Fin k) (j : Fin 8) :
    (i.natAdd 8).natAdd 5 ≠ frameInputReg k j := by
  intro h
  have hh := congrArg Fin.val h
  simp [frameInputReg] at hh
  omega

@[simp] theorem frameInput_reg_ne_extra (k : ℕ) (i : Fin k) (j : Fin 8) :
    frameInputReg k j ≠ (i.natAdd 8).natAdd 5 := (frameInput_extra_ne_reg k i j).symm

theorem frameInputReadPair_requires {k : ℕ} (v : BinaryValues (5 + (8 + k))) :
    (frameInputReadPair k).requires v := by
  simp [frameInputReadPair, seq, inputReadBit_requires, binaryCopy,
    inputReadBit_effect, append_inputReg]

@[simp] theorem frameInputAddPower_effect {k : ℕ} (v : BinaryValues (5 + (8 + k))) :
    (frameInputAddPower k).effect v = Function.update v (frameInputReg k 1)
      (v (frameInputReg k 1) + v (frameInputReg k 2)) := rfl

@[simp] theorem frameInputDoublePower_effect {k : ℕ} (v : BinaryValues (5 + (8 + k))) :
    (frameInputDoublePower k).effect v = Function.update
      (Function.update v (frameInputReg k 2) (2 * v (frameInputReg k 2)))
      (frameInputReg k 3) 0 := by
  funext j
  by_cases h3 : j = frameInputReg k 3
  · subst j; simp [frameInputDoublePower, seq, binaryCopy, add, clear]
  · by_cases h2 : j = frameInputReg k 2
    · subst j; simp [frameInputDoublePower, seq, binaryCopy, add, clear, two_mul]
    · simp [frameInputDoublePower, seq, binaryCopy, add, clear, h2, h3]

/-- A doubled payload bit advances the input cursor and binary payload accumulator. -/
theorem frameInputBody_payload {k : ℕ} (b : Bool) (x : List Bool)
    (acc power i limit : ℕ) (extra : Fin k → ℕ) :
    (frameInputBody k).effect (frameInputValues (packedInput (b :: b :: x)) acc power 0 i limit extra) =
      frameInputValues (packedInput x) (acc + if b then power else 0) (2 * power) 0 i limit extra := by
  simp only [frameInputBody, branchZero, frameInputValues_frame, Matrix.cons_val_succ, Matrix.cons_val_zero,
    ↓reduceIte, seq, frameInputReadPair_effect]
  funext j
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
  · change (_ : BinaryValues (5 + (8 + k))) (inputReg (8 + k) j) =
      frameInputValues _ _ _ _ _ _ _ (inputReg (8 + k) j)
    fin_cases j <;> cases b <;>
      simp [frameInputProcess, branchZero, frameInputDoublePower_effect, frameInputAddPower_effect,
        seq, add, binaryCopy, clear, append_inputReg, append_frameInputReg]
  · refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
    · change (_ : BinaryValues (5 + (8 + k))) (frameInputReg k j) =
        frameInputValues _ _ _ _ _ _ _ (frameInputReg k j)
      fin_cases j <;> cases b <;>
        simp [frameInputProcess, branchZero, frameInputDoublePower_effect, frameInputAddPower_effect,
          seq, add, binaryCopy, clear, append_inputReg, append_frameInputReg, two_mul]
    · cases b <;>
        simp [frameInputProcess, branchZero, frameInputDoublePower_effect, frameInputAddPower_effect,
          seq, add, binaryCopy, clear, append_inputReg, append_frameInputReg]

/-- The delimiter finishes the payload and retains its exact natural value. -/
theorem frameInputBody_delimiter {k : ℕ} (x : List Bool)
    (acc power i limit : ℕ) (extra : Fin k → ℕ) :
    (frameInputBody k).effect (frameInputValues (packedInput (false :: true :: x)) acc power 0 i limit extra) =
      frameInputValues (packedInput x) acc power 1 i limit extra := by
  simp only [frameInputBody, branchZero, frameInputValues_frame, Matrix.cons_val_succ, Matrix.cons_val_zero,
    ↓reduceIte, seq, frameInputReadPair_effect]
  funext j
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
  · change (_ : BinaryValues (5 + (8 + k))) (inputReg (8 + k) j) =
      frameInputValues _ _ _ _ _ _ _ (inputReg (8 + k) j)
    fin_cases j <;>
      simp [frameInputProcess, branchZero, frameInputDoublePower_effect, frameInputAddPower_effect,
        seq, add, binaryCopy, clear, BinaryRoutine.set, addConst, append_inputReg, append_frameInputReg]
  · refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
    · change (_ : BinaryValues (5 + (8 + k))) (frameInputReg k j) =
        frameInputValues _ _ _ _ _ _ _ (frameInputReg k j)
      fin_cases j <;>
        simp [frameInputProcess, branchZero, frameInputDoublePower_effect, frameInputAddPower_effect,
          seq, add, binaryCopy, clear, BinaryRoutine.set, addConst, append_inputReg, append_frameInputReg]
    · simp [frameInputProcess, branchZero, frameInputDoublePower_effect, frameInputAddPower_effect,
        seq, add, binaryCopy, clear, BinaryRoutine.set, addConst, append_inputReg, append_frameInputReg]

/-- Completed readers ignore the remaining fixed loop budget. -/
theorem frameInputBody_done {k : ℕ} (n acc power i limit : ℕ) (extra : Fin k → ℕ) :
    (frameInputBody k).effect (frameInputValues n acc power 1 i limit extra) =
      frameInputValues n acc power 1 i limit extra := by
  simp [frameInputBody, branchZero, identity, emitBits]

theorem frameInputBody_requires {k : ℕ} (n acc power done i limit : ℕ) (extra : Fin k → ℕ) :
    (frameInputBody k).requires (frameInputValues n acc power done i limit extra) := by
  by_cases hd : done = 0
  · simp only [frameInputBody, branchZero, frameInputValues_frame]
    simp only [show ![0, acc, power, 0, 0, done, i, limit] (5 : Fin 8) = done by rfl,
      hd, ↓reduceIte, seq]
    refine ⟨frameInputReadPair_requires _, ?_⟩
    simp [frameInputProcess, branchZero, frameInputDoublePower, frameInputAddPower,
      frameInputReadPair, inputReadBit_effect, seq, binaryCopy, add, clear,
      BinaryRoutine.set, addConst, append_inputReg, append_frameInputReg,
      frameInputValues, frameInputReg]
  · simp [frameInputBody, branchZero, hd, identity, emitBits]

end SparseIrred.UpperBounds.Machine
