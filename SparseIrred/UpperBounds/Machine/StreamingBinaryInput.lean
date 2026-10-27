import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Arithmetic
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Control
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.SpaceBounds
import SparseDivComplexity.Encoding
import Mathlib.Tactic.FinCases

/-! # Reading a packed input bit in linear auxiliary space

A binary input `x` is packed as `decNat (x ++ [true])`; the final one preserves
trailing zero bits. Repeated division by two reads the original bits from left
to right. The routine below is an actual five-register Turing-machine program,
with arbitrary additional registers preserved, and an all-prefix width bound.
-/
namespace SparseIrred.UpperBounds.Machine
open Complexity BinaryRoutine SparseDiv

def inputReg (k : ℕ) (i : Fin 5) : Fin (5 + k) := i.castAdd k

@[simp] theorem inputReg_inj (k : ℕ) (i j : Fin 5) : inputReg k i = inputReg k j ↔ i = j := by
  simp [inputReg]

@[simp] theorem inputReg_ne_extra (k : ℕ) (i : Fin 5) (j : Fin k) :
    inputReg k i ≠ j.natAdd 5 := by
  intro h
  have hh := congrArg Fin.val h
  simp [inputReg] at hh
  omega

@[simp] theorem extra_ne_inputReg (k : ℕ) (i : Fin 5) (j : Fin k) :
    j.natAdd 5 ≠ inputReg k i := (inputReg_ne_extra k i j).symm

/-- Toggle the parity and increment the quotient after every second unit. -/
def inputDivTwoBody (k : ℕ) : BinaryRoutine (5 + k) :=
  branchZero (inputReg k 2) (binarySucc (inputReg k 2))
    (seq (clear (inputReg k 2)) (binarySucc (inputReg k 1)))

def inputDivTwoLoop (k : ℕ) : BinaryRoutine (5 + k) :=
  binaryFor (inputDivTwoBody k) (inputReg k 3) (inputReg k 0)

theorem inputDivTwoBody_sound (k : ℕ) : (inputDivTwoBody k).Sound :=
  (binarySucc_sound _).branchZero ((clear_sound _).seq (binarySucc_sound _)) _

theorem inputDivTwoLoop_sound (k : ℕ) : (inputDivTwoLoop k).Sound :=
  (inputDivTwoBody_sound k).binaryFor _ _

/-- Five front registers: source, quotient, parity, loop counter, zero scratch. -/
def inputDivTwoValues {k : ℕ} (n i : ℕ) (extra : Fin k → ℕ) : BinaryValues (5 + k) :=
  Fin.append ![n, i / 2, i % 2, i, 0] extra

@[simp] theorem inputDivTwoValues_reg {k : ℕ} (n i : ℕ) (extra : Fin k → ℕ) (j : Fin 5) :
    inputDivTwoValues n i extra (inputReg k j) = ![n, i / 2, i % 2, i, 0] j :=
  Fin.append_left _ _ _

@[simp] theorem inputDivTwoValues_extra {k : ℕ} (n i : ℕ) (extra : Fin k → ℕ) (j : Fin k) :
    inputDivTwoValues n i extra (j.natAdd 5) = extra j := Fin.append_right _ _ _

theorem inputDivTwoBody_requires {k : ℕ} (n i : ℕ) (extra : Fin k → ℕ) :
    (inputDivTwoBody k).requires (inputDivTwoValues n i extra) := by
  by_cases h : i % 2 = 0 <;> simp [inputDivTwoBody, branchZero, h, seq, clear, binarySucc]

theorem inputDivTwoBody_step {k : ℕ} (n i : ℕ) (extra : Fin k → ℕ) :
    binaryForStep (inputDivTwoBody k) (inputReg k 3) (inputDivTwoValues n i extra) =
      inputDivTwoValues n (i + 1) extra := by
  have hrem := Nat.mod_lt i (by decide : 0 < 2)
  have hdecomp := Nat.mod_add_div i 2
  by_cases h : i % 2 = 0
  · have hq : (i + 1) / 2 = i / 2 := by omega
    have hr : (i + 1) % 2 = 1 := by omega
    funext j
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
    · change binaryForStep (inputDivTwoBody k) (inputReg k 3)
        (inputDivTwoValues n i extra) (inputReg k j) = inputDivTwoValues n (i + 1) extra (inputReg k j)
      fin_cases j <;> simp [binaryForStep, inputDivTwoBody, branchZero, h, hq, hr, binarySucc]
    · simp [binaryForStep, inputDivTwoBody, branchZero, h, binarySucc]
  · have hq : (i + 1) / 2 = i / 2 + 1 := by omega
    have hr : (i + 1) % 2 = 0 := by omega
    funext j
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
    · change binaryForStep (inputDivTwoBody k) (inputReg k 3)
        (inputDivTwoValues n i extra) (inputReg k j) = inputDivTwoValues n (i + 1) extra (inputReg k j)
      fin_cases j <;> simp [binaryForStep, inputDivTwoBody, branchZero, h, hq, hr,
        seq, clear, binarySucc]
    · simp [binaryForStep, inputDivTwoBody, branchZero, h, seq, clear, binarySucc]

theorem inputDivTwoBody_preserves {k : ℕ} (n i : ℕ) (extra : Fin k → ℕ) :
    (inputDivTwoBody k).effect (inputDivTwoValues n i extra) (inputReg k 3) = i ∧
      (inputDivTwoBody k).effect (inputDivTwoValues n i extra) (inputReg k 0) = n := by
  by_cases h : i % 2 = 0 <;>
    simp [inputDivTwoBody, branchZero, h, seq, clear, binarySucc]

theorem inputDivTwoLoop_values {k : ℕ} (n i : ℕ) (extra : Fin k → ℕ) :
    binaryForValues (inputDivTwoBody k) (inputReg k 3) (inputDivTwoValues n 0 extra) i =
      inputDivTwoValues n i extra := by
  induction i with
  | zero => rfl
  | succ i ih => rw [binaryForValues, ih, inputDivTwoBody_step]

theorem inputDivTwoLoop_requires {k : ℕ} (n : ℕ) (extra : Fin k → ℕ) :
    (inputDivTwoLoop k).requires (inputDivTwoValues n 0 extra) := by
  refine ⟨by simp, by simp, ?_⟩
  intro i hi
  rw [inputDivTwoLoop_values]
  exact ⟨inputDivTwoBody_requires n i extra, (inputDivTwoBody_preserves n i extra).1,
    (inputDivTwoBody_preserves n i extra).2⟩

theorem inputDivTwoLoop_effect {k : ℕ} (n : ℕ) (extra : Fin k → ℕ) :
    (inputDivTwoLoop k).effect (inputDivTwoValues n 0 extra) = inputDivTwoValues n n extra := by
  change binaryForValues (inputDivTwoBody k) (inputReg k 3) (inputDivTwoValues n 0 extra)
    (binaryForCount (inputReg k 3) (inputReg k 0) (inputDivTwoValues n 0 extra)) = _
  have hc : binaryForCount (inputReg k 3) (inputReg k 0) (inputDivTwoValues n 0 extra) = n := by
    simp [binaryForCount]
  rw [hc, inputDivTwoLoop_values]

/-- Consume the low bit and reset temporary registers for the next call. -/
def inputPopBit (k : ℕ) : BinaryRoutine (5 + k) :=
  seq (inputDivTwoLoop k)
    (seq (binaryCopy (inputReg k 1) (inputReg k 0) (inputReg k 4))
      (seq (clear (inputReg k 1)) (clear (inputReg k 3))))

theorem inputPopBit_sound (k : ℕ) : (inputPopBit k).Sound :=
  (inputDivTwoLoop_sound k).seq ((binaryCopy_sound _ _ _).seq
    ((clear_sound _).seq (clear_sound _)))

theorem inputPopBit_requires {k : ℕ} (n : ℕ) (extra : Fin k → ℕ) :
    (inputPopBit k).requires (inputDivTwoValues n 0 extra) := by
  simp only [inputPopBit, seq]
  refine ⟨inputDivTwoLoop_requires n extra, ?_⟩
  rw [inputDivTwoLoop_effect]
  simp [binaryCopy, clear]

theorem inputPopBit_effect {k : ℕ} (n : ℕ) (extra : Fin k → ℕ) :
    (inputPopBit k).effect (inputDivTwoValues n 0 extra) =
      Fin.append ![n / 2, 0, n % 2, 0, 0] extra := by
  simp only [inputPopBit, seq]
  rw [inputDivTwoLoop_effect]
  funext j
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
  · change (clear (inputReg k 3)).effect ((clear (inputReg k 1)).effect
      ((binaryCopy (inputReg k 1) (inputReg k 0) (inputReg k 4)).effect
        (inputDivTwoValues n n extra))) (inputReg k j) = _
    fin_cases j <;> simp [binaryCopy, clear]
  · simp [binaryCopy, clear]

theorem inputDivTwoBody_space (k : ℕ) {S W : ℕ → ℕ} {v : ℕ → BinaryValues (5 + k)}
    (hv : ∀ j i, v j i ≤ W j) : SpaceBoundByWidthAt (inputDivTwoBody k) S v W := by
  apply SpaceBoundByWidthAt.branchZero
  · exact SpaceBoundByWidthAt.binarySucc _ (fun j ↦ hv j _)
  · apply SpaceBoundByWidthAt.seq
    · exact SpaceBoundByWidthAt.clear _ (fun j ↦ hv j _)
    · apply SpaceBoundByWidthAt.binarySucc
      intro j
      simpa [clear] using hv j (inputReg k 1)

theorem inputDivTwoValues_le {k : ℕ} (n i W : ℕ) (extra : Fin k → ℕ)
    (hn : n ≤ W) (hi : i ≤ n) (he : ∀ j, extra j ≤ W) (j : Fin (5 + k)) :
    inputDivTwoValues n i extra j ≤ W := by
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
  · change inputDivTwoValues n i extra (inputReg k j) ≤ W
    have hdiv := Nat.div_le_self i 2
    have hmod := Nat.mod_le i 2
    fin_cases j <;> simp <;> omega
  · simpa using he j

theorem inputDivTwoLoop_space (k : ℕ) (n W : ℕ → ℕ) (extra : ℕ → Fin k → ℕ)
    (hn : ∀ j, n j ≤ W j) (he : ∀ j i, extra j i ≤ W j) (S : ℕ → ℕ) :
    SpaceBoundByWidthAt (inputDivTwoLoop k) S
      (fun j ↦ inputDivTwoValues (n j) 0 (extra j)) W := by
  apply SpaceBoundByWidthAt.binaryFor_of_clamped_body
  · intro j; simpa using hn j
  · intro j count hc
    rw [inputDivTwoLoop_values]
    apply inputDivTwoValues_le _ _ _ _ (hn j) _ (he j)
    simpa [binaryForCount] using Nat.le_of_lt hc
  · apply inputDivTwoBody_space
    intro code idx
    unfold binaryForClampedValues
    rw [inputDivTwoLoop_values]
    apply inputDivTwoValues_le _ _ _ _ (hn _) _ (he _)
    simp [binaryForCount]

theorem inputPopBit_space (k : ℕ) (n W : ℕ → ℕ) (extra : ℕ → Fin k → ℕ)
    (hn : ∀ j, n j ≤ W j) (he : ∀ j i, extra j i ≤ W j) (S : ℕ → ℕ) :
    SpaceBoundByWidthAt (inputPopBit k) S
      (fun j ↦ inputDivTwoValues (n j) 0 (extra j)) W := by
  apply SpaceBoundByWidthAt.seq
  · exact inputDivTwoLoop_space k n W extra hn he S
  · apply SpaceBoundByWidthAt.seq
    · apply SpaceBoundByWidthAt.binaryCopy
      · intro j
        simp only [inputDivTwoLoop_effect, inputDivTwoValues_reg]
        exact (Nat.div_le_self _ _).trans (hn j)
      · intro j
        simpa [inputDivTwoLoop_effect] using hn j
    · apply SpaceBoundByWidthAt.seq
      · apply SpaceBoundByWidthAt.clear
        intro j
        simp only [inputDivTwoLoop_effect, binaryCopy, inputReg_inj, OfNat.ofNat_ne_zero,
          Function.update_of_ne, inputDivTwoValues_reg]
        simp
        exact (Nat.div_le_self _ _).trans (hn j)
      · apply SpaceBoundByWidthAt.clear
        intro j
        simpa [inputDivTwoLoop_effect, binaryCopy, clear] using hn j

/-- Sentinel-terminated little-endian binary input, preserving every zero bit. -/
def packedInput (x : List Bool) : ℕ := decNat (x ++ [true])

@[simp] theorem packedInput_nil : packedInput [] = 1 := by
  simp [packedInput, decNat_cons]

@[simp] theorem packedInput_cons (b : Bool) (x : List Bool) :
    packedInput (b :: x) = (if b then 1 else 0) + 2 * packedInput x := by
  simp only [packedInput, List.cons_append, decNat_cons]

theorem packedInput_pos (x : List Bool) : 0 < packedInput x := by
  induction x with
  | nil => simp
  | cons b x ih => rw [packedInput_cons]; split <;> omega

@[simp] theorem packedInput_bits (x : List Bool) : (packedInput x).bits = x ++ [true] := by
  induction x with
  | nil => simp
  | cons b x ih =>
    have hp := packedInput_pos x
    cases b
    · simp only [packedInput_cons, Bool.false_eq_true, ↓reduceIte, zero_add]
      rw [Nat.bit0_bits _ (by omega), ih]
      rfl
    · simp only [packedInput_cons, ↓reduceIte]
      rw [Nat.add_comm 1, Nat.bit1_bits, ih]
      rfl

@[simp] theorem packedInput_size (x : List Bool) : (packedInput x).size = x.length + 1 := by
  rw [← Nat.size_eq_bits_len, packedInput_bits, List.length_append]
  rfl

@[simp] theorem packedInput_div_two (b : Bool) (x : List Bool) :
    packedInput (b :: x) / 2 = packedInput x := by
  rw [packedInput_cons]
  split <;> omega

@[simp] theorem packedInput_mod_two (b : Bool) (x : List Bool) :
    packedInput (b :: x) % 2 = if b then 1 else 0 := by
  rw [packedInput_cons]
  split <;> omega

/-- A real machine invocation extracts precisely the next input bit and tail. -/
theorem inputPopBit_packed_effect {k : ℕ} (b : Bool) (x : List Bool) (extra : Fin k → ℕ) :
    (inputPopBit k).effect (inputDivTwoValues (packedInput (b :: x)) 0 extra) =
      Fin.append ![packedInput x, 0, if b then 1 else 0, 0, 0] extra := by
  rw [inputPopBit_effect, packedInput_div_two, packedInput_mod_two]

/-- Canonicalize the four disposable bit-reader registers before each use. -/
def inputReadReset (k : ℕ) : BinaryRoutine (5 + k) :=
  seq (clear (inputReg k 1)) (seq (clear (inputReg k 2))
    (seq (clear (inputReg k 3)) (clear (inputReg k 4))))

theorem inputReadReset_sound (k : ℕ) : (inputReadReset k).Sound :=
  (clear_sound _).seq ((clear_sound _).seq ((clear_sound _).seq (clear_sound _)))

theorem inputReadReset_effect {k : ℕ} (v : BinaryValues (5 + k)) :
    (inputReadReset k).effect v =
      inputDivTwoValues (v (inputReg k 0)) 0 (fun j ↦ v (j.natAdd 5)) := by
  funext j
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
  · change (inputReadReset k).effect v (inputReg k j) =
      inputDivTwoValues (v (inputReg k 0)) 0 (fun j ↦ v (j.natAdd 5)) (inputReg k j)
    fin_cases j <;> simp [inputReadReset, seq, clear]
  · simp [inputReadReset, seq, clear]

/-- Reusable input-bit reader, with no hypothesis on the scratch-register contents. -/
def inputReadBit (k : ℕ) : BinaryRoutine (5 + k) :=
  seq (inputReadReset k) (inputPopBit k)

theorem inputReadBit_sound (k : ℕ) : (inputReadBit k).Sound :=
  (inputReadReset_sound k).seq (inputPopBit_sound k)

theorem inputReadBit_requires {k : ℕ} (v : BinaryValues (5 + k)) :
    (inputReadBit k).requires v := by
  refine ⟨by simp [inputReadReset, seq, clear], ?_⟩
  rw [inputReadReset_effect]
  exact inputPopBit_requires _ _

theorem inputReadBit_effect {k : ℕ} (v : BinaryValues (5 + k)) :
    (inputReadBit k).effect v =
      Fin.append ![v (inputReg k 0) / 2, 0, v (inputReg k 0) % 2, 0, 0]
        (fun j ↦ v (j.natAdd 5)) := by
  simp only [inputReadBit, seq, inputReadReset_effect, inputPopBit_effect]

theorem inputReadReset_space (k : ℕ) {S W : ℕ → ℕ} {v : ℕ → BinaryValues (5 + k)}
    (hv : ∀ j i, v j i ≤ W j) : SpaceBoundByWidthAt (inputReadReset k) S v W := by
  apply SpaceBoundByWidthAt.seq
  · exact SpaceBoundByWidthAt.clear _ (fun j ↦ hv j _)
  · apply SpaceBoundByWidthAt.seq
    · apply SpaceBoundByWidthAt.clear
      intro j; simpa [clear] using hv j (inputReg k 2)
    · apply SpaceBoundByWidthAt.seq
      · apply SpaceBoundByWidthAt.clear
        intro j; simpa [clear] using hv j (inputReg k 3)
      · apply SpaceBoundByWidthAt.clear
        intro j; simpa [clear] using hv j (inputReg k 4)

theorem inputReadBit_space (k : ℕ) {S W : ℕ → ℕ} {v : ℕ → BinaryValues (5 + k)}
    (hv : ∀ j i, v j i ≤ W j) : SpaceBoundByWidthAt (inputReadBit k) S v W := by
  apply SpaceBoundByWidthAt.seq
  · exact inputReadReset_space k hv
  · simp only [inputReadReset_effect]
    exact inputPopBit_space k _ _ _ (fun j ↦ hv j _) (fun j i ↦ hv j _) S

end SparseIrred.UpperBounds.Machine
