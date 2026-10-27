import SparseIrred.UpperBounds.Machine.StreamingMachineLinear
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Arithmetic
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Control
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FinCases

/-! # A concrete two-counter rectangular enumeration driver -/

namespace SparseIrred.UpperBounds.Machine

open Complexity BinaryRoutine
open scoped BigOperators

def coreReg (i : Fin 6) : Fin 70 := i.natAdd 64

@[simp] theorem coreReg_inj (i j : Fin 6) : coreReg i = coreReg j ↔ i = j := by
  constructor
  · intro h
    apply Fin.ext
    have := congrArg Fin.val h
    simp [coreReg] at this
    omega
  · intro h; rw [h]

/-- The low 64 registers are reusable workspace. Six persistent registers
hold input, limit, two loop counters, and two sums. -/
def coreValues (input X p a P A : ℕ) : BinaryValues 70 :=
  Fin.append (fun _ : Fin 64 ↦ 0) ![input, X, p, a, P, A]

@[simp] theorem coreValues_reg (input X p a P A : ℕ) (j : Fin 6) :
    coreValues input X p a P A (coreReg j) = ![input, X, p, a, P, A] j :=
  Fin.append_right _ _ _

/-- An internal compositional contract for a single already-implemented
cell. A final algorithm must instantiate this with its verified arithmetic
machine; the contract is not an external literature premise. -/
structure CoreCellSpec (cell : BinaryRoutine 70) (incP incA : ℕ → ℕ → ℕ → ℕ) where
  valid : ℕ → Prop
  requires : ∀ input X p a P A, valid input → p < X → a < X →
    cell.requires (coreValues input X p a P A)
  effect : ∀ input X p a P A, valid input → p < X → a < X →
    cell.effect (coreValues input X p a P A) =
      coreValues input X p a (P + incP input p a) (A + incA input p a)

def coreInner (cell : BinaryRoutine 70) : BinaryRoutine 70 :=
  binaryFor cell (coreReg 3) (coreReg 1)

def coreRow (cell : BinaryRoutine 70) : BinaryRoutine 70 :=
  seq (coreInner cell) (clear (coreReg 3))

def coreEnumeration (cell : BinaryRoutine 70) : BinaryRoutine 70 :=
  binaryFor (coreRow cell) (coreReg 2) (coreReg 1)

theorem coreInner_sound {cell : BinaryRoutine 70} (h : cell.Sound) : (coreInner cell).Sound :=
  h.binaryFor _ _

theorem coreRow_sound {cell : BinaryRoutine 70} (h : cell.Sound) : (coreRow cell).Sound :=
  (coreInner_sound h).seq (clear_sound _)

theorem coreEnumeration_sound {cell : BinaryRoutine 70} (h : cell.Sound) :
    (coreEnumeration cell).Sound := (coreRow_sound h).binaryFor _ _

theorem coreValues_update_a (input X p a P A b : ℕ) :
    Function.update (coreValues input X p a P A) (coreReg 3) b =
      coreValues input X p b P A := by
  funext j
  refine Fin.addCases (m := 64) (n := 6) (fun j ↦ ?_) (fun j ↦ ?_) j
  · have hne : j.castAdd 6 ≠ coreReg 3 := by
      intro h; have := congrArg Fin.val h; simp [coreReg] at this; omega
    simp [coreValues, hne]
  · change Function.update (coreValues input X p a P A) (coreReg 3) b (coreReg j) =
      coreValues input X p b P A (coreReg j)
    fin_cases j <;> simp

theorem coreValues_update_p (input X p a P A q : ℕ) :
    Function.update (coreValues input X p a P A) (coreReg 2) q =
      coreValues input X q a P A := by
  funext j
  refine Fin.addCases (m := 64) (n := 6) (fun j ↦ ?_) (fun j ↦ ?_) j
  · have hne : j.castAdd 6 ≠ coreReg 2 := by
      intro h; have := congrArg Fin.val h; simp [coreReg] at this; omega
    simp [coreValues, hne]
  · change Function.update (coreValues input X p a P A) (coreReg 2) q (coreReg j) =
      coreValues input X q a P A (coreReg j)
    fin_cases j <;> simp

theorem coreInner_values {cell : BinaryRoutine 70} {incP incA : ℕ → ℕ → ℕ → ℕ}
    (spec : CoreCellSpec cell incP incA) (input X p P A i : ℕ)
    (hvalid : spec.valid input) (hp : p < X) (hi : i ≤ X) :
    binaryForValues cell (coreReg 3) (coreValues input X p 0 P A) i =
      coreValues input X p i (P + ∑ a ∈ Finset.range i, incP input p a)
        (A + ∑ a ∈ Finset.range i, incA input p a) := by
  induction i with
  | zero => simp [binaryForValues]
  | succ i ih =>
    rw [binaryForValues, ih (by omega), binaryForStep,
      spec.effect _ _ _ _ _ _ hvalid hp (by omega)]
    simp only [coreValues_reg]
    rw [coreValues_update_a]
    simp [Finset.sum_range_succ, Nat.add_assoc]

theorem coreInner_requires {cell : BinaryRoutine 70} {incP incA : ℕ → ℕ → ℕ → ℕ}
    (spec : CoreCellSpec cell incP incA) (input X p P A : ℕ)
    (hvalid : spec.valid input) (hp : p < X) :
    (coreInner cell).requires (coreValues input X p 0 P A) := by
  refine ⟨by simp, by simp, ?_⟩
  intro i hi
  have hi' : i < X := by simpa [binaryForCount] using hi
  rw [coreInner_values spec _ _ _ _ _ _ hvalid hp hi'.le]
  refine ⟨spec.requires _ _ _ _ _ _ hvalid hp hi', ?_, ?_⟩ <;>
    rw [spec.effect _ _ _ _ _ _ hvalid hp hi'] <;> simp

theorem coreInner_effect {cell : BinaryRoutine 70} {incP incA : ℕ → ℕ → ℕ → ℕ}
    (spec : CoreCellSpec cell incP incA) (input X p P A : ℕ)
    (hvalid : spec.valid input) (hp : p < X) :
    (coreInner cell).effect (coreValues input X p 0 P A) =
      coreValues input X p X (P + ∑ a ∈ Finset.range X, incP input p a)
        (A + ∑ a ∈ Finset.range X, incA input p a) := by
  change binaryForValues cell (coreReg 3) (coreValues input X p 0 P A)
    (binaryForCount (coreReg 3) (coreReg 1) (coreValues input X p 0 P A)) = _
  have hcount : binaryForCount (coreReg 3) (coreReg 1) (coreValues input X p 0 P A) = X := by
    simp [binaryForCount]
  rw [hcount, coreInner_values spec _ _ _ _ _ _ hvalid hp le_rfl]

theorem coreRow_requires {cell : BinaryRoutine 70} {incP incA : ℕ → ℕ → ℕ → ℕ}
    (spec : CoreCellSpec cell incP incA) (input X p P A : ℕ)
    (hvalid : spec.valid input) (hp : p < X) :
    (coreRow cell).requires (coreValues input X p 0 P A) :=
  ⟨coreInner_requires spec _ _ _ _ _ hvalid hp, trivial⟩

theorem coreRow_effect {cell : BinaryRoutine 70} {incP incA : ℕ → ℕ → ℕ → ℕ}
    (spec : CoreCellSpec cell incP incA) (input X p P A : ℕ)
    (hvalid : spec.valid input) (hp : p < X) :
    (coreRow cell).effect (coreValues input X p 0 P A) =
      coreValues input X p 0 (P + ∑ a ∈ Finset.range X, incP input p a)
        (A + ∑ a ∈ Finset.range X, incA input p a) := by
  change Function.update ((coreInner cell).effect _) (coreReg 3) 0 = _
  rw [coreInner_effect spec _ _ _ _ _ hvalid hp, coreValues_update_a]

theorem coreEnumeration_values {cell : BinaryRoutine 70} {incP incA : ℕ → ℕ → ℕ → ℕ}
    (spec : CoreCellSpec cell incP incA) (input X P A i : ℕ)
    (hvalid : spec.valid input) (hi : i ≤ X) :
    binaryForValues (coreRow cell) (coreReg 2) (coreValues input X 0 0 P A) i =
      coreValues input X i 0
        (P + ∑ p ∈ Finset.range i, ∑ a ∈ Finset.range X, incP input p a)
        (A + ∑ p ∈ Finset.range i, ∑ a ∈ Finset.range X, incA input p a) := by
  induction i with
  | zero => simp [binaryForValues]
  | succ i ih =>
    rw [binaryForValues, ih (by omega), binaryForStep,
      coreRow_effect spec _ _ _ _ _ hvalid (by omega)]
    simp only [coreValues_reg]
    rw [coreValues_update_p]
    simp [Finset.sum_range_succ, Nat.add_assoc]

theorem coreEnumeration_requires {cell : BinaryRoutine 70} {incP incA : ℕ → ℕ → ℕ → ℕ}
    (spec : CoreCellSpec cell incP incA) (input X P A : ℕ) (hvalid : spec.valid input) :
    (coreEnumeration cell).requires (coreValues input X 0 0 P A) := by
  refine ⟨by simp, by simp, ?_⟩
  intro i hi
  have hi' : i < X := by simpa [binaryForCount] using hi
  rw [coreEnumeration_values spec _ _ _ _ _ hvalid hi'.le]
  refine ⟨coreRow_requires spec _ _ _ _ _ hvalid hi', ?_, ?_⟩ <;>
    rw [coreRow_effect spec _ _ _ _ _ hvalid hi'] <;> simp

/-- Exact rectangular enumeration: both binary counters contain their finite
double sums when the actual outer loop halts. -/
theorem coreEnumeration_effect {cell : BinaryRoutine 70} {incP incA : ℕ → ℕ → ℕ → ℕ}
    (spec : CoreCellSpec cell incP incA) (input X P A : ℕ) (hvalid : spec.valid input) :
    (coreEnumeration cell).effect (coreValues input X 0 0 P A) =
      coreValues input X X 0
        (P + ∑ p ∈ Finset.range X, ∑ a ∈ Finset.range X, incP input p a)
        (A + ∑ p ∈ Finset.range X, ∑ a ∈ Finset.range X, incA input p a) := by
  change binaryForValues (coreRow cell) (coreReg 2) (coreValues input X 0 0 P A)
    (binaryForCount (coreReg 2) (coreReg 1) (coreValues input X 0 0 P A)) = _
  have hcount : binaryForCount (coreReg 2) (coreReg 1) (coreValues input X 0 0 P A) = X := by
    simp [binaryForCount]
  rw [hcount, coreEnumeration_values spec _ _ _ _ _ hvalid le_rfl]

end SparseIrred.UpperBounds.Machine
