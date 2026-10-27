import SparseIrred.UpperBounds.Machine.StreamingBinaryWorkspace
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Control

/-! # Arithmetic routines leave the output stream untouched -/

namespace SparseIrred.UpperBounds.Machine
open Complexity BinaryRoutine

def RoutineSilent {n : ℕ} (r : BinaryRoutine n) : Prop := ∀ v, r.emitted v = []

theorem RoutineSilent.seq {n : ℕ} {r s : BinaryRoutine n}
    (hr : RoutineSilent r) (hs : RoutineSilent s) : RoutineSilent (seq r s) := by
  intro v
  simp [BinaryRoutine.seq, hr v, hs (r.effect v)]

theorem RoutineSilent.branchZero {n : ℕ} {r s : BinaryRoutine n}
    (hr : RoutineSilent r) (hs : RoutineSilent s) (i : Fin n) :
    RoutineSilent (branchZero i r s) := by
  intro v
  simp only [BinaryRoutine.branchZero]
  split_ifs <;> simp_all [RoutineSilent]

theorem RoutineSilent.binaryFor {n : ℕ} {r : BinaryRoutine n}
    (hr : RoutineSilent r) (i j : Fin n) : RoutineSilent (binaryFor r i j) := by
  intro v
  have h : ∀ count, binaryForEmitted r i v count = [] := by
    intro count
    induction count with
    | zero => rfl
    | succ count ih => rw [binaryForEmitted, ih, hr _]; rfl
  exact h _

theorem routineSilent_clear {n : ℕ} (i : Fin n) : RoutineSilent (clear i) := fun _ ↦ rfl
theorem routineSilent_set {n : ℕ} (i : Fin n) (v : ℕ) :
    RoutineSilent (BinaryRoutine.set i v) := fun _ ↦ rfl
theorem routineSilent_succ {n : ℕ} (i : Fin n) : RoutineSilent (binarySucc i) := fun _ ↦ rfl
theorem routineSilent_pred {n : ℕ} (i : Fin n) : RoutineSilent (binaryPred i) := fun _ ↦ rfl
theorem routineSilent_copy {n : ℕ} (i j k : Fin n) :
    RoutineSilent (binaryCopy i j k) := fun _ ↦ rfl
theorem routineSilent_add {n : ℕ} (i j k : Fin n) :
    RoutineSilent (add i j k) := fun _ ↦ rfl
theorem routineSilent_mulAdd {n : ℕ} (i j k l m : Fin n) :
    RoutineSilent (mulAdd i j k l m) := fun _ ↦ rfl
theorem routineSilent_identity {n : ℕ} : RoutineSilent (identity : BinaryRoutine n) :=
  fun _ ↦ rfl

theorem routineSilent_clearRegisters {n : ℕ} (indices : List (Fin n)) :
    RoutineSilent (clearRegisters indices) := by
  induction indices with
  | nil => exact routineSilent_identity
  | cons i is ih => exact (routineSilent_clear i).seq ih

end SparseIrred.UpperBounds.Machine
