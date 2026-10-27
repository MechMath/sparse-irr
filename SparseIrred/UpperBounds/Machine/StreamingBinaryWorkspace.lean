import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Arithmetic
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.List
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.SpaceBounds

/-! # Reusable finite binary workspaces -/

namespace SparseIrred.UpperBounds.Machine
open Complexity BinaryRoutine

def clearRegisters {n : ℕ} (indices : List (Fin n)) : BinaryRoutine n :=
  seqList (indices.map clear)

theorem clearRegisters_sound {n : ℕ} (indices : List (Fin n)) :
    (clearRegisters indices).Sound := by
  apply seqList_sound
  intro r hr
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
  exact clear_sound i

theorem clearRegisters_requires {n : ℕ} (indices : List (Fin n)) (v : BinaryValues n) :
    (clearRegisters indices).requires v := by
  induction indices generalizing v with
  | nil => trivial
  | cons i indices ih => exact ⟨trivial, ih _⟩

theorem clearRegisters_effect {n : ℕ} (indices : List (Fin n)) (v : BinaryValues n)
    (i : Fin n) : (clearRegisters indices).effect v i = if i ∈ indices then 0 else v i := by
  induction indices generalizing v with
  | nil => simp [clearRegisters, seqList, identity, emitBits]
  | cons j indices ih =>
      change (clearRegisters indices).effect ((clear j).effect v) i = _
      rw [ih]
      by_cases hi : i ∈ indices <;> by_cases hij : i = j <;>
        simp [hi, hij, clear]

theorem clearRegisters_effect_le {n : ℕ} (indices : List (Fin n)) (v : BinaryValues n)
    (i : Fin n) : (clearRegisters indices).effect v i ≤ v i := by
  rw [clearRegisters_effect]
  split_ifs <;> omega

theorem clearRegisters_space {n : ℕ} (indices : List (Fin n))
    {S W : ℕ → ℕ} {v : ℕ → BinaryValues n}
    (hv : ∀ j i, v j i ≤ W j) : SpaceBoundByWidthAt (clearRegisters indices) S v W := by
  induction indices generalizing v with
  | nil => exact SpaceBoundByWidthAt.identity
  | cons i indices ih =>
      apply SpaceBoundByWidthAt.seq
      · exact SpaceBoundByWidthAt.clear i (fun j ↦ hv j i)
      · apply ih
        intro j z
        by_cases h : z = i <;> simp [clear, h, hv]

end SparseIrred.UpperBounds.Machine
