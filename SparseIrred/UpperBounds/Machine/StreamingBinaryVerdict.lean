import SparseIrred.UpperBounds.Machine.StreamingBinaryArithmeticSilent
import SparseIrred.UpperBounds.Machine.StreamingBinaryCompareSpace

/-! # Actual final output of the deterministic enumeration machine -/
namespace SparseIrred.UpperBounds.Machine
open Complexity BinaryRoutine

def coreVerdictDouble : BinaryRoutine 70 :=
  seq (binaryCopy (coreReg 5) 0 5) (add (coreReg 5) 0 5)

def coreVerdictTriple : BinaryRoutine 70 :=
  seq (binaryCopy (coreReg 4) 1 5) (seq (add (coreReg 4) 1 5) (add (coreReg 4) 1 5))

def coreVerdictLoad : BinaryRoutine 70 :=
  seq (clear 5) (seq coreVerdictDouble coreVerdictTriple)

/-- Emit one literal decision bit after comparing `2*A` with `3*P`. -/
def coreVerdict : BinaryRoutine 70 :=
  seq (seq coreVerdictLoad binaryLt70) (branchZero 2 (emitBits [false]) (emitBits [true]))

theorem coreVerdictDouble_sound : coreVerdictDouble.Sound :=
  (binaryCopy_sound _ _ _).seq (add_sound _ _ _)

theorem coreVerdictTriple_sound : coreVerdictTriple.Sound :=
  (binaryCopy_sound _ _ _).seq ((add_sound _ _ _).seq (add_sound _ _ _))

theorem coreVerdictLoad_sound : coreVerdictLoad.Sound :=
  (clear_sound _).seq (coreVerdictDouble_sound.seq coreVerdictTriple_sound)

theorem coreVerdict_sound : coreVerdict.Sound :=
  (coreVerdictLoad_sound.seq binaryLt70_sound).seq
    ((emitBits_sound _).branchZero (emitBits_sound _) _)

theorem coreVerdictLoad_requires (v : BinaryValues 70) : coreVerdictLoad.requires v := by
  simp [coreVerdictLoad, coreVerdictDouble, coreVerdictTriple, seq, clear, binaryCopy, add, coreReg]

theorem coreVerdictLoad_effect (v : BinaryValues 70) :
    coreVerdictLoad.effect v = compareValues (2 * v (coreReg 5)) (3 * v (coreReg 4))
      (v 2) (v 3) (v 4) (fun j ↦ v (j.natAdd 6)) := by
  dsimp only [coreVerdictLoad, coreVerdictDouble, coreVerdictTriple, seq, clear, binaryCopy, add]
  conv_lhs => simp [coreReg]
  funext j
  refine Fin.addCases (m := 6) (n := 64) (fun j ↦ ?_) (fun j ↦ ?_) j
  · fin_cases j <;> simp [compareValues, framedModInput, Fin.append, Fin.addCases, coreReg] <;> omega
  · simp only [compareValues, framedModInput, Fin.append_right]
    have h0 : j.natAdd 6 ≠ (0 : Fin 70) := by intro h; have := congrArg Fin.val h; simp at this
    have h1 : j.natAdd 6 ≠ (1 : Fin 70) := by intro h; have := congrArg Fin.val h; simp at this; omega
    have h5 : j.natAdd 6 ≠ (5 : Fin 70) := by intro h; have := congrArg Fin.val h; simp at this; omega
    simp [h0, h1, h5]

theorem coreVerdict_requires (v : BinaryValues 70) : coreVerdict.requires v := by
  refine ⟨⟨coreVerdictLoad_requires v, ?_⟩, ?_⟩
  · rw [coreVerdictLoad_effect]
    exact binaryLt70_requires _ _ _ _ _ _
  · simp [branchZero, emitBits]

theorem coreVerdictLoad_silent : RoutineSilent coreVerdictLoad :=
  (routineSilent_clear _).seq (((routineSilent_copy _ _ _).seq (routineSilent_add _ _ _)).seq
    ((routineSilent_copy _ _ _).seq ((routineSilent_add _ _ _).seq (routineSilent_add _ _ _))))

/-- Exactly the paper's strict deterministic threshold is emitted by the real machine. -/
theorem coreVerdict_emitted (v : BinaryValues 70) :
    coreVerdict.emitted v = [decide (2 * v (coreReg 5) < 3 * v (coreReg 4))] := by
  simp only [coreVerdict, seq, coreVerdictLoad_silent v,
    binaryLt70_silent (coreVerdictLoad.effect v), List.nil_append]
  rw [coreVerdictLoad_effect, binaryLt70_effect]
  simp only [branchZero, emitBits]
  change (if (if 2 * v (coreReg 5) < 3 * v (coreReg 4) then 1 else 0) = 0 then [false] else [true]) = _
  by_cases h : 2 * v (coreReg 5) < 3 * v (coreReg 4) <;> simp [h]

/-- Computing and emitting the verdict leaves all six persistent registers intact. -/
theorem coreVerdict_effect_core (v : BinaryValues 70) (i : Fin 6) :
    coreVerdict.effect v (coreReg i) = v (coreReg i) := by
  simp only [coreVerdict, seq, branchZero, emitBits]
  split_ifs <;> rw [coreVerdictLoad_effect, binaryLt70_effect]
  all_goals
    let j : Fin 64 := ⟨58 + i.val, by have := i.isLt; omega⟩
    have hj : j.natAdd 6 = coreReg i := by apply Fin.ext; simp [j, coreReg]; omega
    rw [← hj]
    exact framedModInput_extra _ _ _ _ _ _ _

theorem coreVerdictDouble_values_le (v : BinaryValues 70) (W : ℕ)
    (hv : ∀ i, v i ≤ W) (i : Fin 70) : coreVerdictDouble.effect v i ≤ 2 * W := by
  have hcopy := values_update_le (0 : Fin 70) hv (hv (coreReg 5))
  have hsum : (binaryCopy (coreReg 5) 0 5).effect v 0 +
      (binaryCopy (coreReg 5) 0 5).effect v (coreReg 5) ≤ 2 * W := by
    simpa only [binaryCopy, two_mul] using Nat.add_le_add (hcopy 0) (hcopy (coreReg 5))
  exact values_update_le 0 (fun j ↦ (hcopy j).trans (by omega)) hsum i

theorem coreVerdictDouble_space {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (hv : ∀ j i, v j i ≤ W j) :
    SpaceBoundByWidthAt coreVerdictDouble S v (fun j ↦ 2 * W j) := by
  apply SpaceBoundByWidthAt.seq
  · exact (SpaceBoundByWidthAt.binaryCopy _ _ _ (fun j ↦ hv j _) (fun j ↦ hv j _)).mono
      (by intro j; omega)
  · apply SpaceBoundByWidthAt.add
    · intro j; simp [binaryCopy, coreReg]; have := hv j (coreReg 5); simpa [coreReg] using this.trans (by omega)
    · intro j; simp [binaryCopy, coreReg]; have := hv j (coreReg 5); simp [coreReg] at this; omega

theorem coreVerdictTriple_space {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (hv : ∀ j i, v j i ≤ W j) :
    SpaceBoundByWidthAt coreVerdictTriple S v (fun j ↦ 3 * W j) := by
  apply SpaceBoundByWidthAt.seq
  · exact (SpaceBoundByWidthAt.binaryCopy _ _ _ (fun j ↦ hv j _) (fun j ↦ hv j _)).mono
      (by intro j; omega)
  · apply SpaceBoundByWidthAt.seq
    · apply SpaceBoundByWidthAt.add
      · intro j; simp [binaryCopy, coreReg]; have := hv j (coreReg 4); simp [coreReg] at this; omega
      · intro j; simp [binaryCopy, coreReg]; have := hv j (coreReg 4); simp [coreReg] at this; omega
    · apply SpaceBoundByWidthAt.add
      · intro j; simp [binaryCopy, add, coreReg]; have := hv j (coreReg 4); simp [coreReg] at this; omega
      · intro j; simp [binaryCopy, add, coreReg]; have := hv j (coreReg 4); simp [coreReg] at this; omega

theorem coreVerdictLoad_values_le (v : BinaryValues 70) (W : ℕ)
    (hv : ∀ i, v i ≤ W) (i : Fin 70) : coreVerdictLoad.effect v i ≤ 3 * W := by
  rw [coreVerdictLoad_effect]
  refine Fin.addCases (m := 6) (n := 64) (fun j ↦ ?_) (fun j ↦ ?_) i
  · fin_cases j <;> simp [compareValues, framedModInput, Fin.append, Fin.addCases]
    all_goals first | exact (hv _).trans (by omega) | have := hv (coreReg 5); omega | have := hv (coreReg 4); omega
  · simp only [compareValues, framedModInput, Fin.append_right]
    have := hv (j.natAdd 6)
    omega

theorem coreVerdictLoad_space {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (hv : ∀ j i, v j i ≤ W j) : SpaceBoundByWidthAt coreVerdictLoad S v W := by
  have hv1 := fun j ↦ values_update_le (5 : Fin 70) (hv j) (Nat.zero_le (W j))
  have hv2 := fun j ↦ coreVerdictDouble_values_le _ _ (hv1 j)
  apply spaceWidth_mul_add 6
  apply SpaceBoundByWidthAt.seq
  · exact (SpaceBoundByWidthAt.clear _ (fun j ↦ hv j _)).mono (by intro j; omega)
  · apply SpaceBoundByWidthAt.seq
    · exact (coreVerdictDouble_space hv1).mono (by intro j; omega)
    · exact (coreVerdictTriple_space hv2).mono (by intro j; omega)

/-- The final arithmetic comparison and one-bit output preserve linear binary width. -/
theorem coreVerdict_space {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (hv : ∀ j i, v j i ≤ W j) : SpaceBoundByWidthAt coreVerdict S v W := by
  apply SpaceBoundByWidthAt.seq
  · apply SpaceBoundByWidthAt.seq
    · exact coreVerdictLoad_space hv
    · apply spaceWidth_mul_add 3
      have h5 : ∀ j, coreVerdictLoad.effect (v j) 5 = 0 := by
        intro j; rw [coreVerdictLoad_effect]; rfl
      exact (binaryLt70_space_of_scratchZero h5 (fun j ↦ coreVerdictLoad_values_le _ _ (hv j))).mono
        (by intro j; omega)
  · apply SpaceBoundByWidthAt.branchZero
    · exact SpaceBoundByWidthAt.emitBits [false]
    · exact SpaceBoundByWidthAt.emitBits [true]

end SparseIrred.UpperBounds.Machine
