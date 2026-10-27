import SparseIrred.UpperBounds.Machine.StreamingBinaryPrimeTotal
import SparseIrred.UpperBounds.Machine.StreamingBinaryWorkspace
import SparseIrred.UpperBounds.Machine.StreamingBinaryCore
import SparseIrred.UpperBounds.Machine.StreamingBinaryCompareSpace

/-! # Reusable arithmetic adapters for one prime/residue enumeration cell -/

namespace SparseIrred.UpperBounds.Machine
open Complexity BinaryRoutine

def prime70Reset : BinaryRoutine 70 := clearRegisters [1, 2, 3, 4, 5, 6]

def prime70Extra (v : BinaryValues 70) : Fin 63 → ℕ := fun i ↦ v (i.natAdd 7)

theorem prime70Reset_effect (v : BinaryValues 70) :
    prime70Reset.effect v = binaryPrimeValues (v 0) 0 0 (prime70Extra v) := by
  funext i
  refine Fin.addCases (m := 6) (n := 64) (fun i ↦ ?_) (fun i ↦ ?_) i
  · fin_cases i <;> simp [prime70Reset, clearRegisters_effect,
      binaryPrimeValues, framedModInput, Fin.append, Fin.addCases]
  · refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [prime70Reset, clearRegisters_effect, binaryPrimeValues, framedModInput,
        Fin.append, Fin.addCases]
    · have hn : (j.succ.natAdd 6 : Fin 70) ∉ [1, 2, 3, 4, 5, 6] := by
        intro hm
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
        rcases hm with h | h | h | h | h | h <;>
          have hh := congrArg (fun z : Fin 70 ↦ z.val) h <;>
          norm_num [Fin.val_natAdd, Fin.val_succ] at hh <;> omega
      rw [prime70Reset, clearRegisters_effect, ite_eq_right hn]
      rw [binaryPrimeValues, framedModInput, Fin.append_right]
      simp only [Fin.cons_succ, prime70Extra]
      congr 1
      apply Fin.ext
      simp
      omega

/-- A total trial-division call with arbitrary initial private registers. -/
def binaryPrime70 : BinaryRoutine 70 := seq prime70Reset (binaryPrime 63)

theorem binaryPrime70_sound : binaryPrime70.Sound :=
  (clearRegisters_sound _).seq (binaryPrime_sound _)

theorem binaryPrime70_requires (v : BinaryValues 70) : binaryPrime70.requires v := by
  refine ⟨clearRegisters_requires _ _, ?_⟩
  rw [prime70Reset_effect]
  exact binaryPrime_requires _ _

theorem binaryPrime70_effect (v : BinaryValues 70) :
    binaryPrime70.effect v =
      if 2 ≤ v 0 then binaryPrimeValues (v 0) (v 0) (trialPrimeFlag (v 0) (v 0)) (prime70Extra v)
      else binaryPrimeValues (v 0) 0 0 (prime70Extra v) := by
  change (binaryPrime 63).effect (prime70Reset.effect v) = _
  rw [prime70Reset_effect, binaryPrime_effect]

theorem binaryPrime70_flag (v : BinaryValues 70) :
    binaryPrime70.effect v 6 = if (v 0).Prime then 1 else 0 := by
  rw [binaryPrime70_effect]
  by_cases hn : 2 ≤ v 0
  · rw [ite_eq_left hn]
    change trialPrimeFlag (v 0) (v 0) = _
    have hf := trialPrimeFlag_eq_one_iff (v 0) hn
    have hb := trialPrimeFlag_le_one (v 0) (v 0)
    by_cases hp : (v 0).Prime
    · simp only [hp, ite_true]
      exact hf.mpr hp
    · simp only [hp, ite_false]
      have : trialPrimeFlag (v 0) (v 0) ≠ 1 := fun h ↦ hp (hf.mp h)
      omega
  · have hp : ¬(v 0).Prime := fun h ↦ hn h.two_le
    simp only [hn, hp, ite_false]
    rfl

theorem binaryPrime70_preserves (v : BinaryValues 70) (i : Fin 63) :
    binaryPrime70.effect v (i.natAdd 7) = v (i.natAdd 7) := by
  rw [binaryPrime70_effect]
  have hi : i.natAdd 7 = i.succ.natAdd 6 := by ext; simp; omega
  rw [hi]
  split_ifs <;> rw [binaryPrimeValues, framedModInput, Fin.append_right] <;>
    simp [prime70Extra, ← hi]

theorem binaryPrime70_space {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (hv : ∀ j i, v j i ≤ W j) :
    SpaceBoundByWidthAt binaryPrime70 S v (fun j ↦ W j + 3) := by
  apply SpaceBoundByWidthAt.seq
  · exact (clearRegisters_space _ hv).mono (by intro j; omega)
  · have heq : (fun j ↦ prime70Reset.effect (v j)) =
        (fun j ↦ binaryPrimeValues (v j 0) 0 0 (prime70Extra (v j))) := by
      funext j; exact prime70Reset_effect _
    rw [heq]
    exact (binaryPrime_space (fun j ↦ v j 0) (fun j ↦ prime70Extra (v j)) S).mono
      (fun j ↦ Nat.add_le_add_right (hv j 0) 3)

def clearCoreWorkspace : BinaryRoutine 70 :=
  clearRegisters (List.ofFn fun i : Fin 64 ↦ i.castAdd 6)

theorem clearCoreWorkspace_effect (v : BinaryValues 70) :
    clearCoreWorkspace.effect v =
      coreValues (v (coreReg 0)) (v (coreReg 1)) (v (coreReg 2))
        (v (coreReg 3)) (v (coreReg 4)) (v (coreReg 5)) := by
  funext i
  refine Fin.addCases (m := 64) (n := 6) (fun i ↦ ?_) (fun i ↦ ?_) i
  · rw [clearCoreWorkspace, clearRegisters_effect]
    have hm : i.castAdd 6 ∈ (List.ofFn fun z : Fin 64 ↦ z.castAdd 6) :=
      List.mem_ofFn.mpr ⟨i, rfl⟩
    rw [ite_eq_left hm]
    rw [coreValues, Fin.append_left]
  · have hi : i.natAdd 64 ∉ (List.ofFn fun z : Fin 64 ↦ z.castAdd 6) := by
      simp only [List.mem_ofFn]
      rintro ⟨j, hj⟩
      have := congrArg (fun z : Fin 70 ↦ z.val) hj
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      omega
    rw [clearCoreWorkspace, clearRegisters_effect, ite_eq_right hi]
    change v (coreReg i) = coreValues _ _ _ _ _ _ (coreReg i)
    rw [coreValues_reg]
    fin_cases i <;> rfl

/-- Each cell begins by copying the prime candidate into the reusable primality bank. -/
def cellPrimeStart : BinaryRoutine 70 :=
  seq (clear 5) (seq (binaryCopy (coreReg 2) 0 5) binaryPrime70)

theorem cellPrimeStart_sound : cellPrimeStart.Sound :=
  (clear_sound _).seq ((binaryCopy_sound _ _ _).seq binaryPrime70_sound)

theorem cellPrimeStart_requires (v : BinaryValues 70) : cellPrimeStart.requires v := by
  refine ⟨trivial, ?_⟩
  refine ⟨?_, binaryPrime70_requires _⟩
  simp [binaryCopy, clear, coreReg]

theorem cellPrimeStart_flag (v : BinaryValues 70) :
    cellPrimeStart.effect v 6 = if (v (coreReg 2)).Prime then 1 else 0 := by
  change binaryPrime70.effect ((binaryCopy (coreReg 2) 0 5).effect ((clear 5).effect v)) 6 = _
  rw [binaryPrime70_flag]
  simp [binaryCopy, clear, coreReg]
  split_ifs <;> simp_all

theorem cellPrimeStart_preserves (v : BinaryValues 70) (i : Fin 6) :
    cellPrimeStart.effect v (coreReg i) = v (coreReg i) := by
  have hi : coreReg i = (i.natAdd 57).natAdd 7 := by ext; simp [coreReg]; omega
  change binaryPrime70.effect ((binaryCopy (coreReg 2) 0 5).effect ((clear 5).effect v)) _ = _
  rw [hi, binaryPrime70_preserves, ← hi]
  have h0 : coreReg i ≠ (0 : Fin 70) := by
    intro h; have := congrArg (fun z : Fin 70 ↦ z.val) h; simp [coreReg] at this <;> omega
  have h5 : coreReg i ≠ (5 : Fin 70) := by
    intro h; have := congrArg (fun z : Fin 70 ↦ z.val) h; simp [coreReg] at this <;> omega
  simp [binaryCopy, clear, h0, h5]

def cellLtPrepare : BinaryRoutine 70 :=
  seq (clear 5) (seq (binaryCopy (coreReg 3) 0 5) (binaryCopy (coreReg 2) 1 5))

theorem cellLtPrepare_sound : cellLtPrepare.Sound :=
  (clear_sound _).seq ((binaryCopy_sound _ _ _).seq (binaryCopy_sound _ _ _))

theorem cellLtPrepare_requires (v : BinaryValues 70) : cellLtPrepare.requires v := by
  simp [cellLtPrepare, seq, clear, binaryCopy, coreReg]

theorem cellLtPrepare_at (v : BinaryValues 70) (i : Fin 70) :
    cellLtPrepare.effect v i =
      if i = 0 then v (coreReg 3) else if i = 1 then v (coreReg 2)
      else if i = 5 then 0 else v i := by
  by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;> by_cases h5 : i = 5 <;>
    simp [cellLtPrepare, seq, clear, binaryCopy, h0, h1, h5, coreReg]

def cellLtStart : BinaryRoutine 70 := seq cellLtPrepare binaryLt70

theorem cellLtStart_sound : cellLtStart.Sound := cellLtPrepare_sound.seq binaryLt70_sound

theorem cellLtStart_requires (v : BinaryValues 70) : cellLtStart.requires v :=
  ⟨cellLtPrepare_requires v, binaryLt70_requires_of_scratchZero _ (by simp [cellLtPrepare_at])⟩

theorem cellLtStart_flag (v : BinaryValues 70) :
    cellLtStart.effect v 2 = if v (coreReg 3) < v (coreReg 2) then 1 else 0 := by
  change binaryLt70.effect (cellLtPrepare.effect v) 2 = _
  rw [binaryLt70_effect_of_scratchZero _ (by simp [cellLtPrepare_at])]
  simp [compareValues, framedModInput, Fin.append, Fin.addCases, cellLtPrepare_at]

theorem cellLtStart_preserves (v : BinaryValues 70) (i : Fin 6) :
    cellLtStart.effect v (coreReg i) = v (coreReg i) := by
  have hi : coreReg i = (i.natAdd 58).natAdd 6 := by ext; simp [coreReg]; omega
  change binaryLt70.effect (cellLtPrepare.effect v) (coreReg i) = _
  rw [hi, binaryLt70_extra _ (by simp [cellLtPrepare_at]), ← hi, cellLtPrepare_at]
  have hb : 64 ≤ (coreReg i).val := by simp [coreReg]
  have h0 : coreReg i ≠ (0 : Fin 70) := by intro h; rw [h] at hb; norm_num at hb
  have h1 : coreReg i ≠ (1 : Fin 70) := by intro h; rw [h] at hb; norm_num at hb
  have h5 : coreReg i ≠ (5 : Fin 70) := by intro h; rw [h] at hb; norm_num at hb
  simp [h0, h1, h5]

theorem cellPrimeStart_space {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (hv : ∀ j i, v j i ≤ W j) :
    SpaceBoundByWidthAt cellPrimeStart S v (fun j ↦ W j + 3) := by
  apply SpaceBoundByWidthAt.seq
  · exact (SpaceBoundByWidthAt.clear 5 (fun j ↦ hv j 5)).mono (by intro j; omega)
  · apply SpaceBoundByWidthAt.seq
    · apply SpaceBoundByWidthAt.binaryCopy
      · intro j; simpa [clear, coreReg] using (hv j (coreReg 2)).trans (Nat.le_add_right _ 3)
      · intro j; simpa [clear] using (hv j 0).trans (Nat.le_add_right _ 3)
    · apply binaryPrime70_space
      intro j i
      by_cases h0 : i = 0 <;> by_cases h5 : i = 5
      · subst i; contradiction
      · subst i; simpa [clear, binaryCopy, coreReg] using hv j (coreReg 2)
      · subst i; simp [clear, binaryCopy]
      · simpa [clear, binaryCopy, h0, h5] using hv j i

theorem cellLtPrepare_values_le (v : BinaryValues 70) (W : ℕ) (hv : ∀ i, v i ≤ W) :
    ∀ i, cellLtPrepare.effect v i ≤ W := by
  intro i
  rw [cellLtPrepare_at]
  split_ifs <;> first | exact hv _ | exact Nat.zero_le _

theorem cellLtPrepare_space {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (hv : ∀ j i, v j i ≤ W j) : SpaceBoundByWidthAt cellLtPrepare S v W := by
  apply SpaceBoundByWidthAt.seq
  · exact SpaceBoundByWidthAt.clear 5 (fun j ↦ hv j 5)
  · apply SpaceBoundByWidthAt.seq
    · apply SpaceBoundByWidthAt.binaryCopy
      · intro j; simpa [clear, coreReg] using hv j (coreReg 3)
      · intro j; simpa [clear] using hv j 0
    · apply SpaceBoundByWidthAt.binaryCopy
      · intro j; simpa [binaryCopy, clear, coreReg] using hv j (coreReg 2)
      · intro j; simpa [binaryCopy, clear] using hv j 1

theorem cellLtStart_space {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (hv : ∀ j i, v j i ≤ W j) : SpaceBoundByWidthAt cellLtStart S v W := by
  apply SpaceBoundByWidthAt.seq
  · exact cellLtPrepare_space hv
  · exact binaryLt70_space_of_scratchZero (fun j ↦ by simp [cellLtPrepare_at])
      (fun j ↦ cellLtPrepare_values_le _ _ (hv j))

end SparseIrred.UpperBounds.Machine
