import SparseIrred.UpperBounds.Machine.StreamingBinaryMod

/-! # Modular reduction with preserved extra registers -/

namespace SparseIrred.UpperBounds.Machine

open Complexity BinaryRoutine

def modReg (k : ℕ) (i : Fin 6) : Fin (6 + k) := i.castAdd k

@[simp] theorem modReg_inj (k : ℕ) (i j : Fin 6) :
    modReg k i = modReg k j ↔ i = j := by
  simp [modReg]

@[simp] theorem modReg_ne_extra (k : ℕ) (i : Fin 6) (j : Fin k) :
    modReg k i ≠ j.natAdd 6 := by
  intro h
  have := congrArg Fin.val h
  simp [modReg] at this
  omega

@[simp] theorem extra_ne_modReg (k : ℕ) (i : Fin 6) (j : Fin k) :
    j.natAdd 6 ≠ modReg k i := (modReg_ne_extra k i j).symm

def framedModReset (k : ℕ) : BinaryRoutine (6 + k) :=
  seq (seq (binaryCopy (modReg k 1) (modReg k 3) (modReg k 5))
    (binaryPred (modReg k 3))) (clear (modReg k 2))

def framedModBody (k : ℕ) : BinaryRoutine (6 + k) :=
  branchZero (modReg k 3) (framedModReset k)
    (seq (binaryPred (modReg k 3)) (binarySucc (modReg k 2)))

def framedModLoop (k : ℕ) : BinaryRoutine (6 + k) :=
  binaryFor (framedModBody k) (modReg k 4) (modReg k 0)

theorem framedModReset_sound (k : ℕ) : (framedModReset k).Sound :=
  ((binaryCopy_sound _ _ _).seq (binaryPred_sound _)).seq (clear_sound _)

theorem framedModBody_sound (k : ℕ) : (framedModBody k).Sound :=
  (framedModReset_sound k).branchZero
    ((binaryPred_sound _).seq (binarySucc_sound _)) _

theorem framedModLoop_sound (k : ℕ) : (framedModLoop k).Sound :=
  (framedModBody_sound k).binaryFor _ _

def framedModValues {k : ℕ} (n m i : ℕ) (extra : Fin k → ℕ) : BinaryValues (6 + k) :=
  Fin.append (binaryModValues n m i) extra

@[simp] theorem framedModValues_reg {k : ℕ} (n m i : ℕ) (extra : Fin k → ℕ) (j : Fin 6) :
    framedModValues n m i extra (modReg k j) = binaryModValues n m i j :=
  Fin.append_left _ _ _

@[simp] theorem framedModValues_extra {k : ℕ} (n m i : ℕ) (extra : Fin k → ℕ)
    (j : Fin k) : framedModValues n m i extra (j.natAdd 6) = extra j :=
  Fin.append_right _ _ _

theorem framedModBody_requires {k : ℕ} (n m i : ℕ) (extra : Fin k → ℕ) (hm : 0 < m) :
    (framedModBody k).requires (framedModValues n m i extra) := by
  by_cases h : m - 1 - i % m = 0
  · simp [framedModBody, branchZero, h, binaryModValues, framedModReset, seq,
      binaryCopy, binaryPred, clear, hm]
  · simp [framedModBody, branchZero, h, binaryModValues, seq, binaryPred, binarySucc]
    omega

private theorem mod_succ (m i : ℕ) (hm : 0 < m) :
    (i + 1) % m = if m - 1 - i % m = 0 then 0 else i % m + 1 := by
  have hr := Nat.mod_lt i hm
  have hmod : (i + 1) % m = (i % m + 1) % m := by simp [Nat.add_mod]
  rw [hmod]
  split_ifs with h
  · have heq : i % m + 1 = m := by omega
    simp [heq]
  · exact Nat.mod_eq_of_lt (by omega)

theorem framedModBody_step {k : ℕ} (n m i : ℕ) (extra : Fin k → ℕ) (hm : 0 < m) :
    binaryForStep (framedModBody k) (modReg k 4) (framedModValues n m i extra) =
      framedModValues n m (i + 1) extra := by
  have hmod := mod_succ m i hm
  have hr := Nat.mod_lt i hm
  by_cases h : m - 1 - i % m = 0
  · simp only [h, ite_true] at hmod
    funext j
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
    · change binaryForStep (framedModBody k) (modReg k 4)
        (framedModValues n m i extra) (modReg k j) =
          framedModValues n m (i + 1) extra (modReg k j)
      fin_cases j <;>
        simp [binaryForStep, framedModBody, branchZero, binaryModValues, h,
          framedModReset, seq, binaryCopy, binaryPred, clear, hmod]
    · simp [binaryForStep, framedModBody, branchZero, binaryModValues, h,
        framedModReset, seq, binaryCopy, binaryPred, clear]
  · simp only [h, ite_false] at hmod
    funext j
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
    · change binaryForStep (framedModBody k) (modReg k 4)
        (framedModValues n m i extra) (modReg k j) =
          framedModValues n m (i + 1) extra (modReg k j)
      fin_cases j <;>
        simp [binaryForStep, framedModBody, branchZero, binaryModValues, h,
          seq, binaryPred, binarySucc, hmod]
      omega
    · simp [binaryForStep, framedModBody, branchZero, binaryModValues, h,
        seq, binaryPred, binarySucc]

theorem framedModBody_preserves {k : ℕ} (n m i : ℕ) (extra : Fin k → ℕ) :
    (framedModBody k).effect (framedModValues n m i extra) (modReg k 4) = i ∧
      (framedModBody k).effect (framedModValues n m i extra) (modReg k 0) = n := by
  by_cases h : m - 1 - i % m = 0 <;>
    simp [framedModBody, branchZero, binaryModValues, h, framedModReset, seq,
      binaryCopy, binaryPred, clear, binarySucc]

theorem framedModLoop_values {k : ℕ} (n m i : ℕ) (extra : Fin k → ℕ) (hm : 0 < m) :
    binaryForValues (framedModBody k) (modReg k 4) (framedModValues n m 0 extra) i =
      framedModValues n m i extra := by
  induction i with
  | zero => rfl
  | succ i ih => rw [binaryForValues, ih, framedModBody_step n m i extra hm]

theorem framedModLoop_requires {k : ℕ} (n m : ℕ) (extra : Fin k → ℕ) (hm : 0 < m) :
    (framedModLoop k).requires (framedModValues n m 0 extra) := by
  refine ⟨by simp, by simp [binaryModValues], ?_⟩
  intro i hi
  rw [framedModLoop_values n m i extra hm]
  exact ⟨framedModBody_requires n m i extra hm, (framedModBody_preserves n m i extra).1,
    (framedModBody_preserves n m i extra).2⟩

theorem framedModLoop_effect {k : ℕ} (n m : ℕ) (extra : Fin k → ℕ) (hm : 0 < m) :
    (framedModLoop k).effect (framedModValues n m 0 extra) =
      framedModValues n m n extra := by
  change binaryForValues (framedModBody k) (modReg k 4) (framedModValues n m 0 extra)
    (binaryForCount (modReg k 4) (modReg k 0) (framedModValues n m 0 extra)) = _
  have hcount : binaryForCount (modReg k 4) (modReg k 0) (framedModValues n m 0 extra) = n := by
    simp [binaryForCount, binaryModValues]
  rw [hcount, framedModLoop_values n m n extra hm]

theorem framedModBody_space {k : ℕ} {S W : ℕ → ℕ} {v : ℕ → BinaryValues (6 + k)}
    (hW : ∀ j, 1 ≤ W j) (hv : ∀ j i, v j (modReg k i) ≤ W j) :
    SpaceBoundByWidthAt (framedModBody k) S v W := by
  apply SpaceBoundByWidthAt.branchZero
  · apply SpaceBoundByWidthAt.seq
    · apply SpaceBoundByWidthAt.seq
      · exact SpaceBoundByWidthAt.binaryCopy _ _ _ (fun j ↦ hv j 1) (fun j ↦ hv j 3)
      · apply SpaceBoundByWidthAt.binaryPred
        intro j
        simp only [binaryCopy, Function.update_self]
        have := hv j 1
        have := hW j
        omega
    · apply SpaceBoundByWidthAt.clear
      intro j
      simpa [seq, binaryCopy, binaryPred] using hv j 2
  · apply SpaceBoundByWidthAt.seq
    · apply SpaceBoundByWidthAt.binaryPred
      intro j
      have := hv j 3
      have := hW j
      omega
    · apply SpaceBoundByWidthAt.binarySucc
      intro j
      simpa [binaryPred] using hv j 2

theorem framedModLoop_space {k : ℕ} (n m : ℕ → ℕ) (extra : ℕ → Fin k → ℕ)
    (hm : ∀ j, 0 < m j) (S : ℕ → ℕ) :
    SpaceBoundByWidthAt (framedModLoop k) S
      (fun j ↦ framedModValues (n j) (m j) 0 (extra j))
      (fun j ↦ max (n j) (m j) + 1) := by
  apply SpaceBoundByWidthAt.binaryFor_of_clamped_body
  · intro j
    simp only [framedModValues_reg, binaryModValues, Matrix.cons_val_zero]
    omega
  · intro j count hc
    rw [framedModLoop_values _ _ _ _ (hm j), framedModValues_reg]
    apply binaryModValues_le _ _ _ (hm j) _ 4
    simpa [binaryForCount, binaryModValues] using Nat.le_of_lt hc
  · apply framedModBody_space (fun _ ↦ by omega)
    intro code idx
    unfold binaryForClampedValues
    rw [framedModLoop_values _ _ _ _ (hm _), framedModValues_reg]
    apply binaryModValues_le _ _ _ (hm _)
    simp [binaryForCount, binaryModValues]

/-- Clear reused loop registers and initialize the modulus countdown. -/
def framedModInit (k : ℕ) : BinaryRoutine (6 + k) :=
  seq (seq (clear (modReg k 2)) (clear (modReg k 4)))
    (seq (binaryCopy (modReg k 1) (modReg k 3) (modReg k 5))
      (binaryPred (modReg k 3)))

/-- A complete modular-reduction subroutine with preserved extra registers. -/
def framedMod (k : ℕ) : BinaryRoutine (6 + k) := seq (framedModInit k) (framedModLoop k)

theorem framedModInit_sound (k : ℕ) : (framedModInit k).Sound :=
  ((clear_sound _).seq (clear_sound _)).seq
    ((binaryCopy_sound _ _ _).seq (binaryPred_sound _))

theorem framedMod_sound (k : ℕ) : (framedMod k).Sound :=
  (framedModInit_sound k).seq (framedModLoop_sound k)

def framedModInput {k : ℕ} (n m r d c : ℕ) (extra : Fin k → ℕ) : BinaryValues (6 + k) :=
  Fin.append ![n, m, r, d, c, 0] extra

@[simp] theorem framedModInput_reg {k : ℕ} (n m r d c : ℕ) (extra : Fin k → ℕ)
    (j : Fin 6) : framedModInput n m r d c extra (modReg k j) = ![n, m, r, d, c, 0] j :=
  Fin.append_left _ _ _

@[simp] theorem framedModInput_extra {k : ℕ} (n m r d c : ℕ) (extra : Fin k → ℕ)
    (j : Fin k) : framedModInput n m r d c extra (j.natAdd 6) = extra j :=
  Fin.append_right _ _ _

theorem framedModInit_requires {k : ℕ} (n m r d c : ℕ) (extra : Fin k → ℕ) (hm : 0 < m) :
    (framedModInit k).requires (framedModInput n m r d c extra) := by
  simp [framedModInit, seq, clear, binaryCopy, binaryPred, hm]

theorem framedModInit_effect {k : ℕ} (n m r d c : ℕ) (extra : Fin k → ℕ) :
    (framedModInit k).effect (framedModInput n m r d c extra) =
      framedModValues n m 0 extra := by
  funext j
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
  · change (framedModInit k).effect (framedModInput n m r d c extra) (modReg k j) =
      framedModValues n m 0 extra (modReg k j)
    fin_cases j <;> simp [framedModInit, seq, clear, binaryCopy, binaryPred, binaryModValues]
  · simp [framedModInit, seq, clear, binaryCopy, binaryPred]

theorem framedMod_requires {k : ℕ} (n m r d c : ℕ) (extra : Fin k → ℕ) (hm : 0 < m) :
    (framedMod k).requires (framedModInput n m r d c extra) := by
  refine ⟨framedModInit_requires n m r d c extra hm, ?_⟩
  rw [framedModInit_effect]
  exact framedModLoop_requires n m extra hm

/-- The subroutine computes the exact remainder and preserves dividend,
modulus, and every extra register. -/
theorem framedMod_effect {k : ℕ} (n m r d c : ℕ) (extra : Fin k → ℕ) (hm : 0 < m) :
    (framedMod k).effect (framedModInput n m r d c extra) =
      framedModValues n m n extra := by
  change (framedModLoop k).effect ((framedModInit k).effect _) = _
  rw [framedModInit_effect, framedModLoop_effect n m extra hm]

theorem framedModInit_space {k : ℕ} {S W : ℕ → ℕ} {v : ℕ → BinaryValues (6 + k)}
    (hW : ∀ j, 1 ≤ W j) (hv : ∀ j i, v j (modReg k i) ≤ W j) :
    SpaceBoundByWidthAt (framedModInit k) S v W := by
  apply SpaceBoundByWidthAt.seq
  · apply SpaceBoundByWidthAt.seq
    · exact SpaceBoundByWidthAt.clear _ (fun j ↦ hv j 2)
    · apply SpaceBoundByWidthAt.clear
      intro j
      simpa [clear] using hv j 4
  · apply SpaceBoundByWidthAt.seq
    · apply SpaceBoundByWidthAt.binaryCopy
      · intro j; simpa [seq, clear] using hv j 1
      · intro j; simpa [seq, clear] using hv j 3
    · apply SpaceBoundByWidthAt.binaryPred
      intro j
      have hle : v j (modReg k 1) - 1 + 1 ≤ W j := by
        have := hv j 1
        have := hW j
        omega
      simpa [seq, clear, binaryCopy] using hle

/-- Uniform width control for the initialized modular-reduction machine.
Extra registers are preserved, and therefore need no numeric size assumption. -/
theorem framedMod_space {k : ℕ} (n m r d c : ℕ → ℕ) (extra : ℕ → Fin k → ℕ)
    (hm : ∀ j, 0 < m j) (S W : ℕ → ℕ)
    (hn : ∀ j, n j < W j) (hmW : ∀ j, m j < W j)
    (hr : ∀ j, r j ≤ W j) (hd : ∀ j, d j ≤ W j) (hc : ∀ j, c j ≤ W j) :
    SpaceBoundByWidthAt (framedMod k) S
      (fun j ↦ framedModInput (n j) (m j) (r j) (d j) (c j) (extra j)) W := by
  apply SpaceBoundByWidthAt.seq
  · apply framedModInit_space (fun j ↦ by have := hn j; omega)
    intro j i
    rw [framedModInput_reg]
    fin_cases i <;> simp <;>
      first | exact Nat.le_of_lt (hn j) | exact Nat.le_of_lt (hmW j) |
        exact hr j | exact hd j | exact hc j
  · have heq : (fun j ↦ (framedModInit k).effect
        (framedModInput (n j) (m j) (r j) (d j) (c j) (extra j))) =
        (fun j ↦ framedModValues (n j) (m j) 0 (extra j)) :=
      funext (fun j ↦ framedModInit_effect _ _ _ _ _ _)
    rw [heq]
    exact (framedModLoop_space n m extra hm S).mono (fun j ↦ by
      have := hn j
      have := hmW j
      omega)

end SparseIrred.UpperBounds.Machine
