import SparseIrred.UpperBounds.Machine.StreamingBinaryPrime

/-! # Total binary trial-division machine, including zero and one -/

namespace SparseIrred.UpperBounds.Machine

open Complexity BinaryRoutine

/-- Inspect `n-1` without changing the preserved input. -/
def binaryPrimeProbe (k : ℕ) : BinaryRoutine (6 + (k + 1)) :=
  seq (binaryCopy (modReg (k + 1) 0) (modReg (k + 1) 1) (modReg (k + 1) 5))
    (binaryPred (modReg (k + 1) 1))

/-- Initialize the divisor and the optimistic primality flag. -/
def binaryPrimePrepare (k : ℕ) : BinaryRoutine (6 + (k + 1)) :=
  seq (set (modReg (k + 1) 1) 2) (set (primeFlagReg k) 1)

/-- Actual deterministic primality machine. The input and all framed extra registers
are preserved. Zero and one return the initial zero flag directly. -/
def binaryPrime (k : ℕ) : BinaryRoutine (6 + (k + 1)) :=
  branchZero (modReg (k + 1) 0) identity
    (seq (binaryPrimeProbe k)
      (branchZero (modReg (k + 1) 1) identity
        (seq (binaryPrimePrepare k) (binaryPrimeLoop k))))

theorem binaryPrimeProbe_sound (k : ℕ) : (binaryPrimeProbe k).Sound :=
  (binaryCopy_sound _ _ _).seq (binaryPred_sound _)

theorem binaryPrimePrepare_sound (k : ℕ) : (binaryPrimePrepare k).Sound :=
  (set_sound _ _).seq (set_sound _ _)

theorem binaryPrime_sound (k : ℕ) : (binaryPrime k).Sound :=
  identity_sound.branchZero
    ((binaryPrimeProbe_sound k).seq (identity_sound.branchZero
      ((binaryPrimePrepare_sound k).seq (binaryPrimeLoop_sound k)) _)) _

theorem binaryPrimeProbe_effect {k : ℕ} (n d flag : ℕ) (extra : Fin k → ℕ) :
    (binaryPrimeProbe k).effect (binaryPrimeValues n d flag extra) =
      binaryPrimeValues n (n - 1) flag extra := by
  simp only [binaryPrimeProbe, seq, binaryCopy, binaryPred]
  have hv : binaryPrimeValues n d flag extra (modReg (k + 1) 0) = n := by
    simp [binaryPrimeValues]
  rw [hv, binaryPrimeValues_update_divisor n d flag n extra]
  simpa [binaryPrimeValues] using
    binaryPrimeValues_update_divisor n n flag (n - 1) extra

theorem binaryPrimePrepare_effect {k : ℕ} (n d flag : ℕ) (extra : Fin k → ℕ) :
    (binaryPrimePrepare k).effect (binaryPrimeValues n d flag extra) =
      binaryPrimeValues n 2 1 extra := by
  have hcast (i : Fin 6) : i.castAdd (k + 1) = modReg (k + 1) i := rfl
  funext j
  refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) j
  · simp only [hcast]
    fin_cases i <;> simp [binaryPrimePrepare, seq, BinaryRoutine.set, clear, addConst, seq, binaryPrimeValues, primeFlagReg]
  · refine Fin.cases ?_ (fun j ↦ ?_) i <;>
      simp [binaryPrimePrepare, seq, BinaryRoutine.set, clear, addConst, seq, binaryPrimeValues, primeFlagReg]

theorem binaryPrimeProbe_requires {k : ℕ} (n d flag : ℕ) (extra : Fin k → ℕ)
    (hn : 0 < n) : (binaryPrimeProbe k).requires (binaryPrimeValues n d flag extra) := by
  simp [binaryPrimeProbe, seq, binaryCopy, binaryPred, binaryPrimeValues, hn]

theorem binaryPrimePrepare_requires {k : ℕ} (v : BinaryValues (6 + (k + 1))) :
    (binaryPrimePrepare k).requires v := by
  simp [binaryPrimePrepare, seq, BinaryRoutine.set, clear, addConst]

/-- The total primality routine's precondition holds on every natural input. -/
theorem binaryPrime_requires {k : ℕ} (n : ℕ) (extra : Fin k → ℕ) :
    (binaryPrime k).requires (binaryPrimeValues n 0 0 extra) := by
  by_cases hn0 : n = 0
  · simp [binaryPrime, branchZero, binaryPrimeValues, hn0, identity, emitBits]
  · change (if n = 0 then True else
      (binaryPrimeProbe k).requires _ ∧
        (branchZero (modReg (k + 1) 1) identity
          (seq (binaryPrimePrepare k) (binaryPrimeLoop k))).requires
            ((binaryPrimeProbe k).effect (binaryPrimeValues n 0 0 extra)))
    rw [ite_eq_right hn0, binaryPrimeProbe_effect]
    refine ⟨binaryPrimeProbe_requires _ _ _ _ (by omega), ?_⟩
    by_cases hn1 : n = 1
    · simp [branchZero, binaryPrimeValues, hn1, identity, emitBits]
    · change (if n - 1 = 0 then True else
        (binaryPrimePrepare k).requires _ ∧ (binaryPrimeLoop k).requires
          ((binaryPrimePrepare k).effect (binaryPrimeValues n (n - 1) 0 extra)))
      rw [ite_eq_right (by omega), binaryPrimePrepare_effect]
      exact ⟨binaryPrimePrepare_requires _, binaryPrimeLoop_requires n extra (by omega)⟩

/-- Complete output-state description, including preservation of every framed register. -/
theorem binaryPrime_effect {k : ℕ} (n : ℕ) (extra : Fin k → ℕ) :
    (binaryPrime k).effect (binaryPrimeValues n 0 0 extra) =
      if 2 ≤ n then binaryPrimeValues n n (trialPrimeFlag n n) extra
      else binaryPrimeValues n 0 0 extra := by
  by_cases hn0 : n = 0
  · simp [binaryPrime, branchZero, binaryPrimeValues, hn0, identity, emitBits]
  · change (if n = 0 then _ else
      (branchZero (modReg (k + 1) 1) identity
        (seq (binaryPrimePrepare k) (binaryPrimeLoop k))).effect
          ((binaryPrimeProbe k).effect (binaryPrimeValues n 0 0 extra))) = _
    rw [ite_eq_right hn0, binaryPrimeProbe_effect]
    by_cases hn1 : n = 1
    · simp [branchZero, binaryPrimeValues, hn1, identity, emitBits]
    · have hn : 2 ≤ n := by omega
      change (if n - 1 = 0 then _ else
        (binaryPrimeLoop k).effect
          ((binaryPrimePrepare k).effect (binaryPrimeValues n (n - 1) 0 extra))) = _
      rw [ite_eq_right (by omega), binaryPrimePrepare_effect,
        binaryPrimeLoop_effect n extra hn, ite_eq_left hn]

/-- The actual trial-division machine decides primality of every natural input. -/
theorem binaryPrime_flag_iff {k : ℕ} (n : ℕ) (extra : Fin k → ℕ) :
    (binaryPrime k).effect (binaryPrimeValues n 0 0 extra) (primeFlagReg k) = 1 ↔
      n.Prime := by
  rw [binaryPrime_effect]
  by_cases hn : 2 ≤ n
  · rw [ite_eq_left hn]
    simpa [binaryPrimeValues, primeFlagReg] using trialPrimeFlag_eq_one_iff n hn
  · have hnp : ¬n.Prime := fun h ↦ hn h.two_le
    simp [hn, binaryPrimeValues, primeFlagReg, hnp]

/-- A slightly larger width envelope also covers the unselected loop on inputs zero and one. -/
theorem binaryPrimeLoop_space_total {k : ℕ} (n : ℕ → ℕ) (extra : ℕ → Fin k → ℕ)
    (S : ℕ → ℕ) :
    SpaceBoundByWidthAt (binaryPrimeLoop k) S
      (fun j ↦ binaryPrimeValues (n j) 2 1 (extra j)) (fun j ↦ n j + 3) := by
  apply SpaceBoundByWidthAt.binaryFor_of_clamped_body
  · intro j
    simp [binaryPrimeValues]
  · intro j count hc
    rw [binaryPrimeLoop_values]
    simp only [binaryPrimeValues, framedModInput_reg, Matrix.cons_val_one, Matrix.cons_val_zero]
    have hcount : count < n j - 2 := by simpa [binaryForCount, binaryPrimeValues] using hc
    omega
  · have heq : binaryForClampedValues (binaryPrimeBody k) (modReg (k + 1) 1)
        (modReg (k + 1) 0) (fun j ↦ binaryPrimeValues (n j) 2 1 (extra j)) =
        (fun code ↦ binaryPrimeValues (n (Nat.unpair code).1)
          (2 + min (Nat.unpair code).2 (n (Nat.unpair code).1 - 2 - 1))
          (trialPrimeFlag (n (Nat.unpair code).1)
            (2 + min (Nat.unpair code).2 (n (Nat.unpair code).1 - 2 - 1)))
          (extra (Nat.unpair code).1)) := by
      funext code
      dsimp only [binaryForClampedValues]
      rw [binaryPrimeLoop_values]
      simp only [binaryForCount, binaryPrimeValues, framedModInput_reg,
        Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [heq]
    apply binaryPrimeBody_space
    · intro code; omega
    · intro code; omega
    · intro code
      have hm := Nat.min_le_right (Nat.unpair code).2 (n (Nat.unpair code).1 - 2 - 1)
      omega
    · intro code
      exact (trialPrimeFlag_le_one _ _).trans (by omega)

/-- The full routine has an all-prefix linear binary-width certificate, including
both deterministic boundary branches. No primality algorithm is an external premise here. -/
theorem binaryPrime_space {k : ℕ} (n : ℕ → ℕ) (extra : ℕ → Fin k → ℕ)
    (S : ℕ → ℕ) :
    SpaceBoundByWidthAt (binaryPrime k) S
      (fun j ↦ binaryPrimeValues (n j) 0 0 (extra j)) (fun j ↦ n j + 3) := by
  apply SpaceBoundByWidthAt.branchZero
  · exact SpaceBoundByWidthAt.identity
  · apply SpaceBoundByWidthAt.seq
    · apply SpaceBoundByWidthAt.seq
      · apply SpaceBoundByWidthAt.binaryCopy
        · intro j; simp [binaryPrimeValues]
        · intro j; simp [binaryPrimeValues]
      · apply SpaceBoundByWidthAt.binaryPred
        intro j
        simp only [binaryCopy, Function.update_self, binaryPrimeValues, framedModInput_reg,
          Matrix.cons_val_zero]
        omega
    · have heq : (fun j ↦ (binaryPrimeProbe k).effect
          (binaryPrimeValues (n j) 0 0 (extra j))) =
          (fun j ↦ binaryPrimeValues (n j) (n j - 1) 0 (extra j)) :=
        funext fun j ↦ binaryPrimeProbe_effect _ _ _ _
      rw [heq]
      apply SpaceBoundByWidthAt.branchZero
      · exact SpaceBoundByWidthAt.identity
      · apply SpaceBoundByWidthAt.seq
        · apply SpaceBoundByWidthAt.seq
          · apply SpaceBoundByWidthAt.set
            · intro j; simp [binaryPrimeValues]; omega
            · intro j; omega
          · apply SpaceBoundByWidthAt.set
            · intro j
              simp [BinaryRoutine.set, clear, addConst, seq, binaryPrimeValues, primeFlagReg]
            · intro j; omega
        · have heq' : (fun j ↦ (binaryPrimePrepare k).effect
              (binaryPrimeValues (n j) (n j - 1) 0 (extra j))) =
              (fun j ↦ binaryPrimeValues (n j) 2 1 (extra j)) :=
            funext fun j ↦ binaryPrimePrepare_effect _ _ _ _
          rw [heq']
          exact binaryPrimeLoop_space_total n extra S

end SparseIrred.UpperBounds.Machine
