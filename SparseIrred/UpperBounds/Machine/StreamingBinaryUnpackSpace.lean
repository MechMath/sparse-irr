import SparseIrred.UpperBounds.Machine.StreamingBinaryUnpack

/-! # All-prefix linear-width space for the packed-integer decoder -/

namespace SparseIrred.UpperBounds.Machine
open Complexity BinaryRoutine SparseDiv SparseDiv.StringArith

theorem unpackReadBit_values_le (v : BinaryValues 70) (W : ℕ) (hv : ∀ i, v i ≤ W) :
    ∀ i, (inputReadBit 65).effect v i ≤ W := by
  intro i
  rw [inputReadBit_effect]
  refine Fin.addCases (m := 5) (n := 65) (fun i ↦ ?_) (fun i ↦ ?_) i
  · rw [Fin.append_left]
    fin_cases i
    · exact (Nat.div_le_self _ _).trans (hv _)
    · exact Nat.zero_le _
    · exact (Nat.mod_le _ _).trans (hv _)
    · exact Nat.zero_le _
    · exact Nat.zero_le _
  · rw [Fin.append_right]
    exact hv _

private def unpackFinish : BinaryRoutine 70 :=
  seq (branchZero (unpackReg 2) identity (add (unpackReg 6) (unpackReg 5) (unpackReg 4)))
    (seq (binaryCopy (unpackReg 6) (unpackReg 9) (unpackReg 4))
      (seq (add (unpackReg 9) (unpackReg 6) (unpackReg 4))
        (seq (clear (unpackReg 9)) (clear (unpackReg 2)))))

theorem unpackFinish_space {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (hv : ∀ j i, v j i ≤ W j) :
    SpaceBoundByWidthAt unpackFinish S v (fun j ↦ 2 * W j + 1) := by
  apply SpaceBoundByWidthAt.seq
  · apply SpaceBoundByWidthAt.branchZero
    · exact SpaceBoundByWidthAt.identity
    · apply SpaceBoundByWidthAt.add
      · intro j; have := hv j (unpackReg 6); omega
      · intro j; have := hv j (unpackReg 6); have := hv j (unpackReg 5); omega
  · apply SpaceBoundByWidthAt.seq
    · apply SpaceBoundByWidthAt.binaryCopy
      · intro j
        have := hv j (unpackReg 6)
        simp only [branchZero, add, identity, emitBits]
        split_ifs <;> simpa using (show v j (unpackReg 6) ≤ 2 * W j + 1 by omega)
      · intro j
        have := hv j (unpackReg 9)
        simp only [branchZero, add, identity, emitBits]
        split_ifs <;> simpa using (show v j (unpackReg 9) ≤ 2 * W j + 1 by omega)
    · apply SpaceBoundByWidthAt.seq
      · apply SpaceBoundByWidthAt.add
        · intro j
          have := hv j (unpackReg 6)
          simp only [branchZero, add, identity, emitBits, binaryCopy]
          split_ifs <;> simpa using (show v j (unpackReg 6) ≤ 2 * W j + 1 by omega)
        · intro j
          have := hv j (unpackReg 6)
          simp only [branchZero, add, identity, emitBits, binaryCopy]
          split_ifs <;> simpa [two_mul] using
            (show v j (unpackReg 6) + v j (unpackReg 6) ≤ 2 * W j + 1 by omega)
      · apply SpaceBoundByWidthAt.seq
        · apply SpaceBoundByWidthAt.clear
          intro j
          have := hv j (unpackReg 6)
          simp only [branchZero, add, identity, emitBits, binaryCopy]
          split_ifs <;> simpa using (show v j (unpackReg 6) ≤ 2 * W j + 1 by omega)
        · apply SpaceBoundByWidthAt.clear
          intro j
          have := hv j (unpackReg 2)
          simp only [branchZero, add, identity, emitBits, binaryCopy, clear]
          split_ifs <;> simpa using (show v j (unpackReg 2) ≤ 2 * W j + 1 by omega)

theorem unpackActive_space {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (hv : ∀ j i, v j i ≤ W j) :
    SpaceBoundByWidthAt unpackActive S v (fun j ↦ 2 * W j + 1) := by
  change SpaceBoundByWidthAt (seq (inputReadBit 65) unpackFinish) S v _
  apply SpaceBoundByWidthAt.seq
  · exact (inputReadBit_space 65 hv).mono (by intro j; omega)
  · exact unpackFinish_space (fun j ↦ unpackReadBit_values_le (v j) (W j) (hv j))

theorem unpackBody_space (s a w i N : ℕ → ℕ) (extra : ℕ → Fin 59 → ℕ)
    {S W : ℕ → ℕ} (hs : ∀ j, 0 < s j)
    (hv : ∀ j z, unpackValues (s j) (a j) (w j) (i j) (N j) (extra j) z ≤ W j) :
    SpaceBoundByWidthAt unpackBody S
      (fun j ↦ unpackValues (s j) (a j) (w j) (i j) (N j) (extra j))
      (fun j ↦ 2 * W j + 1) := by
  apply SpaceBoundByWidthAt.seq
  · apply SpaceBoundByWidthAt.binaryCopy
    · intro j; have := hv j (unpackReg 0); omega
    · intro j; have := hv j (unpackReg 10); omega
  · apply SpaceBoundByWidthAt.seq
    · apply SpaceBoundByWidthAt.binaryPred
      intro j
      have hb : s j ≤ W j := hv j (unpackReg 0)
      have hp := hs j
      simp only [binaryCopy, Function.update_self, unpackValues_reg, Matrix.cons_val_zero]
      omega
    · apply SpaceBoundByWidthAt.seq
      · apply SpaceBoundByWidthAt.branchZero
        · exact SpaceBoundByWidthAt.identity
        · apply unpackActive_space
          intro j z
          have hb : s j ≤ W j := hv j (unpackReg 0)
          by_cases hz : z = unpackReg 10
          · subst z
            simp [binaryCopy, binaryPred]
            omega
          · simpa [binaryCopy, binaryPred, hz] using hv j z
      · apply SpaceBoundByWidthAt.clear
        intro j
        have hb : s j ≤ W j := hv j (unpackReg 0)
        simp only [binaryCopy, binaryPred, Function.update_self, unpackValues_reg,
          Matrix.cons_val_zero, Function.update_idem, branchZero]
        split_ifs
        · simp [identity, emitBits]
          omega
        · rw [unpackActive_effect]
          simp
          omega

theorem packedInput_drop_le (x : List Bool) (i : ℕ) : packedInput (x.drop i) ≤ packedInput x := by
  induction i generalizing x with
  | zero => simp
  | succ i ih =>
      cases x with
      | nil => simp
      | cons b x =>
          simp only [List.drop_succ_cons, packedInput_cons]
          have := ih x
          split <;> omega

theorem two_pow_length_le_packedInput (x : List Bool) : 2 ^ x.length ≤ packedInput x := by
  simp [packedInput, decNat_append, decNat_cons, decNat_nil]

theorem unpackTraceValues_le (x : List Bool) (i W : ℕ) (extra : Fin 59 → ℕ)
    (hi : i ≤ packedInput x) (hW : packedInput x ≤ W) (he : ∀ z, extra z ≤ W) :
    ∀ z, unpackTraceValues x i extra z ≤ W := by
  have hs := (packedInput_drop_le x i).trans hW
  have hp := (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (Nat.min_le_right i x.length)).trans
    ((two_pow_length_le_packedInput x).trans hW)
  have ha : decNat (x.take i) ≤ W := by
    have h := Nat.le_of_lt (decNat_lt_two_pow_length (x.take i))
    rw [List.length_take] at h
    exact h.trans hp
  intro z
  unfold unpackTraceValues
  refine Fin.addCases (m := 11) (n := 59) (fun z ↦ ?_) (fun z ↦ ?_) z
  · change unpackValues _ _ _ _ _ _ (unpackReg z) ≤ W
    fin_cases z <;> simp [unpackValues_reg] <;> omega
  · simpa using he z

theorem unpackLoop_space (x : ℕ → List Bool) (extra : ℕ → Fin 59 → ℕ) (S W : ℕ → ℕ)
    (hW : ∀ j, packedInput (x j) ≤ W j) (he : ∀ j z, extra j z ≤ W j) :
    SpaceBoundByWidthAt unpackLoop S (fun j ↦ unpackTraceValues (x j) 0 (extra j))
      (fun j ↦ 2 * W j + 1) := by
  apply SpaceBoundByWidthAt.binaryFor_of_clamped_body
  · intro j
    simp [unpackTraceValues, unpackValues_reg]
    have := hW j
    omega
  · intro j count hc
    rw [unpackLoop_values]
    have hn : count ≤ packedInput (x j) := by
      simpa [binaryForCount, unpackTraceValues] using hc.le
    have := unpackTraceValues_le (x j) count (W j) (extra j) hn (hW j) (he j) (unpackReg 7)
    omega
  · have heq : binaryForClampedValues unpackBody (unpackReg 7) (unpackReg 8)
        (fun j ↦ unpackTraceValues (x j) 0 (extra j)) =
        (fun code ↦ unpackTraceValues (x (Nat.unpair code).1)
          (min (Nat.unpair code).2 (packedInput (x (Nat.unpair code).1) - 1))
          (extra (Nat.unpair code).1)) := by
      funext code
      unfold binaryForClampedValues
      rw [unpackLoop_values]
      congr 2
    rw [heq]
    apply unpackBody_space
    · intro j; exact packedInput_pos _
    · intro code z
      exact unpackTraceValues_le _ _ _ _ ((Nat.min_le_right _ _).trans (Nat.sub_le _ _))
        (hW _) (he _) z

theorem unpackInit_space {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (hW : ∀ j, 1 ≤ W j) (hv : ∀ j i, v j i ≤ W j) :
    SpaceBoundByWidthAt unpackInit S v W := by
  apply SpaceBoundByWidthAt.seq
  · exact clearRegisters_space _ hv
  · apply SpaceBoundByWidthAt.seq
    · apply SpaceBoundByWidthAt.set
      · intro j; simp [clearRegisters_effect]
      · exact hW
    · apply SpaceBoundByWidthAt.binaryCopy
      · intro j
        simpa [BinaryRoutine.set, seq, clear, addConst, clearRegisters_effect]
          using hv j (unpackReg 0)
      · intro j
        simp [BinaryRoutine.set, seq, clear, addConst, clearRegisters_effect]

/-- The complete reusable decoder has an all-prefix linear-width space bound. -/
theorem unpackInput_space (x : ℕ → List Bool) (v : ℕ → BinaryValues 70) (S W : ℕ → ℕ)
    (hsource : ∀ j, v j (unpackReg 0) = packedInput (x j))
    (hv : ∀ j i, v j i ≤ W j) :
    SpaceBoundByWidthAt unpackInput S v (fun j ↦ 2 * W j + 1) := by
  have hW : ∀ j, packedInput (x j) ≤ W j := by
    intro j
    rw [← hsource]
    exact hv j _
  apply SpaceBoundByWidthAt.seq
  · exact (unpackInit_space (fun j ↦ (packedInput_pos _).trans_le (hW j)) hv).mono
      (by intro j; omega)
  · have heq : (fun j ↦ unpackInit.effect (v j)) =
        (fun j ↦ unpackTraceValues (x j) 0 (fun i ↦ v j (i.natAdd 11))) := by
      funext j
      rw [unpackInit_effect, hsource]
      simp [unpackTraceValues]
    rw [heq]
    exact unpackLoop_space x (fun j i ↦ v j (i.natAdd 11)) S W hW
      (fun j i ↦ hv j _)

end SparseIrred.UpperBounds.Machine
