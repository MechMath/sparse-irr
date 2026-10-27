import SparseIrred.UpperBounds.Machine.StreamingBinaryCellComplete
import SparseIrred.UpperBounds.Machine.StreamingBinaryCellBounds
import SparseIrred.UpperBounds.Machine.StreamingBinaryEvalSpace
import SparseIrred.UpperBounds.Machine.StreamingBinaryEvalSilent

/-! # Linear-width all-prefix space of the fully implemented counting cell -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

namespace SparseIrred.UpperBounds.Machine

open Complexity BinaryRoutine

private theorem seqEffect {n : ℕ} (R T : BinaryRoutine n) (v : BinaryValues n) :
    (seq R T).effect v = T.effect (R.effect v) := rfl

private theorem clearBound {n : ℕ} (idx : Fin n) (v : BinaryValues n) (B : ℕ)
    (hv : ∀ i, v i ≤ B) : ∀ i, (clear idx).effect v i ≤ B :=
  values_update_le idx hv (Nat.zero_le _)

private theorem copyBound {n : ℕ} (src dst scratch : Fin n) (v : BinaryValues n) (B : ℕ)
    (hv : ∀ i, v i ≤ B) : ∀ i, (binaryCopy src dst scratch).effect v i ≤ B :=
  values_update_le dst hv (hv src)

private theorem succBound {n : ℕ} (idx : Fin n) (v : BinaryValues n) (B : ℕ)
    (hv : ∀ i, v i ≤ B) : ∀ i, (binarySucc idx).effect v i ≤ B + 1 :=
  values_update_le idx (fun i ↦ (hv i).trans (Nat.le_add_right _ 1)) (Nat.add_le_add_right (hv idx) 1)

private theorem branchBound {n : ℕ} (idx : Fin n) (R T : BinaryRoutine n) (v : BinaryValues n) (B : ℕ)
    (hR : ∀ i, R.effect v i ≤ B) (hT : ∀ i, T.effect v i ≤ B) :
    ∀ i, (branchZero idx R T).effect v i ≤ B := by
  intro i
  change (if v idx = 0 then R.effect v else T.effect v) i ≤ B
  split_ifs
  · exact hR i
  · exact hT i

theorem validCoreInput_positive (input : ℕ) (hvalid : ValidCoreInput input) : 0 < input := by
  obtain ⟨l, rfl⟩ := hvalid
  exact packedInput_pos _

theorem cellEvalCopies_values_le (v : BinaryValues 70) (B : ℕ) (hv : ∀ i, v i ≤ B) :
    ∀ i, cellEvalCopies.effect v i ≤ B := by
  intro i
  rw [cellEvalCopies_at]
  split_ifs <;> first | exact hv _ | exact Nat.zero_le _

theorem cellEvalPrepare_values_le (v : BinaryValues 70) (B : ℕ)
    (hv : ∀ i, v i ≤ B) (hB : 1 ≤ B) : ∀ i, cellEvalPrepare.effect v i ≤ B := by
  have hp : cellModulus (v (coreReg 2)) ≤ B := by
    unfold cellModulus
    split_ifs <;> first | exact hB | exact hv _
  intro i
  rw [cellEvalPrepare_at]
  split_ifs <;> first | exact hp | exact hv _ | exact Nat.zero_le _

theorem cellEvalCopies_space {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (hv : ∀ j i, v j i ≤ W j) : SpaceBoundByWidthAt cellEvalCopies S v W := by
  apply SpaceBoundByWidthAt.seq (SpaceBoundByWidthAt.clear _ (fun j ↦ hv j 5))
  have h1 (j) := clearBound 5 (v j) (W j) (hv j)
  apply SpaceBoundByWidthAt.seq (SpaceBoundByWidthAt.binaryCopy _ _ _
    (fun j ↦ h1 j (coreReg 0)) (fun j ↦ h1 j 16))
  have h2 (j) := copyBound (coreReg 0) 16 5 _ (W j) (h1 j)
  apply SpaceBoundByWidthAt.seq (SpaceBoundByWidthAt.binaryCopy _ _ _
    (fun j ↦ h2 j (coreReg 2)) (fun j ↦ h2 j 17))
  have h3 (j) := copyBound (coreReg 2) 17 5 _ (W j) (h2 j)
  exact SpaceBoundByWidthAt.binaryCopy _ _ _ (fun j ↦ h3 j (coreReg 3)) (fun j ↦ h3 j 18)

theorem cellEvalPrepare_space {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (hv : ∀ j i, v j i ≤ W j) (hW : ∀ j, 1 ≤ W j) :
    SpaceBoundByWidthAt cellEvalPrepare S v W := by
  apply SpaceBoundByWidthAt.seq (cellEvalCopies_space hv)
  apply SpaceBoundByWidthAt.branchZero
  · exact SpaceBoundByWidthAt.set _ _
      (fun j ↦ cellEvalCopies_values_le _ _ (hv j) 17) hW
  · exact SpaceBoundByWidthAt.identity

theorem cellEvalStart_values_le (deriv : Bool) (v : BinaryValues 70) (B : ℕ)
    (hvalid : ValidCoreInput (v (coreReg 0))) (hv : ∀ i, v i ≤ B) :
    ∀ i, (cellEvalStart deriv).effect v i ≤ B := by
  have hB : 1 ≤ B := (validCoreInput_positive _ hvalid).trans_le (hv _)
  obtain ⟨l, hl⟩ := hvalid
  exact binarySparseEval_values_le deriv _ l (by simpa [cellEvalPrepare_at] using hl)
    (by simpa [cellEvalPrepare_at] using cellModulus_pos (v (coreReg 2))) B
    (cellEvalPrepare_values_le v B hv hB)

theorem cellEvalStart_space (deriv : Bool) {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (hvalid : ∀ j, ValidCoreInput (v j (coreReg 0))) (hv : ∀ j i, v j i ≤ W j) :
    SpaceBoundByWidthAt (cellEvalStart deriv) S v W := by
  classical
  have hW : ∀ j, 1 ≤ W j := fun j ↦ (validCoreInput_positive _ (hvalid j)).trans_le (hv j _)
  have hex : ∀ j, ∃ l, v j (coreReg 0) = packedInput (SparseDiv.Appendix.encITerms l) := hvalid
  choose l hl using hex
  apply SpaceBoundByWidthAt.seq (cellEvalPrepare_space hv hW)
  exact binarySparseEval_space deriv l (fun j ↦ by simpa [cellEvalPrepare_at] using hl j)
    (fun j ↦ by simpa [cellEvalPrepare_at] using cellModulus_pos (v j (coreReg 2)))
    (fun j ↦ cellEvalPrepare_values_le _ _ (hv j) (hW j))

theorem cellPrimeCount_values_le (v : BinaryValues 70) (B : ℕ) (hv : ∀ i, v i ≤ B) :
    ∀ i, cellPrimeCount.effect v i ≤ B + 1 :=
  branchBound _ _ _ v _ (succBound _ _ B hv) (fun i ↦ (hv i).trans (Nat.le_add_right _ 1))

theorem cellDerivativeCount_values_le (v : BinaryValues 70) (B : ℕ)
    (hvalid : ValidCoreInput (v (coreReg 0))) (hv : ∀ i, v i ≤ B) :
    ∀ i, cellDerivativeCount.effect v i ≤ B + 1 := by
  have he := cellEvalStart_values_le true v B hvalid hv
  exact branchBound _ _ _ _ _ (fun i ↦ (he i).trans (Nat.le_add_right _ 1)) (succBound _ _ B he)

theorem cellRootCount_values_le (v : BinaryValues 70) (B : ℕ)
    (hvalid : ValidCoreInput (v (coreReg 0))) (hv : ∀ i, v i ≤ B) :
    ∀ i, cellRootCount.effect v i ≤ B + 2 := by
  have he := cellEvalStart_values_le false v B hvalid hv
  change ∀ i, (branchZero 31 identity (seq (binarySucc (coreReg 5)) cellDerivativeCount)).effect
    ((cellEvalStart false).effect v) i ≤ B + 2
  apply branchBound 31 identity (seq (binarySucc (coreReg 5)) cellDerivativeCount)
    ((cellEvalStart false).effect v) (B + 2) (fun i ↦ (he i).trans (Nat.le_add_right _ 2))
  have hval := ((cellEvalStart_delta false v hvalid).trans (coreSuccRoot_delta _)).valid hvalid
  have h := cellDerivativeCount_values_le _ (B + 1) hval (succBound _ _ B he)
  simpa only [seqEffect, Nat.add_assoc] using h

theorem cellPrimeCase_values_le (v : BinaryValues 70) (B : ℕ)
    (hvalid : ValidCoreInput (v (coreReg 0))) (hv : ∀ i, v i ≤ B) :
    ∀ i, cellPrimeCase.effect v i ≤ B + 4 := by
  have hp := cellPrimeCount_values_le v B hv
  have hlt : ∀ i, cellLtStart.effect (cellPrimeCount.effect v) i ≤ B + 2 := by
    simpa only [Nat.add_assoc] using cellLtStart_values_le _ (B + 1) hp
  change ∀ i, (branchZero 2 identity cellRootCount).effect
    (cellLtStart.effect (cellPrimeCount.effect v)) i ≤ B + 4
  apply branchBound 2 identity cellRootCount (cellLtStart.effect (cellPrimeCount.effect v))
    (B + 4) (fun i ↦ (hlt i).trans (by omega))
  have hval := ((cellPrimeCount_delta v).trans (coreLtStart_delta _)).valid hvalid
  simpa only [Nat.add_assoc] using cellRootCount_values_le _ (B + 2) hval hlt

theorem cellPrimeCount_space {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (hv : ∀ j i, v j i ≤ W j) : SpaceBoundByWidthAt cellPrimeCount S v W := by
  apply SpaceBoundByWidthAt.branchZero
  · exact SpaceBoundByWidthAt.binarySucc _ (fun j ↦ hv j _)
  · exact SpaceBoundByWidthAt.identity

theorem cellDerivativeCount_space {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (hvalid : ∀ j, ValidCoreInput (v j (coreReg 0))) (hv : ∀ j i, v j i ≤ W j) :
    SpaceBoundByWidthAt cellDerivativeCount S v W := by
  apply SpaceBoundByWidthAt.seq (cellEvalStart_space true hvalid hv)
  apply SpaceBoundByWidthAt.branchZero 31 SpaceBoundByWidthAt.identity
  exact SpaceBoundByWidthAt.binarySucc _ (fun j ↦ cellEvalStart_values_le true _ _ (hvalid j) (hv j) _)

theorem cellRootCount_space {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (hvalid : ∀ j, ValidCoreInput (v j (coreReg 0))) (hv : ∀ j i, v j i ≤ W j) :
    SpaceBoundByWidthAt cellRootCount S v W := by
  have he (j) := cellEvalStart_values_le false (v j) (W j) (hvalid j) (hv j)
  apply SpaceBoundByWidthAt.seq (cellEvalStart_space false hvalid hv)
  apply SpaceBoundByWidthAt.branchZero 31 SpaceBoundByWidthAt.identity
  apply SpaceBoundByWidthAt.seq (SpaceBoundByWidthAt.binarySucc _ (fun j ↦ he j _))
  apply spaceWidth_add_const 1
  exact cellDerivativeCount_space
    (fun j ↦ ((cellEvalStart_delta false _ (hvalid j)).trans (coreSuccRoot_delta _)).valid (hvalid j))
    (fun j ↦ succBound _ _ _ (he j))

theorem cellPrimeCase_space {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (hvalid : ∀ j, ValidCoreInput (v j (coreReg 0))) (hv : ∀ j i, v j i ≤ W j) :
    SpaceBoundByWidthAt cellPrimeCase S v W := by
  have hp (j) := cellPrimeCount_values_le (v j) (W j) (hv j)
  have hlt (j) : ∀ i, cellLtStart.effect (cellPrimeCount.effect (v j)) i ≤ W j + 2 := by
    simpa only [Nat.add_assoc] using cellLtStart_values_le _ (W j + 1) (hp j)
  apply SpaceBoundByWidthAt.seq (cellPrimeCount_space hv)
  apply SpaceBoundByWidthAt.seq
  · exact spaceWidth_add_const 1 (cellLtStart_space hp)
  · apply SpaceBoundByWidthAt.branchZero 2 SpaceBoundByWidthAt.identity
    exact spaceWidth_add_const 2 (cellRootCount_space
      (fun j ↦ ((cellPrimeCount_delta (v j)).trans (coreLtStart_delta _)).valid (hvalid j)) hlt)

/-- Every internal machine prefix of the real counting cell fits a fixed
multiple of the original binary register width. -/
theorem completeCell_space {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (hvalid : ∀ j, ValidCoreInput (v j (coreReg 0))) (hv : ∀ j i, v j i ≤ W j) :
    SpaceBoundByWidthAt completeCell S v W := by
  have hp (j) := cellPrimeStart_values_le (v j) (W j) (hv j)
  have hval (j) := (corePrimeStart_delta (v j)).valid (hvalid j)
  apply SpaceBoundByWidthAt.seq
  · apply SpaceBoundByWidthAt.seq (spaceWidth_add_const 3 (cellPrimeStart_space hv))
    apply SpaceBoundByWidthAt.branchZero 6 SpaceBoundByWidthAt.identity
    exact spaceWidth_add_const 3 (cellPrimeCase_space hval hp)
  · apply spaceWidth_add_const 7
    apply clearCoreWorkspace_space
    intro j
    change ∀ i, (branchZero 6 identity cellPrimeCase).effect (cellPrimeStart.effect (v j)) i ≤ W j + 7
    apply branchBound 6 identity cellPrimeCase (cellPrimeStart.effect (v j)) (W j + 7)
      (fun i ↦ (hp j i).trans (by omega))
    simpa only [Nat.add_assoc] using cellPrimeCase_values_le _ (W j + 3) (hval j) (hp j)

theorem cellEvalCopies_silent : RoutineSilent cellEvalCopies :=
  (routineSilent_clear _).seq ((routineSilent_copy _ _ _).seq
    ((routineSilent_copy _ _ _).seq (routineSilent_copy _ _ _)))

theorem cellEvalPrepare_silent : RoutineSilent cellEvalPrepare :=
  cellEvalCopies_silent.seq ((routineSilent_set _ _).branchZero routineSilent_identity _)

theorem cellEvalStart_silent (deriv : Bool) : RoutineSilent (cellEvalStart deriv) :=
  cellEvalPrepare_silent.seq (binarySparseEval_silent deriv)

theorem cellPrimeCount_silent : RoutineSilent cellPrimeCount :=
  (routineSilent_succ _).branchZero routineSilent_identity _

theorem cellDerivativeCount_silent : RoutineSilent cellDerivativeCount :=
  (cellEvalStart_silent true).seq (routineSilent_identity.branchZero (routineSilent_succ _) _)

theorem cellRootCount_silent : RoutineSilent cellRootCount :=
  (cellEvalStart_silent false).seq (routineSilent_identity.branchZero
    ((routineSilent_succ _).seq cellDerivativeCount_silent) _)

theorem cellPrimeCase_silent : RoutineSilent cellPrimeCase :=
  cellPrimeCount_silent.seq (cellLtStart_silent.seq
    (routineSilent_identity.branchZero cellRootCount_silent _))

theorem completeCell_silent : RoutineSilent completeCell :=
  (cellPrimeStart_silent.seq (routineSilent_identity.branchZero cellPrimeCase_silent _)).seq
    clearCoreWorkspace_silent

end SparseIrred.UpperBounds.Machine
