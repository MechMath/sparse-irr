import SparseIrred.UpperBounds.Machine.StreamingBinaryCellCompleteEval
import SparseIrred.UpperBounds.Machine.StreamingBinaryCellCompleteDelta

/-! # The actual prime/residue counting cell of Section 3.6 -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

namespace SparseIrred.UpperBounds.Machine

open Complexity BinaryRoutine

private theorem routine_seq_requires {n : ℕ} (R T : BinaryRoutine n) (v : BinaryValues n) :
    (seq R T).requires v ↔ R.requires v ∧ T.requires (R.effect v) := Iff.rfl

private theorem routine_seq_effect {n : ℕ} (R T : BinaryRoutine n) (v : BinaryValues n) :
    (seq R T).effect v = T.effect (R.effect v) := rfl

private theorem routine_branch_requires {n : ℕ} (i : Fin n) (R T : BinaryRoutine n)
    (v : BinaryValues n) :
    (branchZero i R T).requires v ↔ if v i = 0 then R.requires v else T.requires v := Iff.rfl

theorem CoreDelta.valid {v w : BinaryValues 70} {P A : ℕ} (h : CoreDelta v w P A)
    (hv : ValidCoreInput (v (coreReg 0))) : ValidCoreInput (w (coreReg 0)) := by
  rw [h.input]; exact hv

def cellTest (deriv : Bool) (v : BinaryValues 70) : ℕ :=
  cellZeroFlag deriv (v (coreReg 0)) (cellModulus (v (coreReg 2))) (v (coreReg 3))

theorem cellTest_le_one (deriv : Bool) (v : BinaryValues 70) : cellTest deriv v ≤ 1 :=
  cellZeroFlag_le_one _ _ _ _

theorem CoreDelta.test {v w : BinaryValues 70} {P A : ℕ} (h : CoreDelta v w P A)
    (deriv : Bool) : cellTest deriv w = cellTest deriv v := by
  unfold cellTest
  rw [h.input, h.prime, h.residue]

def cellRootWeight (v : BinaryValues 70) : ℕ :=
  if cellTest false v = 0 then 0 else 1 + cellTest true v

theorem CoreDelta.rootWeight {v w : BinaryValues 70} {P A : ℕ} (h : CoreDelta v w P A) :
    cellRootWeight w = cellRootWeight v := by
  unfold cellRootWeight
  rw [h.test false, h.test true]

theorem cellEvalStart_delta (deriv : Bool) (v : BinaryValues 70)
    (hv : ValidCoreInput (v (coreReg 0))) : CoreDelta v ((cellEvalStart deriv).effect v) 0 0 :=
  CoreDelta.of_preserves (cellEvalStart_preserves deriv v hv)

/-- A prime row contributes once to the prime counter, at residue zero. -/
def cellPrimeCount : BinaryRoutine 70 :=
  branchZero (coreReg 3) (binarySucc (coreReg 4)) identity

def cellDerivativeCount : BinaryRoutine 70 :=
  seq (cellEvalStart true) (branchZero 31 identity (binarySucc (coreReg 5)))

def cellRootCount : BinaryRoutine 70 :=
  seq (cellEvalStart false)
    (branchZero 31 identity (seq (binarySucc (coreReg 5)) cellDerivativeCount))

def cellPrimeCase : BinaryRoutine 70 :=
  seq cellPrimeCount (seq cellLtStart (branchZero 2 identity cellRootCount))

/-- The complete cell performs trial primality, residue-range checking,
ordinary/derivative evaluation, and exact counter updates, then clears its
private workspace for the next cell. -/
def completeCell : BinaryRoutine 70 :=
  seq (seq cellPrimeStart (branchZero 6 identity cellPrimeCase)) clearCoreWorkspace

theorem cellPrimeCount_sound : cellPrimeCount.Sound :=
  (binarySucc_sound _).branchZero identity_sound _

theorem cellDerivativeCount_sound : cellDerivativeCount.Sound :=
  (cellEvalStart_sound true).seq (identity_sound.branchZero (binarySucc_sound _) _)

theorem cellRootCount_sound : cellRootCount.Sound :=
  (cellEvalStart_sound false).seq
    (identity_sound.branchZero ((binarySucc_sound _).seq cellDerivativeCount_sound) _)

theorem cellPrimeCase_sound : cellPrimeCase.Sound :=
  cellPrimeCount_sound.seq (cellLtStart_sound.seq (identity_sound.branchZero cellRootCount_sound _))

theorem completeCell_sound : completeCell.Sound :=
  (cellPrimeStart_sound.seq (identity_sound.branchZero cellPrimeCase_sound _)).seq
    (clearRegisters_sound _)

theorem cellPrimeCount_requires (v : BinaryValues 70) : cellPrimeCount.requires v := by
  simp [cellPrimeCount, branchZero, binarySucc, identity, emitBits]

theorem cellPrimeCount_delta (v : BinaryValues 70) :
    CoreDelta v (cellPrimeCount.effect v) (if v (coreReg 3) = 0 then 1 else 0) 0 := by
  by_cases h : v (coreReg 3) = 0
  · simp only [cellPrimeCount, branchZero, h, ite_true]
    exact coreSuccPrime_delta v
  · simp only [cellPrimeCount, branchZero, h, ite_false, identity, emitBits]
    exact CoreDelta.refl v

theorem cellDerivativeCount_requires (v : BinaryValues 70)
    (hv : ValidCoreInput (v (coreReg 0))) : cellDerivativeCount.requires v := by
  refine ⟨cellEvalStart_requires true v hv, ?_⟩
  simp [branchZero, identity, emitBits, binarySucc]

theorem cellDerivativeCount_delta (v : BinaryValues 70)
    (hv : ValidCoreInput (v (coreReg 0))) :
    CoreDelta v (cellDerivativeCount.effect v) 0 (cellTest true v) := by
  have hdelta := cellEvalStart_delta true v hv
  have hflag := cellEvalStart_flag true v hv
  change (cellEvalStart true).effect v 31 = cellTest true v at hflag
  change CoreDelta v ((branchZero 31 identity (binarySucc (coreReg 5))).effect
    ((cellEvalStart true).effect v)) _ _
  simp only [branchZero, hflag]
  by_cases hzero : cellTest true v = 0
  · simp only [hzero, ite_true, identity, emitBits]
    exact hdelta
  · have hone : cellTest true v = 1 := by have := cellTest_le_one true v; omega
    simp only [hone, one_ne_zero, ite_false]
    simpa only [Nat.zero_add] using hdelta.trans (coreSuccRoot_delta _)

theorem cellRootCount_requires (v : BinaryValues 70)
    (hv : ValidCoreInput (v (coreReg 0))) : cellRootCount.requires v := by
  rw [cellRootCount, routine_seq_requires]
  refine ⟨cellEvalStart_requires false v hv, ?_⟩
  rw [routine_branch_requires]
  by_cases h : (cellEvalStart false).effect v 31 = 0
  · rw [ite_eq_left h]; trivial
  · rw [ite_eq_right h]
    rw [routine_seq_requires]
    exact ⟨trivial, cellDerivativeCount_requires _
      (((cellEvalStart_delta false v hv).trans (coreSuccRoot_delta _)).valid hv)⟩

theorem cellRootCount_delta (v : BinaryValues 70)
    (hv : ValidCoreInput (v (coreReg 0))) :
    CoreDelta v (cellRootCount.effect v) 0 (cellRootWeight v) := by
  have hdelta := cellEvalStart_delta false v hv
  have hflag := cellEvalStart_flag false v hv
  change (cellEvalStart false).effect v 31 = cellTest false v at hflag
  change CoreDelta v ((branchZero 31 identity
    (seq (binarySucc (coreReg 5)) cellDerivativeCount)).effect ((cellEvalStart false).effect v)) _ _
  simp only [branchZero, hflag, cellRootWeight]
  by_cases hzero : cellTest false v = 0
  · simp only [hzero, ite_true, identity, emitBits]
    exact hdelta
  · simp only [hzero, ite_false]
    rw [routine_seq_effect]
    have hfirst := hdelta.trans (coreSuccRoot_delta _)
    have hnext := cellDerivativeCount_delta _ (hfirst.valid hv)
    rw [hfirst.test true] at hnext
    simpa only [Nat.zero_add] using hfirst.trans hnext

theorem cellPrimeCase_requires (v : BinaryValues 70)
    (hv : ValidCoreInput (v (coreReg 0))) : cellPrimeCase.requires v := by
  refine ⟨cellPrimeCount_requires v, cellLtStart_requires _, ?_⟩
  change if cellLtStart.effect (cellPrimeCount.effect v) 2 = 0 then True
    else cellRootCount.requires (cellLtStart.effect (cellPrimeCount.effect v))
  by_cases h : cellLtStart.effect (cellPrimeCount.effect v) 2 = 0
  · simp only [h, ite_true]
  · rw [ite_eq_right h]
    exact cellRootCount_requires _ (((cellPrimeCount_delta v).trans (coreLtStart_delta _)).valid hv)

theorem cellPrimeCase_delta (v : BinaryValues 70)
    (hv : ValidCoreInput (v (coreReg 0))) :
    CoreDelta v (cellPrimeCase.effect v) (if v (coreReg 3) = 0 then 1 else 0)
      (if v (coreReg 3) < v (coreReg 2) then cellRootWeight v else 0) := by
  have hfirst := (cellPrimeCount_delta v).trans (coreLtStart_delta _)
  have hflag := cellLtStart_flag (cellPrimeCount.effect v)
  rw [(cellPrimeCount_delta v).residue, (cellPrimeCount_delta v).prime] at hflag
  change CoreDelta v ((branchZero 2 identity cellRootCount).effect
    (cellLtStart.effect (cellPrimeCount.effect v))) _ _
  simp only [branchZero, hflag]
  by_cases hlt : v (coreReg 3) < v (coreReg 2)
  · simp only [hlt, ite_true, one_ne_zero, ite_false]
    have hnext := cellRootCount_delta _ (hfirst.valid hv)
    rw [hfirst.rootWeight] at hnext
    simpa only [Nat.add_zero, Nat.zero_add] using hfirst.trans hnext
  · simp only [hlt, ite_false, ite_true, identity, emitBits]
    simpa only [Nat.add_zero, id_eq] using hfirst

theorem completeCell_requires (v : BinaryValues 70)
    (hv : ValidCoreInput (v (coreReg 0))) : completeCell.requires v := by
  refine ⟨⟨cellPrimeStart_requires v, ?_⟩, clearRegisters_requires _ _⟩
  change if cellPrimeStart.effect v 6 = 0 then True else cellPrimeCase.requires (cellPrimeStart.effect v)
  by_cases h : cellPrimeStart.effect v 6 = 0
  · simp only [h, ite_true]
  · rw [ite_eq_right h]
    exact cellPrimeCase_requires _ ((corePrimeStart_delta v).valid hv)

theorem corePrimeContribution_branch (input p a : ℕ) :
    corePrimeContribution input p a = if p.Prime then (if a = 0 then 1 else 0) else 0 := by
  by_cases hp : p.Prime <;> simp [corePrimeContribution, streamPrimeIncrement, hp]

theorem coreRootContribution_branch (v : BinaryValues 70) :
    coreRootContribution (v (coreReg 0)) (v (coreReg 2)) (v (coreReg 3)) =
      if (v (coreReg 2)).Prime then
        (if v (coreReg 3) < v (coreReg 2) then cellRootWeight v else 0) else 0 := by
  by_cases hp : (v (coreReg 2)).Prime
  · have hmod := cellModulus_eq (v (coreReg 2)) hp.pos
    unfold coreRootContribution streamRootIncrement cellRootWeight cellTest cellZeroFlag
    rw [hmod]
    by_cases ha : v (coreReg 3) < v (coreReg 2) <;>
      by_cases hr : SparseDiv.StringArith.isZeroBits (sparseEvalModStr false
        (SparseDiv.encNat (v (coreReg 2))) (SparseDiv.encNat (v (coreReg 3)))
          (unpackedInput (v (coreReg 0)))) = [true] <;>
      by_cases hd : SparseDiv.StringArith.isZeroBits (sparseEvalModStr true
        (SparseDiv.encNat (v (coreReg 2))) (SparseDiv.encNat (v (coreReg 3)))
          (unpackedInput (v (coreReg 0)))) = [true] <;>
      simp [hp, ha, hr, hd]
  · simp [coreRootContribution, streamRootIncrement, hp]

/-- The complete actual cell has exactly the two mathematical increments
used in the proved rectangular enumeration invariant. -/
theorem completeCell_effect (v : BinaryValues 70)
    (hv : ValidCoreInput (v (coreReg 0))) :
    completeCell.effect v =
      coreValues (v (coreReg 0)) (v (coreReg 1)) (v (coreReg 2)) (v (coreReg 3))
        (v (coreReg 4) + corePrimeContribution (v (coreReg 0)) (v (coreReg 2)) (v (coreReg 3)))
        (v (coreReg 5) + coreRootContribution (v (coreReg 0)) (v (coreReg 2)) (v (coreReg 3))) := by
  rw [corePrimeContribution_branch, coreRootContribution_branch]
  change clearCoreWorkspace.effect
    ((branchZero 6 identity cellPrimeCase).effect (cellPrimeStart.effect v)) = _
  simp only [branchZero, cellPrimeStart_flag]
  have hstart := corePrimeStart_delta v
  by_cases hp : (v (coreReg 2)).Prime
  · simp only [hp, ite_true, one_ne_zero, ite_false]
    have hcase := cellPrimeCase_delta _ (hstart.valid hv)
    rw [hstart.residue, hstart.prime, hstart.rootWeight] at hcase
    simpa only [Nat.zero_add] using (hstart.trans hcase).clear
  · simp only [hp, ite_false, ite_true, identity, emitBits, id_eq]
    exact hstart.clear

/-- The former cell interface is instantiated by the actual, internally
verified arithmetic machine; its only domain condition is a genuine encoded
sparse input. -/
def completeCellSpec : CoreCellSpec completeCell corePrimeContribution coreRootContribution where
  valid := ValidCoreInput
  requires := by
    intro input X p a P A hvalid _ _
    exact completeCell_requires _ (by simpa using hvalid)
  effect := by
    intro input X p a P A hvalid _ _
    have h := completeCell_effect (coreValues input X p a P A) (by simpa using hvalid)
    simpa using h

end SparseIrred.UpperBounds.Machine
