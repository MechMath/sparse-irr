import SparseIrred.UpperBounds.Machine.StreamingBinaryCell
import SparseIrred.UpperBounds.Machine.StreamingBinaryArithmeticSilent

/-! # Workspace values and output preservation of enumeration-cell adapters -/

namespace SparseIrred.UpperBounds.Machine
open Complexity BinaryRoutine

theorem binaryPrime70_values_le (v : BinaryValues 70) (B : ℕ) (hv : ∀ i, v i ≤ B) :
    ∀ i, binaryPrime70.effect v i ≤ B + 1 := by
  intro i
  rw [binaryPrime70_effect]
  have hp := hv 0
  have hf := trialPrimeFlag_le_one (v 0) (v 0)
  split_ifs
  all_goals
    refine Fin.addCases (m := 6) (n := 64) (fun i ↦ ?_) (fun i ↦ ?_) i
    · rw [binaryPrimeValues, framedModInput, Fin.append_left]
      fin_cases i <;> simp <;> omega
    · rw [binaryPrimeValues, framedModInput, Fin.append_right]
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simp <;> omega
      · simp only [Fin.cons_succ, prime70Extra]
        exact (hv _).trans (Nat.le_add_right _ 1)

theorem cellPrimeStart_values_le (v : BinaryValues 70) (B : ℕ) (hv : ∀ i, v i ≤ B) :
    ∀ i, cellPrimeStart.effect v i ≤ B + 3 := by
  intro i
  apply (binaryPrime70_values_le _ B ?_ i).trans (by omega)
  intro z
  by_cases h0 : z = 0 <;> by_cases h5 : z = 5
  · subst z; contradiction
  · subst z; simpa [binaryCopy, clear, coreReg] using hv (coreReg 2)
  · subst z; simp [binaryCopy, clear]
  · simpa [binaryCopy, clear, h0, h5] using hv z

theorem cellLtStart_values_le (v : BinaryValues 70) (B : ℕ) (hv : ∀ i, v i ≤ B) :
    ∀ i, cellLtStart.effect v i ≤ B + 1 := by
  intro i
  change binaryLt70.effect (cellLtPrepare.effect v) i ≤ _
  rw [binaryLt70_effect_of_scratchZero _ (by simp [cellLtPrepare_at])]
  have hp := cellLtPrepare_values_le v B hv
  refine Fin.addCases (m := 6) (n := 64) (fun i ↦ ?_) (fun i ↦ ?_) i
  · rw [compareValues, framedModInput, Fin.append_left]
    have h0 := hp 0
    have h1 := hp 1
    fin_cases i <;> simp <;> (try split_ifs) <;> omega
  · rw [compareValues, framedModInput, Fin.append_right]
    exact (hp _).trans (Nat.le_add_right _ 1)

theorem binaryPrimeClean_silent (k : ℕ) : RoutineSilent (binaryPrimeClean k) :=
  (routineSilent_clear _).seq ((routineSilent_clear _).seq (routineSilent_clear _))

theorem binaryPrimeBody_silent (k : ℕ) : RoutineSilent (binaryPrimeBody k) :=
  (framedMod_silent _).seq
    (((routineSilent_clear _).branchZero routineSilent_identity _).seq (binaryPrimeClean_silent k))

theorem binaryPrimeLoop_silent (k : ℕ) : RoutineSilent (binaryPrimeLoop k) :=
  (binaryPrimeBody_silent k).binaryFor _ _

theorem binaryPrimeProbe_silent (k : ℕ) : RoutineSilent (binaryPrimeProbe k) :=
  (routineSilent_copy _ _ _).seq (routineSilent_pred _)

theorem binaryPrimePrepare_silent (k : ℕ) : RoutineSilent (binaryPrimePrepare k) :=
  (routineSilent_set _ _).seq (routineSilent_set _ _)

theorem binaryPrime_silent (k : ℕ) : RoutineSilent (binaryPrime k) :=
  routineSilent_identity.branchZero ((binaryPrimeProbe_silent k).seq
    (routineSilent_identity.branchZero ((binaryPrimePrepare_silent k).seq
      (binaryPrimeLoop_silent k)) _)) _

theorem binaryPrime70_silent : RoutineSilent binaryPrime70 :=
  (routineSilent_clearRegisters _).seq (binaryPrime_silent _)

theorem cellPrimeStart_silent : RoutineSilent cellPrimeStart :=
  (routineSilent_clear _).seq ((routineSilent_copy _ _ _).seq binaryPrime70_silent)

theorem cellLtPrepare_silent : RoutineSilent cellLtPrepare :=
  (routineSilent_clear _).seq ((routineSilent_copy _ _ _).seq (routineSilent_copy _ _ _))

theorem cellLtStart_silent : RoutineSilent cellLtStart := cellLtPrepare_silent.seq binaryLt70_silent

theorem clearCoreWorkspace_silent : RoutineSilent clearCoreWorkspace := routineSilent_clearRegisters _

theorem clearCoreWorkspace_space {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (hv : ∀ j i, v j i ≤ W j) : SpaceBoundByWidthAt clearCoreWorkspace S v W :=
  clearRegisters_space _ hv

end SparseIrred.UpperBounds.Machine
