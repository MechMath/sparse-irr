/-
The branch Hoare proof is adapted from Complexitylib's BinaryRoutine/Control/Internal.lean.
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in Complexitylib's LICENSE file.
-/
import SparseIrred.UpperBounds.Machine.StreamingBinarySilence
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.SpaceBounds

/-!
# Space bounds for the branch actually taken

The concrete machine, effect, domain, output, and time bound are those of the
library zero branch. Only the advertised space bound is sharpened to the selected
branch. Soundness follows from the actual branch Hoare rule: the other branch has
an impossible precondition and therefore needs no workspace allowance.
-/

namespace SparseIrred.UpperBounds.Machine

open Complexity BinaryRoutine

def branchZeroSelected {n : ℕ} (idx : Fin n) (onZero onPositive : BinaryRoutine n) :
    BinaryRoutine n :=
  { branchZero idx onZero onPositive with
    spaceBound := fun S v ↦ if v idx = 0 then onZero.spaceBound S v else onPositive.spaceBound S v }

private theorem impossibleHoareTimeSpace {n : ℕ} (tm : TM n) (post : TapePred n)
    (time inputLength space : ℕ) :
    tm.HoareTimeSpace (fun _ _ _ ↦ False) post time inputLength space := by
  constructor
  · intro _ _ _ hfalse
    exact hfalse.elim
  · intro _ _ _ hfalse _ _
    exact hfalse.elim

theorem branchZeroSelected_sound {n : ℕ} {onZero onPositive : BinaryRoutine n}
    (hzeroSound : onZero.Sound) (hpositiveSound : onPositive.Sound) (idx : Fin n) :
    (branchZeroSelected idx onZero onPositive).Sound := by
  constructor
  · intro values inp₀ ys inputLength initialSpace hrequires hinp hinitialSpace hinputSpace
    have hframe : ∀ inp work out, CanonicalPred inp₀ values ys inp work out →
        inp.read ≠ Γ.start ∧ (∀ i, (work i).read ≠ Γ.start) ∧ out.read ≠ Γ.start := by
      rintro inp work out ⟨rfl, rfl, hout⟩
      exact ⟨hinp.read_ne_start, fun i ↦ (workTapes_parked values i).read_ne_start,
        hout.parked.read_ne_start⟩
    by_cases hzero : values idx = 0
    · have hrequiresZero : onZero.requires values := by
        simpa [branchZeroSelected, branchZero, hzero] using hrequires
      have hzeroRun := hzeroSound.hoareTimeSpace values inp₀ ys
        inputLength initialSpace hrequiresZero hinp hinitialSpace hinputSpace
      have hpositiveRun := impossibleHoareTimeSpace onPositive.machine
        (fun _ _ _ ↦ False) (onPositive.timeBound values) inputLength 0
      have hbranch := TM.branchWorkBlankTM_hoareTimeSpace idx
        onZero.machine onPositive.machine hframe (fun _ _ _ hpre _ ↦ hpre)
        (fun _ work _ hpre hnonblank ↦ by
          rcases hpre with ⟨_rfl, hwork, _hout⟩
          have hbinary := workTapes_hasBinaryNat values idx
          rw [hwork] at hnonblank
          exact False.elim (hnonblank (hbinary.read_eq_blank_iff.2 hzero)))
        hzeroRun hpositiveRun
      refine hbranch.consequence (fun _ _ _ h ↦ h) ?_ le_rfl le_rfl ?_
      · intro inp work out hpost
        rcases hpost with hpost | hfalse
        · simpa [branchZeroSelected, branchZero, hzero] using hpost
        · exact False.elim hfalse
      · simp [branchZeroSelected, hzero]
    · have hrequiresPositive : onPositive.requires values := by
        simpa [branchZeroSelected, branchZero, hzero] using hrequires
      have hzeroRun := impossibleHoareTimeSpace onZero.machine
        (fun _ _ _ ↦ False) (onZero.timeBound values) inputLength 0
      have hpositiveRun := hpositiveSound.hoareTimeSpace values inp₀ ys
        inputLength initialSpace hrequiresPositive hinp hinitialSpace hinputSpace
      have hbranch := TM.branchWorkBlankTM_hoareTimeSpace idx
        onZero.machine onPositive.machine hframe
        (fun _ work _ hpre hblank ↦ by
          rcases hpre with ⟨_rfl, hwork, _hout⟩
          have hbinary := workTapes_hasBinaryNat values idx
          rw [hwork] at hblank
          exact False.elim (hzero (hbinary.read_eq_blank_iff.1 hblank)))
        (fun _ _ _ hpre _ ↦ hpre) hzeroRun hpositiveRun
      refine hbranch.consequence (fun _ _ _ h ↦ h) ?_ le_rfl le_rfl ?_
      · intro inp work out hpost
        rcases hpost with hfalse | hpost
        · exact False.elim hfalse
        · simpa [branchZeroSelected, branchZero, hzero] using hpost
      · simp [branchZeroSelected, hzero]
  · exact hzeroSound.isTransducer.branchWorkBlankTM hpositiveSound.isTransducer

theorem branchZeroSelected_silent {n : ℕ} {onZero onPositive : BinaryRoutine n}
    (hzero : RoutineSilent onZero) (hpositive : RoutineSilent onPositive) (idx : Fin n) :
    RoutineSilent (branchZeroSelected idx onZero onPositive) :=
  hzero.branchZero hpositive idx

/-- A uniform width estimate on reindexed families gives a conditional pointwise
estimate, without requiring any values outside the stated domain to be well formed. -/
theorem spaceWidth_on_condition {n : ℕ} (r : BinaryRoutine n) (P : ℕ → Prop)
    (S W : ℕ → ℕ) (v : ℕ → BinaryValues n)
    (h : ∀ index : ℕ → ℕ, (∀ j, P (index j)) →
      SpaceBoundByWidthAt r (fun j ↦ S (index j)) (fun j ↦ v (index j))
        (fun j ↦ W (index j))) :
    ∃ C, ∀ j, P j → r.spaceBound (S j) (v j) ≤ S j + C * (W j).size + C := by
  classical
  by_cases hex : ∃ j, P j
  · obtain ⟨j₀, hj₀⟩ := hex
    let index : ℕ → ℕ := fun j ↦ if P j then j else j₀
    have hindex (j : ℕ) : P (index j) := by
      dsimp only [index]
      split_ifs with hj
      · exact hj
      · exact hj₀
    obtain ⟨C, hC⟩ := h index hindex
    refine ⟨C, fun j hj ↦ ?_⟩
    simpa only [index, ite_eq_left hj] using hC j
  · exact ⟨0, fun j hj ↦ (hex ⟨j, hj⟩).elim⟩

theorem branchZeroSelected_space {n : ℕ} (idx : Fin n) (onZero onPositive : BinaryRoutine n)
    {S W : ℕ → ℕ} {v : ℕ → BinaryValues n}
    (hz : ∃ C, ∀ j, v j idx = 0 →
      onZero.spaceBound (S j) (v j) ≤ S j + C * (W j).size + C)
    (hp : ∃ C, ∀ j, v j idx ≠ 0 →
      onPositive.spaceBound (S j) (v j) ≤ S j + C * (W j).size + C) :
    SpaceBoundByWidthAt (branchZeroSelected idx onZero onPositive) S v W := by
  obtain ⟨C₀, hC₀⟩ := hz
  obtain ⟨C₁, hC₁⟩ := hp
  refine ⟨C₀ + C₁, fun j ↦ ?_⟩
  change (if v j idx = 0 then _ else _) ≤ _
  split_ifs with hj
  · exact (hC₀ j hj).trans (by nlinarith)
  · exact (hC₁ j hj).trans (by nlinarith)

end SparseIrred.UpperBounds.Machine
