import SparseIrred.UpperBounds.Machine.StreamingBinaryCell
import SparseIrred.UpperBounds.Machine.StreamingBinaryCoreSemantics
import SparseIrred.UpperBounds.Machine.StreamingBinaryEval
import SparseIrred.UpperBounds.Machine.StreamingBinaryArithmeticSilent

/-! # A total positive-modulus adapter for one enumeration-cell evaluation -/

set_option maxHeartbeats 1000000

namespace SparseIrred.UpperBounds.Machine

open Complexity BinaryRoutine SparseDiv SparseDiv.Appendix SparseDiv.StringArith

def cellModulus (p : ℕ) : ℕ := if p = 0 then 1 else p

theorem cellModulus_pos (p : ℕ) : 0 < cellModulus p := by
  unfold cellModulus
  split_ifs <;> omega

theorem cellModulus_eq (p : ℕ) (hp : 0 < p) : cellModulus p = p := by
  simp [cellModulus, Nat.ne_of_gt hp]

def cellEvalCopies : BinaryRoutine 70 :=
  seq (clear 5) (seq (binaryCopy (coreReg 0) 16 5)
    (seq (binaryCopy (coreReg 2) 17 5) (binaryCopy (coreReg 3) 18 5)))

/-- The modulus is clamped away from zero even on unselected resource-analysis
branches; on a prime candidate this leaves the modulus unchanged. -/
def cellEvalPrepare : BinaryRoutine 70 :=
  seq cellEvalCopies (branchZero 17 (BinaryRoutine.set 17 1) identity)

def cellEvalStart (deriv : Bool) : BinaryRoutine 70 :=
  seq cellEvalPrepare (binarySparseEval deriv)

theorem cellEvalCopies_sound : cellEvalCopies.Sound :=
  (clear_sound _).seq ((binaryCopy_sound _ _ _).seq
    ((binaryCopy_sound _ _ _).seq (binaryCopy_sound _ _ _)))

theorem cellEvalPrepare_sound : cellEvalPrepare.Sound :=
  cellEvalCopies_sound.seq ((set_sound _ _).branchZero identity_sound _)

theorem cellEvalStart_sound (deriv : Bool) : (cellEvalStart deriv).Sound :=
  cellEvalPrepare_sound.seq (binarySparseEval_sound deriv)

theorem cellEvalCopies_requires (v : BinaryValues 70) : cellEvalCopies.requires v := by
  simp [cellEvalCopies, seq, clear, binaryCopy, coreReg]

theorem cellEvalPrepare_requires (v : BinaryValues 70) : cellEvalPrepare.requires v := by
  refine ⟨cellEvalCopies_requires v, ?_⟩
  simp [branchZero, BinaryRoutine.set, seq, clear, addConst, identity, emitBits]

theorem cellEvalCopies_at (v : BinaryValues 70) (i : Fin 70) :
    cellEvalCopies.effect v i =
      if i = 16 then v (coreReg 0) else if i = 17 then v (coreReg 2)
      else if i = 18 then v (coreReg 3) else if i = 5 then 0 else v i := by
  change Function.update (Function.update (Function.update (Function.update v 5 0)
    16 (v (coreReg 0))) 17 (v (coreReg 2))) 18 (v (coreReg 3)) i = _
  by_cases h16 : i = 16
  · subst i; simp
  · by_cases h17 : i = 17
    · subst i; simp
    · by_cases h18 : i = 18
      · subst i; simp
      · simp [Function.update_apply, h16, h17, h18]

theorem cellEvalPrepare_at (v : BinaryValues 70) (i : Fin 70) :
    cellEvalPrepare.effect v i =
      if i = 16 then v (coreReg 0) else if i = 17 then cellModulus (v (coreReg 2))
      else if i = 18 then v (coreReg 3) else if i = 5 then 0 else v i := by
  have hset (w : BinaryValues 70) :
      (BinaryRoutine.set (17 : Fin 70) 1).effect w = Function.update w 17 1 := by
    simp only [BinaryRoutine.set, seq, clear, addConst, Function.update_self,
      Nat.zero_add, Function.update_idem]
  change (if cellEvalCopies.effect v 17 = 0 then
    (BinaryRoutine.set (17 : Fin 70) 1).effect (cellEvalCopies.effect v)
    else cellEvalCopies.effect v) i = _
  have h17v : cellEvalCopies.effect v 17 = v (coreReg 2) := by simp [cellEvalCopies_at]
  rw [h17v]
  simp only [hset]
  by_cases h17 : i = 17
  · subst i
    by_cases hp : v (coreReg 2) = 0 <;> simp [hp, cellModulus, cellEvalCopies_at]
  · by_cases hp : v (coreReg 2) = 0 <;>
      simp [hp, h17, Function.update_apply, cellModulus, cellEvalCopies_at]

theorem cellEvalPrepare_preserves (v : BinaryValues 70) (i : Fin 6) :
    cellEvalPrepare.effect v (coreReg i) = v (coreReg i) := by
  have hlow : ∀ j : Fin 70, j.val < 64 → coreReg i ≠ j := by
    intro j hj heq
    have hh := congrArg Fin.val heq
    simp [coreReg] at hh
    omega
  rw [cellEvalPrepare_at]
  simp [hlow 16 (by decide), hlow 17 (by decide), hlow 18 (by decide), hlow 5 (by decide)]

theorem cellEvalStart_requires (deriv : Bool) (v : BinaryValues 70)
    (hvalid : ValidCoreInput (v (coreReg 0))) : (cellEvalStart deriv).requires v := by
  obtain ⟨l, hl⟩ := hvalid
  refine ⟨cellEvalPrepare_requires v, binarySparseEval_requires deriv _ l ?_ ?_⟩
  · simpa [cellEvalPrepare_at] using hl
  · simpa [cellEvalPrepare_at] using cellModulus_pos (v (coreReg 2))

theorem cellEvalStart_preserves (deriv : Bool) (v : BinaryValues 70)
    (hvalid : ValidCoreInput (v (coreReg 0))) (i : Fin 6) :
    (cellEvalStart deriv).effect v (coreReg i) = v (coreReg i) := by
  obtain ⟨l, hl⟩ := hvalid
  change (binarySparseEval deriv).effect (cellEvalPrepare.effect v) (coreReg i) = _
  rw [binarySparseEval_frame deriv _ l
    (by simpa [cellEvalPrepare_at] using hl)
    (by simpa [cellEvalPrepare_at] using cellModulus_pos (v (coreReg 2)))
    _ (by simp [coreReg]; omega), cellEvalPrepare_preserves]

/-- The exact numeric flag used by the internal root-count increment. -/
def cellZeroFlag (deriv : Bool) (input p a : ℕ) : ℕ :=
  if isZeroBits (sparseEvalModStr deriv (encNat p) (encNat a) (unpackedInput input)) = [true]
    then 1 else 0

theorem cellZeroFlag_le_one (deriv : Bool) (input p a : ℕ) :
    cellZeroFlag deriv input p a ≤ 1 := by
  unfold cellZeroFlag
  split_ifs <;> omega

theorem cellEvalStart_flag (deriv : Bool) (v : BinaryValues 70)
    (hvalid : ValidCoreInput (v (coreReg 0))) :
    (cellEvalStart deriv).effect v 31 =
      cellZeroFlag deriv (v (coreReg 0)) (cellModulus (v (coreReg 2))) (v (coreReg 3)) := by
  obtain ⟨l, hl⟩ := hvalid
  have hs : cellEvalPrepare.effect v 16 = packedInput (encITerms l) := by
    simpa [cellEvalPrepare_at] using hl
  have hm : 0 < cellEvalPrepare.effect v 17 := by
    simpa [cellEvalPrepare_at] using cellModulus_pos (v (coreReg 2))
  have hiff := binarySparseEval_zero_iff deriv (cellEvalPrepare.effect v) l hs hm
  have hbound := binarySparseEval_flag_le_one deriv (cellEvalPrepare.effect v)
  have hp17 : cellEvalPrepare.effect v 17 = cellModulus (v (coreReg 2)) := by
    simp [cellEvalPrepare_at]
  have ha18 : cellEvalPrepare.effect v 18 = v (coreReg 3) := by simp [cellEvalPrepare_at]
  rw [hp17, ha18] at hiff
  have hroot := sparseEvalModStr_nat_isZero_iff deriv (cellModulus (v (coreReg 2)))
    (v (coreReg 3)) l (Nat.ne_of_gt (cellModulus_pos _))
  change (binarySparseEval deriv).effect (cellEvalPrepare.effect v) 31 = _
  unfold cellZeroFlag
  rw [hl, unpackedInput_packedInput]
  split_ifs with hzero
  · exact hiff.mpr (hroot.mp hzero)
  · have hne : (binarySparseEval deriv).effect (cellEvalPrepare.effect v) 31 ≠ 1 :=
      fun h ↦ hzero (hroot.mpr (hiff.mp h))
    omega

theorem cellEvalStart_flag_pos (deriv : Bool) (v : BinaryValues 70)
    (hvalid : ValidCoreInput (v (coreReg 0))) (hp : 0 < v (coreReg 2)) :
    (cellEvalStart deriv).effect v 31 =
      cellZeroFlag deriv (v (coreReg 0)) (v (coreReg 2)) (v (coreReg 3)) := by
  rw [cellEvalStart_flag deriv v hvalid, cellModulus_eq _ hp]

end SparseIrred.UpperBounds.Machine
