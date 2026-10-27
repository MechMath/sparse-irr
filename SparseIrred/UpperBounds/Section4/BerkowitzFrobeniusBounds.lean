import SparseIrred.UpperBounds.Section4.BerkowitzFrobeniusProgram
import SparseIrred.UpperBounds.Section4.EntryMachineBounds
import SparseIrred.UpperBounds.Section4.StackRestricted
import SparseIrred.UpperBounds.Section4.BerkowitzProgramBounds

/-!
# Address bounds for nested Frobenius powering

Every exponent interval remains inside `q*d`; all row and column indices already
belong to `Fin d`. Thus the extra calls used by a deleted minor have binary-sized
addresses throughout their execution.
-/

namespace SparseIrred.UpperBounds.Section4

open Matrix Polynomial

/-- The only natural-number registers in a Frobenius address are those of a power call. -/
def FrobeniusEntryAddress.Bounded {d : ℕ} (q : ℕ) : FrobeniusEntryAddress d → Prop
  | .entry _ _ | .delta _ _ => True
  | .power a => a.Bounded (q * d)

variable {K : Type*} [Field K] [Fintype K]

theorem frobeniusEntryProgram_closed (f : K[X]) (hf : 0 < f.natDegree) :
    (frobeniusEntryProgram f hf).Closed (FrobeniusEntryAddress.Bounded (Fintype.card K)) := by
  intro a op l r ha h
  cases a with
  | delta i j => simp [frobeniusEntryProgram, frobeniusEntryInstruction] at h
  | entry i j =>
    cases h
    change (0 + Fintype.card K * j.val ≤ Fintype.card K * f.natDegree) ∧ True
    exact ⟨by simpa using Nat.mul_le_mul_left (Fintype.card K) j.isLt.le, trivial⟩
  | power a =>
    cases he : (productProgram (fun _ ↦ coefficientCompanion f)).instruction a with
    | value v => simp [frobeniusEntryProgram, frobeniusEntryInstruction, he] at h
    | branch op' l' r' =>
      simp only [frobeniusEntryProgram, frobeniusEntryInstruction, he,
        EntryInstruction.branch.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact productInstruction_bounded (fun _ ↦ coefficientCompanion f)
        (Fintype.card K * f.natDegree) a op' l' r' ha he

theorem frobeniusMinorEntryInitial_bounded (f : K[X]) (hf : 0 < f.natDegree)
    (i j : Fin (f.natDegree - 1 + 1))
    (kl : Fin (f.natDegree - 1) × Fin (f.natDegree - 1)) :
    (frobeniusMinorEntryInitial f hf i j kl).Bounded (Fintype.card K) := trivial

/-- Every determinant leaf request starts a valid bounded Frobenius call. -/
theorem frobeniusMinorSubprogramRequest_bounded (f : K[X]) (hf : 0 < f.natDegree)
    (i j : Fin (f.natDegree - 1 + 1)) (a : BerkowitzAddress (f.natDegree - 1))
    (b : FrobeniusEntryAddress f.natDegree)
    (hr : berkowitzSubprogramRequest (frobeniusMinorEntryInitial f hf i j) a = some b) :
    b.Bounded (Fintype.card K) := by
  unfold berkowitzSubprogramRequest at hr
  cases he : berkowitzEntryRequest a with
  | none => simp [he] at hr
  | some ij =>
    simp only [he, Option.map_some, Option.some.injEq] at hr
    subst b
    exact frobeniusMinorEntryInitial_bounded f hf i j ij

def FrobeniusMinorAddress.Bounded {d : ℕ} (q : ℕ) : FrobeniusMinorAddress d → Prop :=
  SubstituteAddress.Bounded BerkowitzAddress.Bounded (FrobeniusEntryAddress.Bounded q)

theorem minorProgram_closed (f : K[X]) (hf : 0 < f.natDegree)
    (i j : Fin (f.natDegree - 1 + 1)) :
    (minorProgram f hf i j).Closed (FrobeniusMinorAddress.Bounded (Fintype.card K)) := by
  apply EntryProgram.substitute_closed
    (berkowitzProgram (0 : Matrix (Fin (f.natDegree - 1)) (Fin (f.natDegree - 1)) K))
    (frobeniusEntryProgram f hf)
    (berkowitzSubprogramRequest (frobeniusMinorEntryInitial f hf i j))
    (frobeniusEntryBound f.natDegree (Fintype.card K))
    (berkowitzSubprogramRequest_rank _ _ _ (fun _ ↦ frobeniusEntryProgram_rank f hf _ _))
    BerkowitzAddress.Bounded (FrobeniusEntryAddress.Bounded (Fintype.card K))
  · exact berkowitzProgram_closed _
  · exact frobeniusEntryProgram_closed f hf
  · intro a b _ hr
    exact frobeniusMinorSubprogramRequest_bounded f hf i j a b hr

theorem minorInitial_bounded (d q : ℕ) : (minorInitial d).Bounded q := by
  simp [minorInitial, FrobeniusMinorAddress.Bounded, SubstituteAddress.Bounded,
    BerkowitzAddress.Bounded]

end SparseIrred.UpperBounds.Section4
