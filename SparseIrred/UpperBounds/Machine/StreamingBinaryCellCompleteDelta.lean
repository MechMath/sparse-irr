import SparseIrred.UpperBounds.Machine.StreamingBinaryCell

/-! # Composing exact updates of the six persistent enumeration registers -/

namespace SparseIrred.UpperBounds.Machine

open Complexity BinaryRoutine

/-- Exact persistent-register effect; all private workspace is abstracted
until the final clearing step restores its canonical zero contents. -/
def CoreDelta (v w : BinaryValues 70) (P A : ℕ) : Prop :=
  ∀ i : Fin 6, w (coreReg i) =
    if i = 4 then v (coreReg 4) + P else if i = 5 then v (coreReg 5) + A else v (coreReg i)

theorem CoreDelta.refl (v : BinaryValues 70) : CoreDelta v v 0 0 := by
  intro i; fin_cases i <;> simp

theorem CoreDelta.of_preserves {v w : BinaryValues 70}
    (h : ∀ i, w (coreReg i) = v (coreReg i)) : CoreDelta v w 0 0 := by
  intro i; rw [h i]; fin_cases i <;> simp

theorem CoreDelta.trans {v w z : BinaryValues 70} {P A Q B : ℕ}
    (h : CoreDelta v w P A) (g : CoreDelta w z Q B) : CoreDelta v z (P + Q) (A + B) := by
  intro i
  rw [g i]
  fin_cases i <;> simp [h _, Nat.add_assoc]

theorem CoreDelta.input {v w : BinaryValues 70} {P A : ℕ} (h : CoreDelta v w P A) :
    w (coreReg 0) = v (coreReg 0) := by simpa using h 0

theorem CoreDelta.limit {v w : BinaryValues 70} {P A : ℕ} (h : CoreDelta v w P A) :
    w (coreReg 1) = v (coreReg 1) := by simpa using h 1

theorem CoreDelta.prime {v w : BinaryValues 70} {P A : ℕ} (h : CoreDelta v w P A) :
    w (coreReg 2) = v (coreReg 2) := by simpa using h 2

theorem CoreDelta.residue {v w : BinaryValues 70} {P A : ℕ} (h : CoreDelta v w P A) :
    w (coreReg 3) = v (coreReg 3) := by simpa using h 3

theorem CoreDelta.primeCount {v w : BinaryValues 70} {P A : ℕ} (h : CoreDelta v w P A) :
    w (coreReg 4) = v (coreReg 4) + P := by simpa using h 4

theorem CoreDelta.rootCount {v w : BinaryValues 70} {P A : ℕ} (h : CoreDelta v w P A) :
    w (coreReg 5) = v (coreReg 5) + A := by simpa using h 5

theorem coreSuccPrime_delta (v : BinaryValues 70) :
    CoreDelta v ((binarySucc (coreReg 4)).effect v) 1 0 := by
  intro i
  fin_cases i <;> simp [binarySucc, coreReg]

theorem coreSuccRoot_delta (v : BinaryValues 70) :
    CoreDelta v ((binarySucc (coreReg 5)).effect v) 0 1 := by
  intro i
  fin_cases i <;> simp [binarySucc, coreReg]

theorem corePrimeStart_delta (v : BinaryValues 70) : CoreDelta v (cellPrimeStart.effect v) 0 0 :=
  CoreDelta.of_preserves (cellPrimeStart_preserves v)

theorem coreLtStart_delta (v : BinaryValues 70) : CoreDelta v (cellLtStart.effect v) 0 0 :=
  CoreDelta.of_preserves (cellLtStart_preserves v)

/-- Clearing reusable workspace turns a persistent-register contract into a
literal canonical vector equality. -/
theorem CoreDelta.clear {v w : BinaryValues 70} {P A : ℕ} (h : CoreDelta v w P A) :
    clearCoreWorkspace.effect w = coreValues (v (coreReg 0)) (v (coreReg 1))
      (v (coreReg 2)) (v (coreReg 3)) (v (coreReg 4) + P) (v (coreReg 5) + A) := by
  rw [clearCoreWorkspace_effect, h.input, h.limit, h.prime, h.residue, h.primeCount, h.rootCount]

end SparseIrred.UpperBounds.Machine
