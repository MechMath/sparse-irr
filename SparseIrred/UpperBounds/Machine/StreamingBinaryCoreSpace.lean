import SparseIrred.UpperBounds.Machine.StreamingBinaryCore

/-! # All-prefix space of the actual nested binary enumeration loops -/

namespace SparseIrred.UpperBounds.Machine

open Complexity BinaryRoutine
open scoped BigOperators

def coreInitial (input X P A : ℕ → ℕ) (j : ℕ) : BinaryValues 70 :=
  coreValues (input j) (X j) 0 0 (P j) (A j)

def coreRowInputs (cell : BinaryRoutine 70) (input X P A : ℕ → ℕ) : ℕ → BinaryValues 70 :=
  binaryForClampedValues (coreRow cell) (coreReg 2) (coreReg 1) (coreInitial input X P A)

def coreCellInputs (cell : BinaryRoutine 70) (input X P A : ℕ → ℕ) : ℕ → BinaryValues 70 :=
  binaryForClampedValues cell (coreReg 3) (coreReg 1) (coreRowInputs cell input X P A)

def coreRowIndex (X : ℕ → ℕ) (code : ℕ) : ℕ :=
  min (Nat.unpair code).2 (X (Nat.unpair code).1 - 1)

theorem coreRowIndex_lt (X : ℕ → ℕ) (hX : ∀ j, 0 < X j) (code : ℕ) :
    coreRowIndex X code < X (Nat.unpair code).1 := by
  have := min_le_right (Nat.unpair code).2 (X (Nat.unpair code).1 - 1)
  have := hX (Nat.unpair code).1
  dsimp [coreRowIndex]
  omega

theorem coreRowInputs_eq {cell : BinaryRoutine 70} {incP incA : ℕ → ℕ → ℕ → ℕ}
    (spec : CoreCellSpec cell incP incA) (input X P A : ℕ → ℕ)
    (hvalid : ∀ j, spec.valid (input j)) (hX : ∀ j, 0 < X j)
    (code : ℕ) :
    coreRowInputs cell input X P A code =
      coreValues (input (Nat.unpair code).1) (X (Nat.unpair code).1) (coreRowIndex X code) 0
        (P (Nat.unpair code).1 + ∑ p ∈ Finset.range (coreRowIndex X code),
          ∑ a ∈ Finset.range (X (Nat.unpair code).1), incP (input (Nat.unpair code).1) p a)
        (A (Nat.unpair code).1 + ∑ p ∈ Finset.range (coreRowIndex X code),
          ∑ a ∈ Finset.range (X (Nat.unpair code).1), incA (input (Nat.unpair code).1) p a) := by
  unfold coreRowInputs binaryForClampedValues
  dsimp only
  have hcount : binaryForCount (coreReg 2) (coreReg 1)
      (coreInitial input X P A (Nat.unpair code).1) = X (Nat.unpair code).1 := by
    simp [binaryForCount, coreInitial]
  rw [hcount]
  exact coreEnumeration_values spec _ _ _ _ _ (hvalid _) (coreRowIndex_lt X hX code).le

/-- Expose the exact arithmetic state at every actual inner-loop body entry. -/
theorem coreCellInputs_eq {cell : BinaryRoutine 70} {incP incA : ℕ → ℕ → ℕ → ℕ}
    (spec : CoreCellSpec cell incP incA) (input X P A : ℕ → ℕ)
    (hvalid : ∀ j, spec.valid (input j)) (hX : ∀ j, 0 < X j)
    (code : ℕ) :
    let row := (Nat.unpair code).1
    let j := (Nat.unpair row).1
    let p := coreRowIndex X row
    let a := min (Nat.unpair code).2 (X j - 1)
    coreCellInputs cell input X P A code = coreValues (input j) (X j) p a
      (P j + (∑ q ∈ Finset.range p, ∑ b ∈ Finset.range (X j), incP (input j) q b) +
        ∑ b ∈ Finset.range a, incP (input j) p b)
      (A j + (∑ q ∈ Finset.range p, ∑ b ∈ Finset.range (X j), incA (input j) q b) +
        ∑ b ∈ Finset.range a, incA (input j) p b) := by
  dsimp only
  unfold coreCellInputs binaryForClampedValues
  dsimp only
  have hcount : binaryForCount (coreReg 3) (coreReg 1)
      (coreRowInputs cell input X P A (Nat.unpair code).1) =
      X (Nat.unpair (Nat.unpair code).1).1 := by
    rw [coreRowInputs_eq spec input X P A hvalid hX]
    simp [binaryForCount]
  rw [hcount, coreRowInputs_eq spec input X P A hvalid hX]
  apply coreInner_values spec _ _ _ _ _ _ (hvalid _) (coreRowIndex_lt X hX _)
  exact (min_le_right _ _).trans (Nat.sub_le _ _)

/-- Two binary loop controllers preserve a single space budget for all
iterations. The only non-controller obligation is the proved cell routine's
space certificate on its exact reachable input trajectory. -/
theorem coreEnumeration_space {cell : BinaryRoutine 70} {incP incA : ℕ → ℕ → ℕ → ℕ}
    (spec : CoreCellSpec cell incP incA) (input X P A S W : ℕ → ℕ)
    (hvalid : ∀ j, spec.valid (input j)) (hX : ∀ j, 0 < X j) (hXW : ∀ j, X j ≤ W j)
    (hcell : SpaceBoundByWidthAt cell
      (fun code ↦ S (Nat.unpair (Nat.unpair code).1).1)
      (coreCellInputs cell input X P A)
      (fun code ↦ W (Nat.unpair (Nat.unpair code).1).1)) :
    SpaceBoundByWidthAt (coreEnumeration cell) S (coreInitial input X P A) W := by
  apply SpaceBoundByWidthAt.binaryFor_of_clamped_body
  · intro j; simpa [coreInitial] using hXW j
  · intro j count hc
    have hc' : count < X j := by simpa [binaryForCount, coreInitial] using hc
    rw [show coreInitial input X P A j = coreValues (input j) (X j) 0 0 (P j) (A j) from rfl,
      coreEnumeration_values spec _ _ _ _ _ (hvalid _) hc'.le]
    simpa using hc'.le.trans (hXW j)
  · change SpaceBoundByWidthAt (coreRow cell) _ (coreRowInputs cell input X P A) _
    apply SpaceBoundByWidthAt.seq
    · apply SpaceBoundByWidthAt.binaryFor_of_clamped_body
      · intro code
        rw [coreRowInputs_eq spec input X P A hvalid hX]
        simpa using hXW (Nat.unpair code).1
      · intro code count hc
        have hc' : count < X (Nat.unpair code).1 := by
          rw [coreRowInputs_eq spec input X P A hvalid hX] at hc
          simpa [binaryForCount] using hc
        rw [coreRowInputs_eq spec input X P A hvalid hX,
          coreInner_values spec _ _ _ _ _ _ (hvalid _) (coreRowIndex_lt X hX code) hc'.le]
        simpa using hc'.le.trans (hXW (Nat.unpair code).1)
      · exact hcell
    · apply SpaceBoundByWidthAt.clear
      intro code
      rw [coreRowInputs_eq spec input X P A hvalid hX,
        coreInner_effect spec _ _ _ _ _ (hvalid _) (coreRowIndex_lt X hX code)]
      simpa using hXW (Nat.unpair code).1

end SparseIrred.UpperBounds.Machine
