import SparseIrred.UpperBounds.Machine.StreamingBinaryEvalDerivative
import SparseIrred.UpperBounds.Machine.StreamingBinaryEvalTermSpace
import SparseIrred.UpperBounds.Machine.StreamingMachineLinear

/-! # Linear-width workspace for formal-derivative term evaluation -/

namespace SparseIrred.UpperBounds.Machine

open Complexity BinaryRoutine

theorem binaryDerivativePrepare_space (a m e c sign pos neg : ℕ → ℕ)
    (extra : ℕ → Fin 57 → ℕ) (S W : ℕ → ℕ)
    (he : ∀ j, e j ≤ W j) (hc : ∀ j, c j ≤ W j) (hce : ∀ j, c j * e j ≤ W j) :
    SpaceBoundByWidthAt binaryDerivativePrepare S
      (fun j ↦ signedTermValues (a j) (m j) (e j) 0 (c j) (sign j)
        (pos j) (neg j) 0 (extra j)) W := by
  apply spaceWidth_mul_add 2
  apply SpaceBoundByWidthAt.seq
  · apply SpaceBoundByWidthAt.mulAdd
    · intro j
      simp [signedTermValues_eq, Fin.append, Fin.addCases]
      have := hc j; omega
    · intro j
      simp [signedTermValues_eq, Fin.append, Fin.addCases]
      have := he j; omega
    · intro j
      simp [signedTermValues_eq, Fin.append, Fin.addCases]
      have := hc j
      have := hce j
      omega
  · apply SpaceBoundByWidthAt.seq
    · apply SpaceBoundByWidthAt.binaryCopy
      · intro j
        simp [mulAdd, signedTermValues_eq, Fin.append, Fin.addCases]
        have := hce j; omega
      · intro j
        simp [mulAdd, signedTermValues_eq, Fin.append, Fin.addCases]
        have := hc j; omega
    · apply SpaceBoundByWidthAt.seq
      · apply SpaceBoundByWidthAt.clear
        intro j
        simp [binaryCopy, mulAdd, signedTermValues_eq, Fin.append, Fin.addCases]
        have := hce j; omega
      · apply SpaceBoundByWidthAt.binaryPred
        intro j
        simp [clear, binaryCopy, mulAdd, signedTermValues_eq, Fin.append, Fin.addCases]
        have := he j; omega

theorem binarySignedDerivative_space (a m e c sign pos neg : ℕ → ℕ)
    (extra : ℕ → Fin 57 → ℕ) (hm : ∀ j, 0 < m j) (S W : ℕ → ℕ)
    (ha : ∀ j, a j ≤ W j) (he : ∀ j, e j ≤ W j) (hc : ∀ j, c j ≤ W j)
    (hce : ∀ j, c j * e j ≤ W j) (ham : ∀ j, a j * m j < W j)
    (hcem : ∀ j, c j * e j * m j < W j)
    (hp : ∀ j, pos j < m j) (hn : ∀ j, neg j < m j)
    (hmW : ∀ j, m j < W j) (h2mW : ∀ j, 2 * m j < W j) :
    SpaceBoundByWidthAt binarySignedDerivative S
      (fun j ↦ signedTermValues (a j) (m j) (e j) 0 (c j) (sign j)
        (pos j) (neg j) 0 (extra j)) W := by
  apply SpaceBoundByWidthAt.branchZero 7 SpaceBoundByWidthAt.identity
  apply SpaceBoundByWidthAt.seq
  · exact binaryDerivativePrepare_space a m e c sign pos neg extra S W he hc hce
  · have heq : (fun j ↦ binaryDerivativePrepare.effect
        (signedTermValues (a j) (m j) (e j) 0 (c j) (sign j) (pos j) (neg j) 0 (extra j))) =
        (fun j ↦ signedTermValues (a j) (m j) (e j - 1) 0 (c j * e j) (sign j)
          (pos j) (neg j) 0 (extra j)) :=
      funext (fun j ↦ binaryDerivativePrepare_effect _ _ _ _ _ _ _ _)
    rw [heq]
    exact binarySignedTerm_space _ _ _ _ _ _ _ _ hm S W ha
      (fun j ↦ (Nat.sub_le _ _).trans (he j)) hce ham hcem hp hn hmW h2mW

/-- Both ordinary and derivative sparse-term evaluation use the same kind of
linear binary-width space certificate. -/
theorem binarySignedEvalTerm_space (deriv : Bool) (a m e c sign pos neg : ℕ → ℕ)
    (extra : ℕ → Fin 57 → ℕ) (hm : ∀ j, 0 < m j) (S W : ℕ → ℕ)
    (ha : ∀ j, a j ≤ W j) (he : ∀ j, e j ≤ W j) (hc : ∀ j, c j ≤ W j)
    (hce : ∀ j, c j * e j ≤ W j) (ham : ∀ j, a j * m j < W j)
    (hcm : ∀ j, c j * m j < W j) (hcem : ∀ j, c j * e j * m j < W j)
    (hp : ∀ j, pos j < m j) (hn : ∀ j, neg j < m j)
    (hmW : ∀ j, m j < W j) (h2mW : ∀ j, 2 * m j < W j) :
    SpaceBoundByWidthAt (binarySignedEvalTerm deriv) S
      (fun j ↦ signedTermValues (a j) (m j) (e j) 0 (c j) (sign j)
        (pos j) (neg j) 0 (extra j)) W := by
  cases deriv
  · exact binarySignedTerm_space a m e c sign pos neg extra hm S W ha he hc ham hcm hp hn hmW h2mW
  · exact binarySignedDerivative_space a m e c sign pos neg extra hm S W
      ha he hc hce ham hcem hp hn hmW h2mW

end SparseIrred.UpperBounds.Machine
