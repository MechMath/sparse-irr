import SparseIrred.UpperBounds.Machine.StreamingBinaryEvalTerm

/-! # All-prefix linear-width space for signed sparse-term accumulation -/

set_option maxHeartbeats 1600000

namespace SparseIrred.UpperBounds.Machine

open Complexity BinaryRoutine

theorem binaryAccStore_space (negative : Bool) {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (h0 : ∀ j, v j 0 ≤ W j) (h2 : ∀ j, v j 2 ≤ W j)
    (h3 : ∀ j, v j 3 ≤ W j) (h4 : ∀ j, v j 4 ≤ W j)
    (ha : ∀ j, v j (signedAccumulator negative) ≤ W j) :
    SpaceBoundByWidthAt (binaryAccStore negative) S v W := by
  cases negative <;>
    apply SpaceBoundByWidthAt.seq (SpaceBoundByWidthAt.binaryCopy _ _ _ h2 ha) <;>
    apply SpaceBoundByWidthAt.seq <;>
    first
    | (apply SpaceBoundByWidthAt.clear; intro j; simpa [binaryCopy, signedAccumulator] using h0 j)
    | (apply SpaceBoundByWidthAt.seq <;>
        first
        | (apply SpaceBoundByWidthAt.clear; intro j;
            simpa [clear, binaryCopy, signedAccumulator] using h2 j)
        | (apply SpaceBoundByWidthAt.seq <;>
            first
            | (apply SpaceBoundByWidthAt.clear; intro j;
                simpa [clear, binaryCopy, signedAccumulator] using h3 j)
            | (apply SpaceBoundByWidthAt.clear; intro j;
                simpa [clear, binaryCopy, signedAccumulator] using h4 j)))

theorem binaryAccumulate_space (negative : Bool)
    (a m e i c sign pos neg r : ℕ → ℕ) (extra : ℕ → Fin 57 → ℕ)
    (hm : ∀ j, 0 < m j) (S W : ℕ → ℕ)
    (hp : ∀ j, pos j < m j) (hn : ∀ j, neg j < m j) (hr : ∀ j, r j < m j)
    (hmW : ∀ j, m j < W j) (h2mW : ∀ j, 2 * m j < W j) :
    SpaceBoundByWidthAt (binaryAccumulate negative) S
      (fun j ↦ signedTermValues (a j) (m j) (e j) (i j) (c j) (sign j)
        (pos j) (neg j) (r j) (extra j)) W := by
  have hsel : ∀ j, (if negative then neg j else pos j) < m j := by
    cases negative <;> simp <;> assumption
  have hsum : ∀ j, (if negative then neg j else pos j) + r j < W j := by
    intro j
    have := hsel j
    have := hr j
    have := h2mW j
    omega
  apply SpaceBoundByWidthAt.seq
  · apply SpaceBoundByWidthAt.seq
    · apply SpaceBoundByWidthAt.seq
      · apply SpaceBoundByWidthAt.binaryCopy
        · intro j
          cases negative <;>
            simpa [signedAccumulator, signedTermValues_eq, Fin.append, Fin.addCases]
              using (Nat.le_of_lt ((hsel j).trans (hmW j)))
        · intro j
          simp [signedTermValues_eq, Fin.append, Fin.addCases]
      · apply SpaceBoundByWidthAt.add
        · intro j
          cases negative <;>
            simpa [binaryCopy, signedAccumulator, signedTermValues_eq, Fin.append, Fin.addCases]
              using Nat.le_of_lt ((hr j).trans (hmW j))
        · intro j
          cases negative <;>
            simpa [binaryCopy, signedAccumulator, signedTermValues_eq, Fin.append, Fin.addCases]
              using Nat.le_of_lt (hsum j)
    · have heq : (fun j ↦ (binaryAccLoad negative).effect
          (signedTermValues (a j) (m j) (e j) (i j) (c j) (sign j)
            (pos j) (neg j) (r j) (extra j))) =
          (fun j ↦ framedModInput ((if negative then neg j else pos j) + r j) (m j) (r j) 0 0
            (powExtra (a j) (e j) (i j)
              (termExtra (c j) (signedTermExtra (sign j) (pos j) (neg j) (extra j))))) :=
        funext (fun j ↦ binaryAccLoad_effect negative _ _ _ _ _ _ _ _ _ _)
      rw [heq]
      exact framedMod_space _ _ _ _ _ _ hm S W hsum hmW
        (fun j ↦ Nat.le_of_lt ((hr j).trans (hmW j)))
        (fun _ ↦ Nat.zero_le _) (fun _ ↦ Nat.zero_le _)
  · have heq : (fun j ↦ (seq (binaryAccLoad negative) (framedMod 64)).effect
        (signedTermValues (a j) (m j) (e j) (i j) (c j) (sign j)
          (pos j) (neg j) (r j) (extra j))) =
        (fun j ↦ framedModValues ((if negative then neg j else pos j) + r j) (m j)
          ((if negative then neg j else pos j) + r j)
          (powExtra (a j) (e j) (i j)
            (termExtra (c j) (signedTermExtra (sign j) (pos j) (neg j) (extra j))))) := by
      funext j
      change (framedMod 64).effect ((binaryAccLoad negative).effect _) = _
      rw [binaryAccLoad_effect, framedMod_effect _ _ _ _ _ _ (hm j)]
    rw [heq]
    apply binaryAccStore_space
    · intro j
      simpa [framedModValues, binaryModValues, Fin.append, Fin.addCases] using (hsum j).le
    · intro j
      have h := (Nat.mod_lt ((if negative then neg j else pos j) + r j) (hm j)).trans (hmW j)
      simpa [framedModValues, binaryModValues, Fin.append, Fin.addCases] using h.le
    · intro j
      simp [framedModValues, binaryModValues, Fin.append, Fin.addCases]
      have := hmW j
      omega
    · intro j
      simpa [framedModValues, binaryModValues, Fin.append, Fin.addCases] using (hsum j).le
    · intro j
      cases negative <;>
        simpa [signedAccumulator, framedModValues, binaryModValues, powExtra, termExtra,
          signedTermExtra, Fin.append, Fin.addCases] using ((hsel j).trans (hmW j)).le

/-- Signed term evaluation and reduction preserve a linear-width workspace. -/
theorem binarySignedTerm_space (a m e c sign pos neg : ℕ → ℕ) (extra : ℕ → Fin 57 → ℕ)
    (hm : ∀ j, 0 < m j) (S W : ℕ → ℕ)
    (ha : ∀ j, a j ≤ W j) (he : ∀ j, e j ≤ W j) (hc : ∀ j, c j ≤ W j)
    (ham : ∀ j, a j * m j < W j) (hcm : ∀ j, c j * m j < W j)
    (hp : ∀ j, pos j < m j) (hn : ∀ j, neg j < m j)
    (hmW : ∀ j, m j < W j) (h2mW : ∀ j, 2 * m j < W j) :
    SpaceBoundByWidthAt binarySignedTerm S
      (fun j ↦ signedTermValues (a j) (m j) (e j) 0 (c j) (sign j)
        (pos j) (neg j) 0 (extra j)) W := by
  apply SpaceBoundByWidthAt.seq
  · exact binaryTerm_space _ _ _ _ _ _ _ _ _ _ hm S W
      (fun _ ↦ Nat.zero_le _) hmW (fun _ ↦ Nat.zero_le _)
      (fun _ ↦ Nat.zero_le _) (fun _ ↦ Nat.zero_le _) (fun _ ↦ Nat.zero_le _)
      ha ham he hc hcm
  · have heq : (fun j ↦ (binaryTerm 60).effect
        (signedTermValues (a j) (m j) (e j) 0 (c j) (sign j) (pos j) (neg j) 0 (extra j))) =
        (fun j ↦ signedTermValues (a j) (m j) (e j) (e j) (c j) (sign j) (pos j) (neg j)
          ((c j * a j ^ e j) % m j) (extra j)) :=
      funext (fun j ↦ binaryTerm_effect _ _ _ _ _ _ _ _ _ _ (hm j))
    rw [heq]
    apply SpaceBoundByWidthAt.branchZero <;>
      exact binaryAccumulate_space _ _ _ _ _ _ _ _ _ _ _ hm S W hp hn
        (fun j ↦ Nat.mod_lt _ (hm j)) hmW h2mW

end SparseIrred.UpperBounds.Machine
