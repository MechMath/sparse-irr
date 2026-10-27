import SparseIrred.UpperBounds.Machine.StreamingBinaryEvalBounds
import SparseIrred.UpperBounds.Machine.StreamingBinaryEvalBoundarySpace
import SparseIrred.UpperBounds.Machine.StreamingBinaryEvalStepSpace
import SparseIrred.UpperBounds.Machine.StreamingBinaryInputTermSpace

/-! # All-prefix linear-width space of the complete actual sparse evaluator -/

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

namespace SparseIrred.UpperBounds.Machine

open Complexity BinaryRoutine SparseDiv SparseDiv.Appendix

theorem binaryEvalProbe_values_le (v : BinaryValues 70) (B : ℕ) (hv : ∀ i, v i ≤ B)
    (i : Fin 70) : binaryEvalProbe.effect v i ≤ B := by
  rw [binaryEvalProbe_effect]
  split_ifs
  · exact (Nat.sub_le _ _).trans (hv 16)
  · exact Nat.zero_le _
  · exact hv i

/-- Only executed parser branches contribute to the space bound; an exhausted
input cursor needs no correctness or resource assumption about a nonexistent next term. -/
theorem binarySparseEvalBody_space (deriv : Bool) (l : ℕ → ITerms)
    {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (hs : ∀ j, v j 16 = packedInput (encITerms (l j))) (hm : ∀ j, 0 < v j 17)
    (hp : ∀ j, v j 19 < v j 17) (hn : ∀ j, v j 20 < v j 17)
    (hv : ∀ j i, v j i ≤ W j) : SpaceBoundByWidthAt (binarySparseEvalBody deriv) S v W := by
  classical
  apply SpaceBoundByWidthAt.seq
  · apply binaryEvalProbe_space
    · intro j; rw [hs j]; exact packedInput_pos _
    · exact hv
  · apply branchZeroSelected_space
    · exact ⟨0, fun j _ ↦ by simp [identity, emitBits]⟩
    · apply spaceWidth_on_condition
      intro index hindex
      let c (j : ℕ) := ((l (index j)).headD (0, 0)).1
      let e (j : ℕ) := ((l (index j)).headD (0, 0)).2
      let ls (j : ℕ) := (l (index j)).tail
      let w (j : ℕ) := binaryEvalProbe.effect (v (index j))
      have hcons (j : ℕ) : l (index j) = (c j, e j) :: ls j := by
        cases hl : l (index j) with
        | nil =>
          have hh := hindex j
          simp [binaryEvalProbe_effect, hs (index j), hl, encITerms, SparseDiv.StringArith.frame] at hh
        | cons t ts => simp [c, e, ls, hl]
      have hcode (j : ℕ) : w j 16 = packedInput (encITerms ((c j, e j) :: ls j)) := by
        rw [show w j 16 = v (index j) 16 from binaryEvalProbe_cursor _, hs (index j), hcons j]
      have hw (j : ℕ) (i : Fin 70) : w j i ≤ W (index j) :=
        binaryEvalProbe_values_le _ _ (hv (index j)) i
      apply SpaceBoundByWidthAt.seq
      · exact parseTerm70_space c e ls hcode hw
      · apply spaceWidth_mul_add 32
        have hparsed (j : ℕ) (i : Fin 70) : parseTerm70.effect (w j) i ≤ 32 * W (index j) :=
          parseTerm70_values_le _ _ _ _ _ (hcode j) (hw j) i
        have hkeep (j : ℕ) (i : Fin 70) (hi : 17 ≤ i.val ∧ i.val ≤ 22) :
            parseTerm70.effect (w j) i = v (index j) i := by
          obtain ⟨_, _, _, _, hframe⟩ := parseTerm70_spec (w j) (c j) (e j) (ls j) (hcode j)
          exact (hframe i (Or.inl hi)).trans (binaryEvalProbe_high _ i (by omega))
        change SpaceBoundByWidthAt (binaryEvalTermStep deriv) (fun j ↦ S (index j))
          (fun j ↦ parseTerm70.effect (w j)) (fun j ↦ 32 * W (index j) + 32)
        apply (binaryEvalTermStep_space_linearWidth (S := fun j ↦ S (index j))
          (B := fun j ↦ 32 * W (index j)) (v := fun j ↦ parseTerm70.effect (w j))
          deriv hparsed ?_ ?_ ?_).mono
        · intro j; omega
        · intro j; rw [hkeep j 17 (by norm_num)]; exact hm (index j)
        · intro j; rw [hkeep j 19 (by norm_num), hkeep j 17 (by norm_num)]; exact hp (index j)
        · intro j; rw [hkeep j 20 (by norm_num), hkeep j 17 (by norm_num)]; exact hn (index j)

theorem binarySparseEvalLoop_space (deriv : Bool) (l : ℕ → ITerms)
    {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (hs : ∀ j, v j 16 = packedInput (encITerms (l j))) (hm : ∀ j, 0 < v j 17)
    (hv : ∀ j i, v j i ≤ W j) :
    SpaceBoundByWidthAt (binaryFor (binarySparseEvalBody deriv) 21 22) S
      (fun j ↦ binaryEvalInit.effect (v j)) W := by
  have hcount (j : ℕ) : binaryForCount (21 : Fin 70) 22 (binaryEvalInit.effect (v j)) =
      packedInput (encITerms (l j)) := by
    simp [binaryForCount, binaryEvalInit_effect, evalInitRegisters, hs j]
  have hinv (j t : ℕ) := binaryEvalLoop_invariant (binarySparseEvalBody deriv) deriv (l j)
    (v j 17) (v j 18) (v j) (hs j) rfl rfl
    (fun i w hw ↦ binarySparseEvalBody_step deriv (l j) _ _ _ (v j) i w hw (hm j)) t
  apply SpaceBoundByWidthAt.binaryFor_of_clamped_body
  · intro j
    simpa [binaryEvalInit_effect] using hv j 16
  · intro j t ht
    exact binarySparseEvalLoop_values_le deriv (v j) (l j) (hs j) (hm j) (W j) (hv j) t
      (by rw [hcount j] at ht; omega) 21
  · let steps (code : ℕ) := min (Nat.unpair code).2
      (packedInput (encITerms (l (Nat.unpair code).1)) - 1)
    have heq : binaryForClampedValues (binarySparseEvalBody deriv) 21 22
        (fun j ↦ binaryEvalInit.effect (v j)) =
        (fun code ↦ binaryForValues (binarySparseEvalBody deriv) 21
          (binaryEvalInit.effect (v (Nat.unpair code).1)) (steps code)) := by
      funext code
      simp only [binaryForClampedValues, hcount, steps]
    rw [heq]
    apply binarySparseEvalBody_space deriv (fun code ↦ (l (Nat.unpair code).1).drop (steps code))
    · intro code; exact (hinv (Nat.unpair code).1 (steps code)).cursor
    · intro code
      rw [(hinv (Nat.unpair code).1 (steps code)).modulus]
      exact hm (Nat.unpair code).1
    · intro code
      have h := hinv (Nat.unpair code).1 (steps code)
      rw [h.modulus]
      exact (h.residue_bounds (hm (Nat.unpair code).1)).1
    · intro code
      have h := hinv (Nat.unpair code).1 (steps code)
      rw [h.modulus]
      exact (h.residue_bounds (hm (Nat.unpair code).1)).2
    · intro code i
      apply binarySparseEvalLoop_values_le deriv _ _ (hs (Nat.unpair code).1)
        (hm (Nat.unpair code).1) _ (hv (Nat.unpair code).1) _ _ i
      dsimp only [steps]
      exact (Nat.min_le_right _ _).trans (Nat.sub_le _ _)

/-- The whole real machine, including table parsing, signed arithmetic, derivative
handling, and final comparison, uses space linear in the binary register width. -/
theorem binarySparseEval_space (deriv : Bool) (l : ℕ → ITerms)
    {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (hs : ∀ j, v j 16 = packedInput (encITerms (l j))) (hm : ∀ j, 0 < v j 17)
    (hv : ∀ j i, v j i ≤ W j) : SpaceBoundByWidthAt (binarySparseEval deriv) S v W := by
  apply SpaceBoundByWidthAt.seq
  · exact binaryEvalInit_space hv
  · apply SpaceBoundByWidthAt.seq
    · exact binarySparseEvalLoop_space deriv l hs hm hv
    · apply binaryEvalFinish_space
      · intro j; have := hm j; have := hv j 17; omega
      · intro j i
        have hc : binaryForCount (21 : Fin 70) 22 (binaryEvalInit.effect (v j)) =
            packedInput (encITerms (l j)) := by
          simp [binaryForCount, binaryEvalInit_effect, evalInitRegisters, hs j]
        change binaryForValues (binarySparseEvalBody deriv) 21 (binaryEvalInit.effect (v j)) _ i ≤ W j
        rw [hc]
        exact binarySparseEvalLoop_values_le deriv _ _ (hs j) (hm j) _ (hv j) _ le_rfl i

end SparseIrred.UpperBounds.Machine
