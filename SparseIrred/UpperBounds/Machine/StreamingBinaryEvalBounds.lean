import SparseIrred.UpperBounds.Machine.StreamingBinaryEval

/-! # Uniform numeric bounds at every sparse-loop boundary -/

namespace SparseIrred.UpperBounds.Machine

open Complexity BinaryRoutine SparseDiv SparseDiv.Appendix

theorem binaryEvalInit_values_le (v : BinaryValues 70) (B : ℕ) (hv : ∀ j, v j ≤ B)
    (j : Fin 70) : binaryEvalInit.effect v j ≤ B := by
  rw [binaryEvalInit_effect]
  split_ifs <;> first | exact hv _ | exact Nat.zero_le _

/-- The loop body returns all disposable registers to zero, reduces each sum
modulo the modulus, and only shortens the remaining table. -/
theorem binarySparseEvalBody_values_le (deriv : Bool) (v : BinaryValues 70) (l : ITerms)
    (hs : v 16 = packedInput (encITerms l)) (hm : 0 < v 17)
    (hp : v 19 < v 17) (hn : v 20 < v 17) (B : ℕ) (hv : ∀ j, v j ≤ B)
    (j : Fin 70) : (binarySparseEvalBody deriv).effect v j ≤ B := by
  cases l with
  | nil =>
    rw [binarySparseEvalBody_nil deriv v hs, binaryEvalProbe_effect]
    split_ifs
    · exact (Nat.sub_le _ _).trans (hv 16)
    · exact Nat.zero_le _
    · exact hv j
  | cons t ls =>
    rcases t with ⟨c, e⟩
    rw [binarySparseEvalBody_cons_effect deriv v c e ls hs hm hp hn j]
    have hb := signedEvalStep_lt deriv (v 18) (v 17) (v 19, v 20) (c, e) hm hp hn
    split_ifs
    · exact Nat.zero_le _
    · exact hb.2.le.trans (hv 17)
    · exact hb.1.le.trans (hv 17)
    · exact (packedTerms_tail_le (c, e) ls).trans (hs ▸ hv 16)
    · exact hv j

/-- Every actual loop-boundary vector fits the same numeric envelope as the input.
The iteration count is bounded by the packed input already stored in that envelope. -/
theorem binarySparseEvalLoop_values_le (deriv : Bool) (v : BinaryValues 70) (l : ITerms)
    (hs : v 16 = packedInput (encITerms l)) (hm : 0 < v 17)
    (B : ℕ) (hv : ∀ j, v j ≤ B) (i : ℕ) (hi : i ≤ packedInput (encITerms l))
    (j : Fin 70) :
    binaryForValues (binarySparseEvalBody deriv) 21 (binaryEvalInit.effect v) i j ≤ B := by
  induction i generalizing j with
  | zero => exact binaryEvalInit_values_le v B hv j
  | succ i ih =>
    have hinv := binaryEvalLoop_invariant (binarySparseEvalBody deriv) deriv l (v 17) (v 18)
      v hs rfl rfl (fun t w hw ↦ binarySparseEvalBody_step deriv l _ _ _ v t w hw hm) i
    have hval (z : Fin 70) :
        binaryForValues (binarySparseEvalBody deriv) 21 (binaryEvalInit.effect v) i z ≤ B :=
      ih (by omega) z
    obtain ⟨hp, hn⟩ := hinv.residue_bounds hm
    have hm' : 0 < binaryForValues (binarySparseEvalBody deriv) 21
        (binaryEvalInit.effect v) i 17 := by rw [hinv.modulus]; exact hm
    have hp' : binaryForValues (binarySparseEvalBody deriv) 21
          (binaryEvalInit.effect v) i 19 <
        binaryForValues (binarySparseEvalBody deriv) 21 (binaryEvalInit.effect v) i 17 := by
      rw [hinv.modulus]; exact hp
    have hn' : binaryForValues (binarySparseEvalBody deriv) 21
          (binaryEvalInit.effect v) i 20 <
        binaryForValues (binarySparseEvalBody deriv) 21 (binaryEvalInit.effect v) i 17 := by
      rw [hinv.modulus]; exact hn
    rw [binaryForValues, binaryForStep]
    by_cases hj : j = 21
    · subst j
      rw [Function.update_self, hinv.counter]
      exact hi.trans (hs ▸ hv 16)
    · rw [Function.update_of_ne hj]
      exact binarySparseEvalBody_values_le deriv _ (l.drop i) hinv.cursor hm' hp' hn' B hval j

theorem binaryEvalFinish_values_le (v : BinaryValues 70) (B : ℕ) (hB : 1 ≤ B)
    (hv : ∀ j, v j ≤ B) (j : Fin 70) : binaryEvalFinish.effect v j ≤ B := by
  let w := compareValues (v 19) (v 20) (if v 19 = v 20 then 1 else 0) 0 0
    (fun i : Fin 64 ↦ v (i.natAdd 6))
  have hw (z : Fin 70) : w z ≤ B := by
    refine Fin.addCases (m := 6) (n := 64) (fun z ↦ ?_) (fun z ↦ ?_) z
    · change compareValues _ _ _ _ _ _ (modReg 64 z) ≤ B
      rw [compareValues, framedModInput_reg]
      fin_cases z <;> simp <;> first | exact hv _ | split_ifs <;> omega
    · change w (z.natAdd 6) ≤ B
      simpa [w] using hv (z.natAdd 6)
  change (binaryCopy 2 31 5).effect (binaryEq70.effect (binaryEvalEqualityLoad.effect v)) j ≤ B
  rw [binaryEvalEqualityLoad_effect, binaryEq70_effect]
  exact values_update_le 31 hw (hw 2) j

/-- The complete evaluator also returns every register inside the same numeric envelope. -/
theorem binarySparseEval_values_le (deriv : Bool) (v : BinaryValues 70) (l : ITerms)
    (hs : v 16 = packedInput (encITerms l)) (hm : 0 < v 17)
    (B : ℕ) (hv : ∀ j, v j ≤ B) (j : Fin 70) :
    (binarySparseEval deriv).effect v j ≤ B := by
  let w := (binaryFor (binarySparseEvalBody deriv) 21 22).effect (binaryEvalInit.effect v)
  have hw (z : Fin 70) : w z ≤ B := by
    have hc : binaryForCount (21 : Fin 70) 22 (binaryEvalInit.effect v) =
        packedInput (encITerms l) := by simp [binaryForCount, binaryEvalInit_effect, evalInitRegisters, hs]
    change binaryForValues (binarySparseEvalBody deriv) 21 (binaryEvalInit.effect v) _ z ≤ B
    rw [hc]
    exact binarySparseEvalLoop_values_le deriv v l hs hm B hv _ le_rfl z
  change binaryEvalFinish.effect w j ≤ B
  exact binaryEvalFinish_values_le w B (by have := hv 17; omega) hw j

end SparseIrred.UpperBounds.Machine
