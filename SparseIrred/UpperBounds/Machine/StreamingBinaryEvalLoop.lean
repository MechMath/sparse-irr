import SparseIrred.UpperBounds.Machine.StreamingBinaryEvalInvariant

/-! # Binary-loop induction for the sparse evaluator's persistent-state invariant -/

namespace SparseIrred.UpperBounds.Machine

open Complexity BinaryRoutine Polynomial SparseDiv SparseDiv.Appendix

/-- The fixed initialization/scan/equality program surrounding a term-scanning body. -/
def binaryEvalProgram (body : BinaryRoutine 70) : BinaryRoutine 70 :=
  seq binaryEvalInit (seq (binaryFor body 21 22) binaryEvalFinish)

theorem binaryEvalProgram_sound (body : BinaryRoutine 70) (hbody : body.Sound) :
    (binaryEvalProgram body).Sound :=
  binaryEvalInit_sound.seq ((hbody.binaryFor 21 22).seq binaryEvalFinish_sound)

/-- Ordinary induction over the concrete binary-loop value trajectory. -/
theorem binaryEvalLoop_invariant (body : BinaryRoutine 70) (deriv : Bool) (l : ITerms)
    (m a : ℕ) (original : BinaryValues 70)
    (hs : original 16 = packedInput (encITerms l))
    (hm : original 17 = m) (ha : original 18 = a)
    (hstep : ∀ i v,
      SparseEvalInvariant deriv l m a (packedInput (encITerms l)) original i v →
      SparseEvalInvariant deriv l m a (packedInput (encITerms l)) original (i + 1)
        (binaryForStep body 21 v)) (i : ℕ) :
    SparseEvalInvariant deriv l m a (packedInput (encITerms l)) original i
      (binaryForValues body 21 (binaryEvalInit.effect original) i) := by
  induction i with
  | zero => exact binaryEvalInit_invariant deriv l m a original hs hm ha
  | succ i ih => exact hstep i _ ih

theorem binaryEvalLoop_requires (body : BinaryRoutine 70) (deriv : Bool) (l : ITerms)
    (m a : ℕ) (original : BinaryValues 70)
    (hs : original 16 = packedInput (encITerms l))
    (hm : original 17 = m) (ha : original 18 = a)
    (hbody : ∀ i v,
      SparseEvalInvariant deriv l m a (packedInput (encITerms l)) original i v →
      body.requires v ∧ body.effect v 21 = v 21 ∧ body.effect v 22 = v 22)
    (hstep : ∀ i v,
      SparseEvalInvariant deriv l m a (packedInput (encITerms l)) original i v →
      SparseEvalInvariant deriv l m a (packedInput (encITerms l)) original (i + 1)
        (binaryForStep body 21 v)) :
    (binaryFor body 21 22).requires (binaryEvalInit.effect original) := by
  refine ⟨by decide, ?_, ?_⟩
  · simp [binaryEvalInit_effect, evalInitRegisters]
  · intro i _
    exact hbody i _ (binaryEvalLoop_invariant body deriv l m a original hs hm ha hstep i)

/-- The actual loop endpoint has consumed the entire finite term table. -/
theorem binaryEvalLoop_final_invariant (body : BinaryRoutine 70) (deriv : Bool) (l : ITerms)
    (m a : ℕ) (original : BinaryValues 70)
    (hs : original 16 = packedInput (encITerms l))
    (hm : original 17 = m) (ha : original 18 = a)
    (hstep : ∀ i v,
      SparseEvalInvariant deriv l m a (packedInput (encITerms l)) original i v →
      SparseEvalInvariant deriv l m a (packedInput (encITerms l)) original (i + 1)
        (binaryForStep body 21 v)) :
    SparseEvalInvariant deriv l m a (packedInput (encITerms l)) original
      (packedInput (encITerms l)) ((binaryFor body 21 22).effect (binaryEvalInit.effect original)) := by
  have hc : binaryForCount (21 : Fin 70) 22 (binaryEvalInit.effect original) =
      packedInput (encITerms l) := by simp [binaryForCount, binaryEvalInit_effect, evalInitRegisters, hs]
  change SparseEvalInvariant _ _ _ _ _ _ _ (binaryForValues body 21 _ _)
  rw [hc]
  exact binaryEvalLoop_invariant body deriv l m a original hs hm ha hstep _

theorem binaryEvalProgram_requires (body : BinaryRoutine 70) (deriv : Bool) (l : ITerms)
    (m a : ℕ) (original : BinaryValues 70)
    (hs : original 16 = packedInput (encITerms l))
    (hm : original 17 = m) (ha : original 18 = a)
    (hbody : ∀ i v,
      SparseEvalInvariant deriv l m a (packedInput (encITerms l)) original i v →
      body.requires v ∧ body.effect v 21 = v 21 ∧ body.effect v 22 = v 22)
    (hstep : ∀ i v,
      SparseEvalInvariant deriv l m a (packedInput (encITerms l)) original i v →
      SparseEvalInvariant deriv l m a (packedInput (encITerms l)) original (i + 1)
        (binaryForStep body 21 v)) : (binaryEvalProgram body).requires original := by
  exact ⟨binaryEvalInit_requires original,
    binaryEvalLoop_requires body deriv l m a original hs hm ha hbody hstep,
    binaryEvalFinish_requires _⟩

theorem binaryEvalProgram_zero_iff (body : BinaryRoutine 70) (deriv : Bool) (l : ITerms)
    (m a : ℕ) (original : BinaryValues 70)
    (hs : original 16 = packedInput (encITerms l))
    (hm : original 17 = m) (ha : original 18 = a) (hmpos : 0 < m)
    (hstep : ∀ i v,
      SparseEvalInvariant deriv l m a (packedInput (encITerms l)) original i v →
      SparseEvalInvariant deriv l m a (packedInput (encITerms l)) original (i + 1)
        (binaryForStep body 21 v)) :
    (binaryEvalProgram body).effect original 31 = 1 ↔
      (if deriv then ((toPolyZ l).map (Int.castRingHom (ZMod m))).derivative.eval (a : ZMod m)
        else ((toPolyZ l).map (Int.castRingHom (ZMod m))).eval (a : ZMod m)) = 0 := by
  exact (binaryEvalLoop_final_invariant body deriv l m a original hs hm ha hstep).finish_zero_iff
    hmpos (terms_length_le_packedInput l)

end SparseIrred.UpperBounds.Machine
