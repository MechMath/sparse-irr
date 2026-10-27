import SparseIrred.UpperBounds.Machine.StreamingBinaryEvalControls
import SparseIrred.UpperBounds.Machine.StreamingBinaryEvalSemantics

/-! # One complete parsed-term update of the sparse evaluator's persistent state -/

namespace SparseIrred.UpperBounds.Machine

open Complexity BinaryRoutine

theorem binaryEvalStoreTerm_requires (v : BinaryValues 70) (h5 : v 5 = 0) :
    binaryEvalStoreTerm.requires v := by
  refine ⟨?_, clearRegisters_requires _ _⟩
  simp [seq, binaryCopy, h5]

theorem binaryEvalStoreTerm_effect (v : BinaryValues 70) (j : Fin 70) :
    binaryEvalStoreTerm.effect v j =
      if j ∈ evalDisposableRegisters then 0 else if j = 20 then v 12
        else if j = 19 then v 11 else v j := by
  simp only [binaryEvalStoreTerm, seq, binaryCopy, clearRegisters_effect,
    show (12 : Fin 70) ≠ 19 by decide, Function.update_apply, ite_false]

/-- Transfer the parsed coefficient, exponent, and sign to the actual arithmetic
machine, execute it, and return the canonical residues to registers 19 and 20. -/
def binaryEvalTermStep (deriv : Bool) : BinaryRoutine 70 :=
  seq binaryEvalLoadTerm (seq (binarySignedEvalTerm deriv) binaryEvalStoreTerm)

theorem binaryEvalTermStep_sound (deriv : Bool) : (binaryEvalTermStep deriv).Sound :=
  binaryEvalLoadTerm_sound.seq ((binarySignedEvalTerm_sound deriv).seq binaryEvalStoreTerm_sound)

theorem binarySignedEvalTerm_scratch_zero (deriv : Bool) (a m e c sign pos neg : ℕ)
    (extra : Fin 57 → ℕ) (hm : 0 < m) :
    (binarySignedEvalTerm deriv).effect (signedTermValues a m e 0 c sign pos neg 0 extra) 5 = 0 := by
  cases deriv
  · rw [binarySignedEvalTerm, ite_eq_right Bool.false_ne_true,
      binarySignedTerm_effect _ _ _ _ _ _ _ _ hm]
    simp [signedTermValues_eq, Fin.append, Fin.addCases]
  · simp only [binarySignedEvalTerm, ↓reduceIte,
      binarySignedDerivative_effect _ _ _ _ _ _ _ _ hm]
    split_ifs <;> simp [signedTermValues_eq, Fin.append, Fin.addCases]

theorem binaryEvalTermStep_requires (deriv : Bool) (v : BinaryValues 70) (hm : 0 < v 17) :
    (binaryEvalTermStep deriv).requires v := by
  refine ⟨binaryEvalLoadTerm_requires v, ?_⟩
  rw [binaryEvalLoadTerm_effect]
  exact ⟨binarySignedEvalTerm_requires _ _ _ _ _ _ _ _ _ hm,
    binaryEvalStoreTerm_requires _ (binarySignedEvalTerm_scratch_zero _ _ _ _ _ _ _ _ _ hm)⟩

/-- The exact pure update of the persistent positive residue. -/
def evalTermStepPos (deriv : Bool) (v : BinaryValues 70) : ℕ :=
  if v 28 = 0 then (v 19 + evalTermMagnitude deriv (v 18) (v 26) (v 27)) % v 17 else v 19

/-- The exact pure update of the persistent negative residue. -/
def evalTermStepNeg (deriv : Bool) (v : BinaryValues 70) : ℕ :=
  if v 28 = 0 then v 20 else (v 20 + evalTermMagnitude deriv (v 18) (v 26) (v 27)) % v 17

theorem binaryEvalTermStep_effect (deriv : Bool) (v : BinaryValues 70)
    (hm : 0 < v 17) (hp : v 19 < v 17) (hn : v 20 < v 17) (j : Fin 70) :
    (binaryEvalTermStep deriv).effect v j =
      if j ∈ evalDisposableRegisters then 0 else if j = 20 then evalTermStepNeg deriv v
        else if j = 19 then evalTermStepPos deriv v else v j := by
  change binaryEvalStoreTerm.effect
    ((binarySignedEvalTerm deriv).effect (binaryEvalLoadTerm.effect v)) j = _
  rw [binaryEvalLoadTerm_effect, binaryEvalStoreTerm_effect]
  have hacc := binarySignedEvalTerm_accumulators deriv (v 18) (v 17) (v 27) (v 26)
    (v 28) (v 19) (v 20) (fun i ↦ v (i.natAdd 13)) hm hp hn
  have hpos := congrArg Prod.fst hacc
  have hneg := congrArg Prod.snd hacc
  dsimp only at hpos hneg
  by_cases hdis : j ∈ evalDisposableRegisters
  · simp [hdis]
  · simp only [hdis, ↓reduceIte]
    by_cases hj20 : j = 20
    · simp only [hj20, ↓reduceIte, hneg, evalTermStepNeg]
    · by_cases hj19 : j = 19
      · simp [hj20, hj19, hpos, evalTermStepPos]
      · simp only [hj20, hj19, ↓reduceIte]
        have hj : 13 ≤ j.val := by
          simp only [evalDisposableRegisters, List.mem_cons,
            Fin.ext_iff] at hdis
          omega
        let i : Fin 57 := ⟨j.val - 13, by have := j.isLt; omega⟩
        have hji : i.natAdd 13 = j := Fin.ext (by simp [i]; omega)
        simpa only [hji] using binarySignedEvalTerm_extra deriv (v 18) (v 17) (v 27) (v 26)
          (v 28) (v 19) (v 20) (fun i ↦ v (i.natAdd 13)) hm i

end SparseIrred.UpperBounds.Machine
