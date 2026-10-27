import SparseIrred.UpperBounds.Machine.StreamingBinaryEvalPrefix
import SparseIrred.UpperBounds.Machine.StreamingBinaryEvalBoundary

/-! # Persistent-state invariant for the actual sparse evaluator -/

namespace SparseIrred.UpperBounds.Machine

open Complexity BinaryRoutine Polynomial SparseDiv SparseDiv.Appendix

/-- Meaning of every live register at an outer sparse-scan boundary. -/
structure SparseEvalInvariant (deriv : Bool) (l : ITerms) (m a N : ℕ)
    (original : BinaryValues 70) (i : ℕ) (v : BinaryValues 70) : Prop where
  cursor : v 16 = packedInput (encITerms (l.drop i))
  modulus : v 17 = m
  base : v 18 = a
  positive : v 19 = (signedEvalFold deriv a m (l.take i) (0, 0)).1
  negative : v 20 = (signedEvalFold deriv a m (l.take i) (0, 0)).2
  counter : v 21 = i
  limit : v 22 = N
  frame : ∀ j : Fin 70, 32 ≤ j.val → v j = original j

theorem binaryEvalInit_invariant (deriv : Bool) (l : ITerms) (m a : ℕ) (v : BinaryValues 70)
    (hs : v 16 = packedInput (encITerms l)) (hm : v 17 = m) (ha : v 18 = a) :
    SparseEvalInvariant deriv l m a (packedInput (encITerms l)) v 0 (binaryEvalInit.effect v) := by
  constructor
  · simp [binaryEvalInit_effect, evalInitRegisters, hs]
  · simp [binaryEvalInit_effect, evalInitRegisters, hm]
  · simp [binaryEvalInit_effect, evalInitRegisters, ha]
  · simp [binaryEvalInit_effect, evalInitRegisters, signedEvalFold]
  · simp [binaryEvalInit_effect, evalInitRegisters, signedEvalFold]
  · simp [binaryEvalInit_effect, evalInitRegisters]
  · simp [binaryEvalInit_effect, hs]
  · intro j hj
    have hneq : j ≠ 22 := by intro h; subst j; norm_num at hj
    have hnot : j ∉ evalInitRegisters := by
      simp only [evalInitRegisters, List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff]
      omega
    simp [binaryEvalInit_effect, hneq, hnot]

theorem SparseEvalInvariant.residue_bounds {deriv : Bool} {l : ITerms} {m a N i : ℕ}
    {original v : BinaryValues 70} (h : SparseEvalInvariant deriv l m a N original i v)
    (hm : 0 < m) : v 19 < m ∧ v 20 < m := by
  rw [h.positive, h.negative]
  exact signedEvalFold_lt deriv a m (l.take i) (0, 0) hm hm hm

/-- At the completed loop boundary, actual equality testing gives the polynomial zero test. -/
theorem SparseEvalInvariant.finish_zero_iff {deriv : Bool} {l : ITerms} {m a N : ℕ}
    {original v : BinaryValues 70} (h : SparseEvalInvariant deriv l m a N original N v)
    (hm : 0 < m) (hN : l.length ≤ N) :
    binaryEvalFinish.effect v 31 = 1 ↔
      (if deriv then ((toPolyZ l).map (Int.castRingHom (ZMod m))).derivative.eval (a : ZMod m)
        else ((toPolyZ l).map (Int.castRingHom (ZMod m))).eval (a : ZMod m)) = 0 := by
  rw [binaryEvalFinish_effect v 31 (by decide)]
  simp only [↓reduceIte]
  have heq : (if v 19 = v 20 then 1 else 0) = 1 ↔ v 19 = v 20 := by
    by_cases hh : v 19 = v 20 <;> simp [hh]
  rw [heq, h.positive, h.negative, List.take_of_length_le hN]
  exact signedEvalFold_eq_iff_eval_zero deriv a m l hm

theorem SparseEvalInvariant.finish_frame {deriv : Bool} {l : ITerms} {m a N i : ℕ}
    {original v : BinaryValues 70} (h : SparseEvalInvariant deriv l m a N original i v)
    (j : Fin 70) (hj : 32 ≤ j.val) : binaryEvalFinish.effect v j = original j := by
  rw [binaryEvalFinish_effect v j (by omega)]
  have hneq : j ≠ 31 := by intro he; subst j; norm_num at hj
  rw [ite_eq_right hneq]
  exact h.frame j hj

end SparseIrred.UpperBounds.Machine
