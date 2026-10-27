import SparseIrred.UpperBounds.Machine.StreamingBinaryEvalBody

/-! # Complete actual sparse evaluator and derivative zero-test machine -/

namespace SparseIrred.UpperBounds.Machine

open Complexity BinaryRoutine Polynomial SparseDiv SparseDiv.Appendix

theorem binarySparseEvalBody_preserves (deriv : Bool) (v : BinaryValues 70) (l : ITerms)
    (hs : v 16 = packedInput (encITerms l)) (hm : 0 < v 17)
    (hp : v 19 < v 17) (hn : v 20 < v 17) (j : Fin 70)
    (hj : j.val = 17 ∨ j.val = 18 ∨ j.val = 21 ∨ j.val = 22 ∨ 32 ≤ j.val) :
    (binarySparseEvalBody deriv).effect v j = v j := by
  cases l with
  | nil => rw [binarySparseEvalBody_nil deriv v hs]; exact binaryEvalProbe_high v j (by omega)
  | cons t ls =>
    rcases t with ⟨c, e⟩
    rw [binarySparseEvalBody_cons_effect deriv v c e ls hs hm hp hn j]
    have hnot : j ∉ evalDisposableRegisters := by
      simp only [evalDisposableRegisters, List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff]
      omega
    have h20 : j ≠ 20 := by intro h; subst j; norm_num at hj
    have h19 : j ≠ 19 := by intro h; subst j; norm_num at hj
    have h16 : j ≠ 16 := by intro h; subst j; norm_num at hj
    simp [hnot, h20, h19, h16]

/-- One real loop iteration preserves the exact input/prefix/counter interpretation. -/
theorem binarySparseEvalBody_step (deriv : Bool) (l : ITerms) (m a N : ℕ)
    (original : BinaryValues 70) (i : ℕ) (v : BinaryValues 70)
    (h : SparseEvalInvariant deriv l m a N original i v) (hm : 0 < m) :
    SparseEvalInvariant deriv l m a N original (i + 1)
      (binaryForStep (binarySparseEvalBody deriv) 21 v) := by
  obtain ⟨hp, hn⟩ := h.residue_bounds hm
  have hvmod : 0 < v 17 := by rw [h.modulus]; exact hm
  have hvpos : v 19 < v 17 := by rw [h.modulus]; exact hp
  have hvneg : v 20 < v 17 := by rw [h.modulus]; exact hn
  cases hd : l.drop i with
  | nil =>
    have hs : v 16 = packedInput (encITerms []) := by rw [h.cursor, hd]
    have hnext : l.drop (i + 1) = [] := by
      apply List.drop_eq_nil_iff.mpr
      have := List.drop_eq_nil_iff.mp hd
      omega
    have hfold := signedEvalFold_take_succ_of_drop_nil deriv a m l i hd (0, 0)
    have hb := binarySparseEvalBody_nil deriv v hs
    constructor
    · simp [binaryForStep, hb, binaryEvalProbe_effect, h.cursor, hd, hnext]
    · simp [binaryForStep, hb, binaryEvalProbe_effect, h.modulus]
    · simp [binaryForStep, hb, binaryEvalProbe_effect, h.base]
    · simp [binaryForStep, hb, binaryEvalProbe_effect, h.positive, hfold]
    · simp [binaryForStep, hb, binaryEvalProbe_effect, h.negative, hfold]
    · simp [binaryForStep, h.counter]
    · simp [binaryForStep, hb, binaryEvalProbe_effect, h.limit]
    · intro j hj
      have h21 : j ≠ 21 := by intro he; subst j; norm_num at hj
      rw [binaryForStep, Function.update_of_ne h21, hb,
        binaryEvalProbe_high v j (by omega)]
      exact h.frame j hj
  | cons t tail =>
    rcases t with ⟨c, e⟩
    have hs : v 16 = packedInput (encITerms ((c, e) :: tail)) := by rw [h.cursor, hd]
    have hnext := drop_succ_of_drop_cons l i (c, e) tail hd
    have hfold := signedEvalFold_take_succ deriv a m l i (c, e) tail hd (0, 0)
    have hb (j : Fin 70) := binarySparseEvalBody_cons_effect deriv v c e tail hs
      hvmod hvpos hvneg j
    constructor
    · simp [binaryForStep, hb, evalDisposableRegisters, hnext]
    · simp [binaryForStep, hb, evalDisposableRegisters, h.modulus]
    · simp [binaryForStep, hb, evalDisposableRegisters, h.base]
    · simp [binaryForStep, hb, evalDisposableRegisters, hfold,
        h.modulus, h.base, h.positive, h.negative]
    · simp [binaryForStep, hb, evalDisposableRegisters, hfold,
        h.modulus, h.base, h.positive, h.negative]
    · simp [binaryForStep, h.counter]
    · simp [binaryForStep, hb, evalDisposableRegisters, h.limit]
    · intro j hj
      have h21 : j ≠ 21 := by intro he; subst j; norm_num at hj
      rw [binaryForStep, Function.update_of_ne h21,
        binarySparseEvalBody_preserves deriv v _ hs hvmod hvpos hvneg j (by omega)]
      exact h.frame j hj

/-- The uniform machine for ordinary or derivative sparse evaluation.
Inputs are read from registers 16 (packed table), 17 (modulus), and 18 (base).
The literal zero-test flag is returned in register 31; registers 32 onward are preserved. -/
def binarySparseEval (deriv : Bool) : BinaryRoutine 70 :=
  binaryEvalProgram (binarySparseEvalBody deriv)

theorem binarySparseEval_sound (deriv : Bool) : (binarySparseEval deriv).Sound :=
  binaryEvalProgram_sound _ (binarySparseEvalBody_sound deriv)

theorem binarySparseEval_requires (deriv : Bool) (v : BinaryValues 70) (l : ITerms)
    (hs : v 16 = packedInput (encITerms l)) (hm : 0 < v 17) :
    (binarySparseEval deriv).requires v := by
  apply binaryEvalProgram_requires (binarySparseEvalBody deriv) deriv l (v 17) (v 18) v hs rfl rfl
  · intro i w hw
    obtain ⟨hp, hn⟩ := hw.residue_bounds hm
    have hm' : 0 < w 17 := by rw [hw.modulus]; exact hm
    have hp' : w 19 < w 17 := by rw [hw.modulus]; exact hp
    have hn' : w 20 < w 17 := by rw [hw.modulus]; exact hn
    refine ⟨binarySparseEvalBody_requires deriv w (l.drop i) hw.cursor hm', ?_, ?_⟩
    · exact binarySparseEvalBody_preserves deriv w _ hw.cursor hm' hp' hn' 21 (by norm_num)
    · exact binarySparseEvalBody_preserves deriv w _ hw.cursor hm' hp' hn' 22 (by norm_num)
  · intro i w hw
    exact binarySparseEvalBody_step deriv l _ _ _ v i w hw hm

/-- The final flag of the actual machine is exactly polynomial (or derivative) zero. -/
theorem binarySparseEval_zero_iff (deriv : Bool) (v : BinaryValues 70) (l : ITerms)
    (hs : v 16 = packedInput (encITerms l)) (hm : 0 < v 17) :
    (binarySparseEval deriv).effect v 31 = 1 ↔
      (if deriv then ((toPolyZ l).map (Int.castRingHom (ZMod (v 17)))).derivative.eval
          (v 18 : ZMod (v 17))
        else ((toPolyZ l).map (Int.castRingHom (ZMod (v 17)))).eval
          (v 18 : ZMod (v 17))) = 0 := by
  apply binaryEvalProgram_zero_iff (binarySparseEvalBody deriv) deriv l (v 17) (v 18) v hs rfl rfl hm
  intro i w hw
  exact binarySparseEvalBody_step deriv l _ _ _ v i w hw hm

theorem binarySparseEval_frame (deriv : Bool) (v : BinaryValues 70) (l : ITerms)
    (hs : v 16 = packedInput (encITerms l)) (hm : 0 < v 17)
    (j : Fin 70) (hj : 32 ≤ j.val) : (binarySparseEval deriv).effect v j = v j := by
  have h := binaryEvalLoop_final_invariant (binarySparseEvalBody deriv) deriv l
    (v 17) (v 18) v hs rfl rfl (fun i w hw ↦
      binarySparseEvalBody_step deriv l _ _ _ v i w hw hm)
  exact h.finish_frame j hj

theorem binarySparseEval_modulus (deriv : Bool) (v : BinaryValues 70) (l : ITerms)
    (hs : v 16 = packedInput (encITerms l)) (hm : 0 < v 17) :
    (binarySparseEval deriv).effect v 17 = v 17 := by
  have h := binaryEvalLoop_final_invariant (binarySparseEvalBody deriv) deriv l
    (v 17) (v 18) v hs rfl rfl (fun i w hw ↦
      binarySparseEvalBody_step deriv l _ _ _ v i w hw hm)
  change binaryEvalFinish.effect _ 17 = _
  rw [binaryEvalFinish_effect _ 17 (by decide)]
  simpa using h.modulus

theorem binarySparseEval_base (deriv : Bool) (v : BinaryValues 70) (l : ITerms)
    (hs : v 16 = packedInput (encITerms l)) (hm : 0 < v 17) :
    (binarySparseEval deriv).effect v 18 = v 18 := by
  have h := binaryEvalLoop_final_invariant (binarySparseEvalBody deriv) deriv l
    (v 17) (v 18) v hs rfl rfl (fun i w hw ↦
      binarySparseEvalBody_step deriv l _ _ _ v i w hw hm)
  change binaryEvalFinish.effect _ 18 = _
  rw [binaryEvalFinish_effect _ 18 (by decide)]
  simpa using h.base

/-- Every execution of the pure machine effect returns a literal Boolean flag. -/
theorem binarySparseEval_flag_le_one (deriv : Bool) (v : BinaryValues 70) :
    (binarySparseEval deriv).effect v 31 ≤ 1 := by
  change binaryEvalFinish.effect _ 31 ≤ 1
  rw [binaryEvalFinish_effect _ 31 (by decide)]
  simp only [↓reduceIte]
  split_ifs <;> omega

/-- Zero in the output flag is precisely failure of the polynomial zero test. -/
theorem binarySparseEval_flag_zero_iff (deriv : Bool) (v : BinaryValues 70) (l : ITerms)
    (hs : v 16 = packedInput (encITerms l)) (hm : 0 < v 17) :
    (binarySparseEval deriv).effect v 31 = 0 ↔
      (if deriv then ((toPolyZ l).map (Int.castRingHom (ZMod (v 17)))).derivative.eval
          (v 18 : ZMod (v 17))
        else ((toPolyZ l).map (Int.castRingHom (ZMod (v 17)))).eval
          (v 18 : ZMod (v 17))) ≠ 0 := by
  have hb := binarySparseEval_flag_le_one deriv v
  have he := binarySparseEval_zero_iff deriv v l hs hm
  constructor
  · intro hzero heval
    have hone := he.mpr heval
    omega
  · intro hnonzero
    have hnotone : (binarySparseEval deriv).effect v 31 ≠ 1 := fun h ↦ hnonzero (he.mp h)
    omega

end SparseIrred.UpperBounds.Machine
