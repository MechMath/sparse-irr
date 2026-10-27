import SparseIrred.UpperBounds.Machine.StreamingBinaryEvalStep
import SparseIrred.UpperBounds.Machine.StreamingBinaryEvalLoop
import SparseIrred.UpperBounds.Machine.StreamingBinaryInputTerm
import SparseIrred.UpperBounds.Machine.StreamingBinarySelected

/-! # The actual sparse-table loop body -/

namespace SparseIrred.UpperBounds.Machine

open Complexity BinaryRoutine SparseDiv SparseDiv.Appendix

/-- Consume one framed term when the input cursor has not reached its sentinel. -/
def binarySparseEvalBody (deriv : Bool) : BinaryRoutine 70 :=
  seq binaryEvalProbe (branchZeroSelected 0 identity (seq parseTerm70 (binaryEvalTermStep deriv)))

theorem binarySparseEvalBody_sound (deriv : Bool) : (binarySparseEvalBody deriv).Sound :=
  binaryEvalProbe_sound.seq
    (branchZeroSelected_sound identity_sound (parseTerm70_sound.seq (binaryEvalTermStep_sound deriv)) _)

theorem binaryEvalProbe_cursor (v : BinaryValues 70) : binaryEvalProbe.effect v 16 = v 16 := by
  simp [binaryEvalProbe_effect]

theorem binaryEvalProbe_high (v : BinaryValues 70) (j : Fin 70) (hj : 16 ≤ j.val) :
    binaryEvalProbe.effect v j = v j := by
  rw [binaryEvalProbe_effect]
  have h0 : j ≠ 0 := by intro h; subst j; norm_num at hj
  have h5 : j ≠ 5 := by intro h; subst j; norm_num at hj
  simp [h0, h5]

theorem binaryEvalProbe_nonempty (v : BinaryValues 70) (c : ℤ) (e : ℕ) (ls : ITerms)
    (hs : v 16 = packedInput (encITerms ((c, e) :: ls))) : binaryEvalProbe.effect v 0 ≠ 0 := by
  rw [binaryEvalProbe_effect]
  simp only [↓reduceIte, hs]
  have hpos := packedInput_pos (encITerms ((c, e) :: ls))
  have hne : packedInput (encITerms ((c, e) :: ls)) ≠ 1 := by
    intro he
    have hnil := (packedTerms_eq_one_iff ((c, e) :: ls)).mp he
    simp at hnil
  omega

theorem binarySparseEvalBody_nil (deriv : Bool) (v : BinaryValues 70)
    (hs : v 16 = packedInput (encITerms [])) :
    (binarySparseEvalBody deriv).effect v = binaryEvalProbe.effect v := by
  have ht : binaryEvalProbe.effect v 0 = 0 := by simp [binaryEvalProbe_effect, hs, encITerms, SparseDiv.StringArith.frame]
  simp [binarySparseEvalBody, seq, branchZeroSelected, branchZero, ht, identity, emitBits]

theorem binarySparseEvalBody_cons (deriv : Bool) (v : BinaryValues 70) (c : ℤ) (e : ℕ)
    (ls : ITerms) (hs : v 16 = packedInput (encITerms ((c, e) :: ls))) :
    (binarySparseEvalBody deriv).effect v =
      (binaryEvalTermStep deriv).effect (parseTerm70.effect (binaryEvalProbe.effect v)) := by
  simp only [binarySparseEvalBody, seq, branchZeroSelected, branchZero, binaryEvalProbe_nonempty v c e ls hs,
    ↓reduceIte]

/-- Every syntactically valid remaining table satisfies the concrete body domain. -/
theorem binarySparseEvalBody_requires (deriv : Bool) (v : BinaryValues 70) (l : ITerms)
    (hs : v 16 = packedInput (encITerms l)) (hm : 0 < v 17) :
    (binarySparseEvalBody deriv).requires v := by
  refine ⟨binaryEvalProbe_requires v (hs ▸ packedInput_pos _), ?_⟩
  cases l with
  | nil =>
    have ht : binaryEvalProbe.effect v 0 = 0 := by simp [binaryEvalProbe_effect, hs, encITerms, SparseDiv.StringArith.frame]
    simp [branchZeroSelected, branchZero, ht, identity, emitBits]
  | cons t ls =>
    rcases t with ⟨c, e⟩
    have hc : binaryEvalProbe.effect v 16 = packedInput (encITerms ((c, e) :: ls)) :=
      (binaryEvalProbe_cursor v).trans hs
    change if binaryEvalProbe.effect v 0 = 0 then True else _
    rw [ite_eq_right (binaryEvalProbe_nonempty v c e ls hs)]
    refine ⟨parseTerm70_requires _ c e ls hc, binaryEvalTermStep_requires deriv _ ?_⟩
    obtain ⟨_, _, _, _, hkeep⟩ := parseTerm70_spec _ c e ls hc
    rw [hkeep 17 (by norm_num), binaryEvalProbe_high v 17 (by decide)]
    exact hm

/-- On a nonempty table the actual body realizes one signed modular term update. -/
theorem binarySparseEvalBody_cons_effect (deriv : Bool) (v : BinaryValues 70)
    (c : ℤ) (e : ℕ) (ls : ITerms)
    (hs : v 16 = packedInput (encITerms ((c, e) :: ls)))
    (hm : 0 < v 17) (hp : v 19 < v 17) (hn : v 20 < v 17) (j : Fin 70) :
    (binarySparseEvalBody deriv).effect v j =
      if j ∈ evalDisposableRegisters then 0
      else if j = 20 then (signedEvalStep deriv (v 18) (v 17) (v 19, v 20) (c, e)).2
      else if j = 19 then (signedEvalStep deriv (v 18) (v 17) (v 19, v 20) (c, e)).1
      else if j = 16 then packedInput (encITerms ls) else v j := by
  let w := parseTerm70.effect (binaryEvalProbe.effect v)
  have hc : binaryEvalProbe.effect v 16 = packedInput (encITerms ((c, e) :: ls)) :=
    (binaryEvalProbe_cursor v).trans hs
  obtain ⟨hcursor, hmag, hexp, hsign, hkeep⟩ := parseTerm70_spec _ c e ls hc
  have hpersistent (i : Fin 70) (hi : 17 ≤ i.val ∧ i.val ≤ 22) : w i = v i := by
    exact (hkeep i (Or.inl hi)).trans (binaryEvalProbe_high v i (by omega))
  have hm' : 0 < w 17 := by rw [hpersistent 17 (by norm_num)]; exact hm
  have hp' : w 19 < w 17 := by
    rw [hpersistent 19 (by norm_num), hpersistent 17 (by norm_num)]; exact hp
  have hn' : w 20 < w 17 := by
    rw [hpersistent 20 (by norm_num), hpersistent 17 (by norm_num)]; exact hn
  have hpos : evalTermStepPos deriv w =
      (signedEvalStep deriv (v 18) (v 17) (v 19, v 20) (c, e)).1 := by
    unfold evalTermStepPos
    rw [show w 26 = c.natAbs from hmag, show w 27 = e from hexp,
      show w 28 = (if c < 0 then 1 else 0) from hsign,
      hpersistent 17 (by norm_num), hpersistent 18 (by norm_num), hpersistent 19 (by norm_num)]
    by_cases h : c < 0 <;> simp [signedEvalStep, h]
  have hneg : evalTermStepNeg deriv w =
      (signedEvalStep deriv (v 18) (v 17) (v 19, v 20) (c, e)).2 := by
    unfold evalTermStepNeg
    rw [show w 26 = c.natAbs from hmag, show w 27 = e from hexp,
      show w 28 = (if c < 0 then 1 else 0) from hsign,
      hpersistent 17 (by norm_num), hpersistent 18 (by norm_num), hpersistent 20 (by norm_num)]
    by_cases h : c < 0 <;> simp [signedEvalStep, h]
  rw [binarySparseEvalBody_cons deriv v c e ls hs]
  change (binaryEvalTermStep deriv).effect w j = _
  rw [binaryEvalTermStep_effect deriv w hm' hp' hn' j, hpos, hneg]
  by_cases hdis : j ∈ evalDisposableRegisters
  · simp [hdis]
  · by_cases hj20 : j = 20
    · simp [hdis, hj20]
    · by_cases hj19 : j = 19
      · simp [hdis, hj19]
      · simp only [hdis, hj20, hj19, ↓reduceIte]
        by_cases hj16 : j = 16
        · simpa [hj16] using hcursor
        · rw [ite_eq_right hj16]
          have hframe : (17 ≤ j.val ∧ j.val ≤ 22) ∨ 32 ≤ j.val := by
            simp only [evalDisposableRegisters, List.mem_cons, List.mem_singleton,
              Fin.ext_iff] at hdis
            have hval16 : j.val ≠ 16 := fun h ↦ hj16 (Fin.ext h)
            omega
          exact (hkeep j hframe).trans (binaryEvalProbe_high v j (by omega))

end SparseIrred.UpperBounds.Machine
