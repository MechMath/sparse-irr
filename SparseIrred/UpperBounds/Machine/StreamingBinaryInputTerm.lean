import SparseIrred.UpperBounds.Machine.StreamingBinaryInputFrameSilent
import SparseIrred.UpperBounds.Machine.StreamingBinaryUnpack
import SparseDivComplexity.Appendix.IntTermsString

/-! # Actual fixed-register extraction of one encoded sparse integer term -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace SparseIrred.UpperBounds.Machine
open Complexity BinaryRoutine SparseDiv SparseDiv.Appendix SparseDiv.StringArith

/-- Scratch-safe preserved-source copy. Register 15 belongs to the parser. -/
def parseCopy (src dst : Fin 70) : BinaryRoutine 70 :=
  seq (clear 15) (binaryCopy src dst 15)

def parseJoin : BinaryRoutine 70 := seq (clear 15) (add 7 6 15)

def parseTermOuter : BinaryRoutine 70 :=
  seq (parseCopy 16 0) (seq (frameInput 57) (seq (parseCopy 0 16)
    (seq parseJoin (parseCopy 6 0))))

def parseTermCoefficient : BinaryRoutine 70 :=
  seq (frameInput 57) (seq parseJoin (seq (parseCopy 6 29)
    (seq unpackInput (seq (parseCopy 5 27) (parseCopy 29 0)))))

def parseTermSignMagnitude : BinaryRoutine 70 :=
  seq (frameInput 57) (seq (parseCopy 6 28)
    (seq unpackInput (parseCopy 5 26)))

def parseTerm70 : BinaryRoutine 70 :=
  seq parseTermOuter (seq parseTermCoefficient (seq parseTermSignMagnitude
    (clearRegisters [23, 24, 25, 29, 30, 31])))

theorem parseCopy_sound (src dst : Fin 70) : (parseCopy src dst).Sound :=
  (clear_sound _).seq (binaryCopy_sound _ _ _)

theorem parseJoin_sound : parseJoin.Sound := (clear_sound _).seq (add_sound _ _ _)

theorem parseTermOuter_sound : parseTermOuter.Sound :=
  (parseCopy_sound _ _).seq ((frameInput_sound _).seq ((parseCopy_sound _ _).seq
    (parseJoin_sound.seq (parseCopy_sound _ _))))

theorem parseTermCoefficient_sound : parseTermCoefficient.Sound :=
  (frameInput_sound _).seq (parseJoin_sound.seq ((parseCopy_sound _ _).seq
    (unpackInput_sound.seq ((parseCopy_sound _ _).seq (parseCopy_sound _ _)))))

theorem parseTermSignMagnitude_sound : parseTermSignMagnitude.Sound :=
  (frameInput_sound _).seq ((parseCopy_sound _ _).seq (unpackInput_sound.seq (parseCopy_sound _ _)))

theorem parseTerm70_sound : parseTerm70.Sound :=
  parseTermOuter_sound.seq (parseTermCoefficient_sound.seq (parseTermSignMagnitude_sound.seq
    (clearRegisters_sound _)))

theorem parseCopy_requires (src dst : Fin 70) (v : BinaryValues 70)
    (h1 : src ≠ dst) (h2 : src ≠ 15) (h3 : dst ≠ 15) : (parseCopy src dst).requires v := by
  simp [parseCopy, seq, clear, binaryCopy, h1, h2, h3]

@[simp] theorem parseCopy_effect (src dst : Fin 70) (v : BinaryValues 70) (hs : src ≠ 15) :
    (parseCopy src dst).effect v = Function.update (Function.update v 15 0) dst (v src) := by
  simp [parseCopy, seq, clear, binaryCopy, hs]

@[simp] theorem parseJoin_requires (v : BinaryValues 70) : parseJoin.requires v := by
  simp [parseJoin, seq, clear, add]

@[simp] theorem parseJoin_effect (v : BinaryValues 70) :
    parseJoin.effect v = Function.update (Function.update v 15 0) 6 (v 6 + v 7) := by
  simp [parseJoin, seq, clear, add]

theorem packedInput_eq_value_add_power (x : List Bool) :
    packedInput x = decNat x + 2 ^ x.length := by
  simp [packedInput, decNat_append, decNat_cons]

/-- Simple fixed-index projections of the frame-reader effect. -/
theorem frame70_spec (v : BinaryValues 70) (a b : List Bool) (h : v 0 = packedInput (pair a b)) :
    (frameInput 57).effect v 0 = packedInput b ∧
      (frameInput 57).effect v 6 = decNat a ∧
      (frameInput 57).effect v 7 = 2 ^ a.length ∧
      ∀ j : Fin 70, 13 ≤ j.val → (frameInput 57).effect v j = v j := by
  rw [frameInput_effect (k := 57) v a b h]
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro j hj
  let q : Fin 57 := ⟨j.val - 13, by omega⟩
  have hq : (q.natAdd 8).natAdd 5 = j := by apply Fin.ext; simp [q]; omega
  rw [← hq, frameInputValues_extra]

/-- The numeric decoder preserves every parser/caller register beyond its workspace. -/
theorem unpack70_spec (v : BinaryValues 70) (x : List Bool) (h : v 0 = packedInput x) :
    unpackInput.effect v 5 = decNat x ∧
      ∀ j : Fin 70, 11 ≤ j.val → unpackInput.effect v j = v j := by
  rw [unpackInput_effect v x h]
  refine ⟨rfl, ?_⟩
  intro j hj
  let q : Fin 59 := ⟨j.val - 11, by omega⟩
  have hq : q.natAdd 11 = j := by apply Fin.ext; simp [q]; omega
  rw [← hq]
  simp [unpackValues]

theorem parseTermOuter_spec (v : BinaryValues 70) (a b : List Bool)
    (h : v 16 = packedInput (pair a b)) :
    parseTermOuter.requires v ∧
      parseTermOuter.effect v 0 = packedInput a ∧
      parseTermOuter.effect v 16 = packedInput b ∧
      ∀ j : Fin 70, 17 ≤ j.val → parseTermOuter.effect v j = v j := by
  let v1 := (parseCopy 16 0).effect v
  let v2 := (frameInput 57).effect v1
  let v3 := (parseCopy 0 16).effect v2
  let v4 := parseJoin.effect v3
  let v5 := (parseCopy 6 0).effect v4
  have h1 : v1 0 = packedInput (pair a b) := by simp [v1, h]
  have h2 : v2 0 = packedInput b ∧ v2 6 = decNat a ∧ v2 7 = 2 ^ a.length ∧
      ∀ j : Fin 70, 13 ≤ j.val → v2 j = v1 j := frame70_spec v1 a b h1
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨parseCopy_requires _ _ _ (by decide) (by decide) (by decide),
      frameInput_requires (k := 57) v1 a b h1,
      parseCopy_requires _ _ _ (by decide) (by decide) (by decide),
      parseJoin_requires _, parseCopy_requires _ _ _ (by decide) (by decide) (by decide)⟩
  · change v5 0 = _
    simp only [v5, v4, v3, parseCopy_effect, Fin.reduceEq, parseJoin_effect,
      Function.update_self]
    simp [h2.2.1, h2.2.2.1, ← packedInput_eq_value_add_power]
  · change v5 16 = _
    simp [v5, v4, v3, h2.1]
  · intro j hj
    change v5 j = _
    have hj0 : j ≠ 0 := by intro he; rw [he] at hj; norm_num at hj
    have hj6 : j ≠ 6 := by intro he; rw [he] at hj; norm_num at hj
    have hj15 : j ≠ 15 := by intro he; rw [he] at hj; norm_num at hj
    have hj16 : j ≠ 16 := by intro he; rw [he] at hj; norm_num at hj
    have hkeep : v2 j = v j := (h2.2.2.2 j (by omega)).trans (by simp [v1, hj0, hj15])
    simpa [v5, v4, v3, hj0, hj6, hj15, hj16] using hkeep


theorem parseTermCoefficient_spec (v : BinaryValues 70) (a b : List Bool)
    (h : v 0 = packedInput (pair a b)) :
    parseTermCoefficient.requires v ∧
      parseTermCoefficient.effect v 0 = packedInput a ∧
      parseTermCoefficient.effect v 27 = decNat b ∧
      ∀ j : Fin 70, 13 ≤ j.val → j ≠ 15 → j ≠ 27 → j ≠ 29 →
        parseTermCoefficient.effect v j = v j := by
  let v1 := (frameInput 57).effect v
  let v2 := parseJoin.effect v1
  let v3 := (parseCopy 6 29).effect v2
  let v4 := unpackInput.effect v3
  let v5 := (parseCopy 5 27).effect v4
  let v6 := (parseCopy 29 0).effect v5
  have h1 : v1 0 = packedInput b ∧ v1 6 = decNat a ∧ v1 7 = 2 ^ a.length ∧
      ∀ j : Fin 70, 13 ≤ j.val → v1 j = v j := frame70_spec v a b h
  have h3 : v3 0 = packedInput b := by simp [v3, v2, h1.1]
  have h4 : v4 5 = decNat b ∧ ∀ j : Fin 70, 11 ≤ j.val → v4 j = v3 j :=
    unpack70_spec v3 b h3
  have h29 : v3 29 = packedInput a := by
    simp [v3, v2, h1.2.1, h1.2.2.1, ← packedInput_eq_value_add_power]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨frameInput_requires (k := 57) v a b h, parseJoin_requires _,
      parseCopy_requires _ _ _ (by decide) (by decide) (by decide),
      unpackInput_requires v3 b h3,
      parseCopy_requires _ _ _ (by decide) (by decide) (by decide),
      parseCopy_requires _ _ _ (by decide) (by decide) (by decide)⟩
  · change v6 0 = _
    simp [v6, v5, show v4 29 = v3 29 from h4.2 29 (by decide), h29]
  · change v6 27 = _
    simp [v6, v5, h4.1]
  · intro j hj hj15 hj27 hj29
    change v6 j = _
    have hj0 : j ≠ 0 := by intro he; rw [he] at hj; norm_num at hj
    have hj6 : j ≠ 6 := by intro he; rw [he] at hj; norm_num at hj
    have hkeep : v4 j = v j := (h4.2 j (by omega)).trans (by
      simpa [v3, v2, hj29, hj15, hj6] using h1.2.2.2 j hj)
    simpa [v6, v5, hj0, hj15, hj27] using hkeep


theorem parseTermSignMagnitude_spec (v : BinaryValues 70) (a b : List Bool)
    (h : v 0 = packedInput (pair a b)) :
    parseTermSignMagnitude.requires v ∧
      parseTermSignMagnitude.effect v 26 = decNat b ∧
      parseTermSignMagnitude.effect v 28 = decNat a ∧
      ∀ j : Fin 70, 13 ≤ j.val → j ≠ 15 → j ≠ 26 → j ≠ 28 →
        parseTermSignMagnitude.effect v j = v j := by
  let v1 := (frameInput 57).effect v
  let v2 := (parseCopy 6 28).effect v1
  let v3 := unpackInput.effect v2
  let v4 := (parseCopy 5 26).effect v3
  have h1 : v1 0 = packedInput b ∧ v1 6 = decNat a ∧ v1 7 = 2 ^ a.length ∧
      ∀ j : Fin 70, 13 ≤ j.val → v1 j = v j := frame70_spec v a b h
  have h2 : v2 0 = packedInput b := by simp [v2, h1.1]
  have h3 : v3 5 = decNat b ∧ ∀ j : Fin 70, 11 ≤ j.val → v3 j = v2 j :=
    unpack70_spec v2 b h2
  have h28 : v2 28 = decNat a := by simp [v2, h1.2.1]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨frameInput_requires (k := 57) v a b h,
      parseCopy_requires _ _ _ (by decide) (by decide) (by decide),
      unpackInput_requires v2 b h2,
      parseCopy_requires _ _ _ (by decide) (by decide) (by decide)⟩
  · change v4 26 = _
    simp [v4, h3.1]
  · change v4 28 = _
    simp [v4, show v3 28 = v2 28 from h3.2 28 (by decide), h28]
  · intro j hj hj15 hj26 hj28
    change v4 j = _
    have hkeep : v3 j = v j := (h3.2 j (by omega)).trans (by
      simpa [v2, hj28, hj15] using h1.2.2.2 j hj)
    simpa [v4, hj26, hj15] using hkeep


private theorem parseTerm70_correct (v : BinaryValues 70) (c : ℤ) (e : ℕ) (ls : ITerms)
    (h16 : v 16 = packedInput (encITerms ((c, e) :: ls))) :
    parseTerm70.requires v ∧
      parseTerm70.effect v 16 = packedInput (encITerms ls) ∧
      parseTerm70.effect v 26 = c.natAbs ∧
      parseTerm70.effect v 27 = e ∧
      parseTerm70.effect v 28 = (if c < 0 then 1 else 0) ∧
      ∀ j : Fin 70, (17 ≤ j.val ∧ j.val ≤ 22) ∨ 32 ≤ j.val →
        parseTerm70.effect v j = v j := by
  let v1 := parseTermOuter.effect v
  let v2 := parseTermCoefficient.effect v1
  let v3 := parseTermSignMagnitude.effect v2
  let v4 := (clearRegisters [23, 24, 25, 29, 30, 31]).effect v3
  have houter := parseTermOuter_spec v (encITerm (c, e)) (encITerms ls) (by
    simpa only [encITerms, List.map_cons, frame_cons, pair] using h16)
  have hcoeff := parseTermCoefficient_spec v1 (encInt c) (encNat e) (by
    simpa only [encITerm] using houter.2.1)
  have hsign := parseTermSignMagnitude_spec v2 [decide (c < 0)] (encNat c.natAbs)
    (by simpa only [encInt] using hcoeff.2.1)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨houter.1, hcoeff.1, hsign.1, clearRegisters_requires _ _⟩
  · change v4 16 = _
    dsimp only [v4]
    rw [clearRegisters_effect]
    simp only [List.mem_cons, List.mem_singleton, Fin.reduceEq, or_self, ↓reduceIte]
    exact (hsign.2.2.2 16 (by decide) (by decide) (by decide) (by decide)).trans
      ((hcoeff.2.2.2 16 (by decide) (by decide) (by decide) (by decide)).trans houter.2.2.1)
  · change v4 26 = _
    dsimp only [v4]
    rw [clearRegisters_effect]
    simpa using hsign.2.1
  · change v4 27 = _
    dsimp only [v4]
    rw [clearRegisters_effect]
    simp only [List.mem_cons, List.mem_singleton, Fin.reduceEq, or_self, ↓reduceIte]
    exact (hsign.2.2.2 27 (by decide) (by decide) (by decide) (by decide)).trans
      (by simpa using hcoeff.2.2.1)
  · change v4 28 = _
    dsimp only [v4]
    rw [clearRegisters_effect]
    simpa [decNat_cons] using hsign.2.2.1
  · intro j hj
    have hj13 : 13 ≤ j.val := by omega
    have hj15 : j ≠ 15 := by intro h; simp [h] at hj
    have hj26 : j ≠ 26 := by intro h; simp [h] at hj
    have hj27 : j ≠ 27 := by intro h; simp [h] at hj
    have hj28 : j ≠ 28 := by intro h; simp [h] at hj
    have hj29 : j ≠ 29 := by intro h; simp [h] at hj
    have hjclean : j ∉ ([23, 24, 25, 29, 30, 31] : List (Fin 70)) := by
      intro hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num at hj
    change v4 j = _
    dsimp only [v4]
    rw [clearRegisters_effect, if_neg hjclean]
    exact (hsign.2.2.2 j hj13 hj15 hj26 hj28).trans
      ((hcoeff.2.2.2 j hj13 hj15 hj27 hj29).trans (houter.2.2.2 j (by omega)))

/-- Every correctly framed nonempty sparse input satisfies the concrete program domain. -/
theorem parseTerm70_requires (v : BinaryValues 70) (c : ℤ) (e : ℕ) (ls : ITerms)
    (h16 : v 16 = packedInput (encITerms ((c, e) :: ls))) : parseTerm70.requires v :=
  (parseTerm70_correct v c e ls h16).1

/-- The three nested frame decoders and two numeric decoders extract exactly one term. -/
theorem parseTerm70_spec (v : BinaryValues 70) (c : ℤ) (e : ℕ) (ls : ITerms)
    (h16 : v 16 = packedInput (encITerms ((c, e) :: ls))) :
    parseTerm70.effect v 16 = packedInput (encITerms ls) ∧
      parseTerm70.effect v 26 = c.natAbs ∧
      parseTerm70.effect v 27 = e ∧
      parseTerm70.effect v 28 = (if c < 0 then 1 else 0) ∧
      ∀ j : Fin 70, (17 ≤ j.val ∧ j.val ≤ 22) ∨ 32 ≤ j.val →
        parseTerm70.effect v j = v j := (parseTerm70_correct v c e ls h16).2

theorem parseCopy_silent (src dst : Fin 70) : RoutineSilent (parseCopy src dst) :=
  (routineSilent_clear _).seq (routineSilent_copy _ _ _)

theorem parseJoin_silent : RoutineSilent parseJoin :=
  (routineSilent_clear _).seq (routineSilent_add _ _ _)

theorem parseTermOuter_silent : RoutineSilent parseTermOuter :=
  (parseCopy_silent _ _).seq ((frameInput_silent _).seq ((parseCopy_silent _ _).seq
    (parseJoin_silent.seq (parseCopy_silent _ _))))

theorem parseTermCoefficient_silent : RoutineSilent parseTermCoefficient :=
  (frameInput_silent _).seq (parseJoin_silent.seq ((parseCopy_silent _ _).seq
    (unpackInput_silent.seq ((parseCopy_silent _ _).seq (parseCopy_silent _ _)))))

theorem parseTermSignMagnitude_silent : RoutineSilent parseTermSignMagnitude :=
  (frameInput_silent _).seq ((parseCopy_silent _ _).seq
    (unpackInput_silent.seq (parseCopy_silent _ _)))

theorem parseTerm70_silent : RoutineSilent parseTerm70 :=
  parseTermOuter_silent.seq (parseTermCoefficient_silent.seq (parseTermSignMagnitude_silent.seq
    (routineSilent_clearRegisters _)))

end SparseIrred.UpperBounds.Machine
