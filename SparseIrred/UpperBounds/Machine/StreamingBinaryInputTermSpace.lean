import SparseIrred.UpperBounds.Machine.StreamingBinaryInputTerm
import SparseIrred.UpperBounds.Machine.StreamingBinaryInputFrameLoopSpace
import SparseIrred.UpperBounds.Machine.StreamingBinaryUnpackSpace

/-! # Linear binary-width workspace for complete sparse-term parsing -/
namespace SparseIrred.UpperBounds.Machine
open Complexity BinaryRoutine SparseDiv SparseDiv.Appendix SparseDiv.StringArith

@[simp] theorem parseCopy_values_le (src dst : Fin 70) (v : BinaryValues 70) (W : ℕ)
    (hv : ∀ i, v i ≤ W) (i : Fin 70) : (parseCopy src dst).effect v i ≤ W := by
  have h := values_update_le 15 hv (Nat.zero_le W)
  exact values_update_le dst h (h src) i

theorem parseCopy_space (src dst : Fin 70) {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (hv : ∀ j i, v j i ≤ W j) : SpaceBoundByWidthAt (parseCopy src dst) S v W := by
  apply SpaceBoundByWidthAt.seq
  · exact SpaceBoundByWidthAt.clear _ (fun j ↦ hv j _)
  · apply SpaceBoundByWidthAt.binaryCopy
    · intro j; exact values_update_le 15 (hv j) (Nat.zero_le _) src
    · intro j; exact values_update_le 15 (hv j) (Nat.zero_le _) dst

theorem parseJoin_values_le (v : BinaryValues 70) (W : ℕ)
    (hv : ∀ i, v i ≤ W) (i : Fin 70) : parseJoin.effect v i ≤ 2 * W := by
  rw [parseJoin_effect]
  exact values_update_le 6 (values_update_le 15 (fun z ↦ (hv z).trans (by omega))
    (Nat.zero_le _)) (by have := hv 6; have := hv 7; omega) i

theorem parseJoin_space {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (hv : ∀ j i, v j i ≤ W j) :
    SpaceBoundByWidthAt parseJoin S v (fun j ↦ 2 * W j) := by
  apply SpaceBoundByWidthAt.seq
  · exact (SpaceBoundByWidthAt.clear 15 (fun j ↦ hv j 15)).mono (by intro j; omega)
  · apply SpaceBoundByWidthAt.add
    · intro j; simp [clear]; have := hv j 7; omega
    · intro j; simp [clear]; have := hv j 6; have := hv j 7; omega

theorem unpackInput_values_le (v : BinaryValues 70) (x : List Bool) (W : ℕ)
    (hsource : v 0 = packedInput x) (hv : ∀ j, v j ≤ W) (j : Fin 70) :
    unpackInput.effect v j ≤ W := by
  have hW : packedInput x ≤ W := hsource ▸ hv 0
  have h := unpackTraceValues_le x (packedInput x) W (fun i ↦ v (i.natAdd 11)) le_rfl hW
    (fun i ↦ hv _) j
  have hlen := packedInput_ge_length x
  rw [unpackInput_effect v x hsource]
  simpa [unpackTraceValues, List.drop_eq_nil_of_le (by omega : x.length ≤ packedInput x),
    List.take_of_length_le (by omega : x.length ≤ packedInput x),
    Nat.min_eq_right (by omega : x.length ≤ packedInput x)] using h

theorem parseTermOuter_values_le (v : BinaryValues 70) (a b : List Bool) (W : ℕ)
    (hinput : v 16 = packedInput (pair a b)) (hv : ∀ i, v i ≤ W) (i : Fin 70) :
    parseTermOuter.effect v i ≤ 4 * W := by
  have hv1 := parseCopy_values_le 16 0 v W hv
  have h1 : (parseCopy 16 0).effect v 0 = packedInput (pair a b) := by simp [hinput]
  have hv2 := frameInput_values_le (k := 57) _ W a b h1 hv1
  have hv3 := parseCopy_values_le 0 16 _ _ hv2
  have hv4 := parseJoin_values_le _ _ hv3
  have hv5 := parseCopy_values_le 6 0 _ _ hv4 i
  simpa only [parseTermOuter, seq, show 2 * (2 * W) = 4 * W by omega] using hv5

theorem parseTermOuter_space {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (a b : ℕ → List Bool) (hinput : ∀ j, v j 16 = packedInput (pair (a j) (b j)))
    (hv : ∀ j i, v j i ≤ W j) : SpaceBoundByWidthAt parseTermOuter S v W := by
  let v1 := fun j ↦ (parseCopy 16 0).effect (v j)
  let v2 := fun j ↦ (frameInput 57).effect (v1 j)
  let v3 := fun j ↦ (parseCopy 0 16).effect (v2 j)
  let v4 := fun j ↦ parseJoin.effect (v3 j)
  have hv1 := fun j ↦ parseCopy_values_le 16 0 (v j) (W j) (hv j)
  have h1 : ∀ j, v1 j 0 = packedInput (pair (a j) (b j)) := by intro j; simp [v1, hinput j]
  have hv2 := fun j ↦ frameInput_values_le (k := 57) _ _ (a j) (b j) (h1 j) (hv1 j)
  have hv3 := fun j ↦ parseCopy_values_le 0 16 _ _ (hv2 j)
  have hv4 := fun j ↦ parseJoin_values_le _ _ (hv3 j)
  apply spaceWidth_mul_add 4
  apply SpaceBoundByWidthAt.seq
  · exact (parseCopy_space _ _ hv).mono (by intro j; omega)
  · apply SpaceBoundByWidthAt.seq
    · exact (frameInput_space (k := 57) a b h1 hv1).mono (by intro j; omega)
    · apply SpaceBoundByWidthAt.seq
      · exact (parseCopy_space _ _ hv2).mono (by intro j; omega)
      · apply SpaceBoundByWidthAt.seq
        · exact (parseJoin_space hv3).mono (by intro j; omega)
        · exact (parseCopy_space _ _ hv4).mono (by intro j; omega)

theorem parseTermCoefficient_values_le (v : BinaryValues 70) (a b : List Bool) (W : ℕ)
    (hinput : v 0 = packedInput (pair a b)) (hv : ∀ i, v i ≤ W) (i : Fin 70) :
    parseTermCoefficient.effect v i ≤ 4 * W := by
  have hv1 := frameInput_values_le (k := 57) v W a b hinput hv
  have hv2 := parseJoin_values_le _ _ hv1
  have hv3 := parseCopy_values_le 6 29 _ _ hv2
  have h3 : (parseCopy 6 29).effect (parseJoin.effect ((frameInput 57).effect v)) 0 =
      packedInput b := by simp [(frame70_spec v a b hinput).1]
  have hv4 := unpackInput_values_le _ b _ h3 hv3
  have hv5 := parseCopy_values_le 5 27 _ _ hv4
  have hv6 := parseCopy_values_le 29 0 _ _ hv5 i
  simpa only [parseTermCoefficient, seq, show 2 * (2 * W) = 4 * W by omega] using hv6

theorem parseTermCoefficient_space {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (a b : ℕ → List Bool) (hinput : ∀ j, v j 0 = packedInput (pair (a j) (b j)))
    (hv : ∀ j i, v j i ≤ W j) : SpaceBoundByWidthAt parseTermCoefficient S v W := by
  have hv1 := fun j ↦ frameInput_values_le (k := 57) (v j) (W j) (a j) (b j) (hinput j) (hv j)
  have hv2 := fun j ↦ parseJoin_values_le _ _ (hv1 j)
  have hv3 := fun j ↦ parseCopy_values_le 6 29 _ _ (hv2 j)
  have h3 : ∀ j, (parseCopy 6 29).effect (parseJoin.effect ((frameInput 57).effect (v j))) 0 =
      packedInput (b j) := by intro j; simp [(frame70_spec (v j) (a j) (b j) (hinput j)).1]
  have hv4 := fun j ↦ unpackInput_values_le _ (b j) _ (h3 j) (hv3 j)
  have hv5 := fun j ↦ parseCopy_values_le 5 27 _ _ (hv4 j)
  apply spaceWidth_mul_add 8
  apply SpaceBoundByWidthAt.seq
  · exact (frameInput_space (k := 57) a b hinput hv).mono (by intro j; omega)
  · apply SpaceBoundByWidthAt.seq
    · exact (parseJoin_space hv1).mono (by intro j; omega)
    · apply SpaceBoundByWidthAt.seq
      · exact (parseCopy_space _ _ hv2).mono (by intro j; omega)
      · apply SpaceBoundByWidthAt.seq
        · exact (unpackInput_space b _ S _ h3 hv3).mono (by intro j; omega)
        · apply SpaceBoundByWidthAt.seq
          · exact (parseCopy_space _ _ hv4).mono (by intro j; omega)
          · exact (parseCopy_space _ _ hv5).mono (by intro j; omega)

theorem parseTermSignMagnitude_values_le (v : BinaryValues 70) (a b : List Bool) (W : ℕ)
    (hinput : v 0 = packedInput (pair a b)) (hv : ∀ i, v i ≤ W) (i : Fin 70) :
    parseTermSignMagnitude.effect v i ≤ 2 * W := by
  have hv1 := frameInput_values_le (k := 57) v W a b hinput hv
  have hv2 := parseCopy_values_le 6 28 _ _ hv1
  have h2 : (parseCopy 6 28).effect ((frameInput 57).effect v) 0 = packedInput b := by
    simp [(frame70_spec v a b hinput).1]
  have hv3 := unpackInput_values_le _ b _ h2 hv2
  exact parseCopy_values_le 5 26 _ _ hv3 i

theorem parseTermSignMagnitude_space {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (a b : ℕ → List Bool) (hinput : ∀ j, v j 0 = packedInput (pair (a j) (b j)))
    (hv : ∀ j i, v j i ≤ W j) : SpaceBoundByWidthAt parseTermSignMagnitude S v W := by
  have hv1 := fun j ↦ frameInput_values_le (k := 57) (v j) (W j) (a j) (b j) (hinput j) (hv j)
  have hv2 := fun j ↦ parseCopy_values_le 6 28 _ _ (hv1 j)
  have h2 : ∀ j, (parseCopy 6 28).effect ((frameInput 57).effect (v j)) 0 = packedInput (b j) := by
    intro j; simp [(frame70_spec (v j) (a j) (b j) (hinput j)).1]
  have hv3 := fun j ↦ unpackInput_values_le _ (b j) _ (h2 j) (hv2 j)
  apply spaceWidth_mul_add 4
  apply SpaceBoundByWidthAt.seq
  · exact (frameInput_space (k := 57) a b hinput hv).mono (by intro j; omega)
  · apply SpaceBoundByWidthAt.seq
    · exact (parseCopy_space _ _ hv1).mono (by intro j; omega)
    · apply SpaceBoundByWidthAt.seq
      · exact (unpackInput_space b _ S _ h2 hv2).mono (by intro j; omega)
      · exact (parseCopy_space _ _ hv3).mono (by intro j; omega)

/-- Every register remains within a fixed numeric multiple of the incoming envelope. -/
theorem parseTerm70_values_le (v : BinaryValues 70) (c : ℤ) (e : ℕ) (ls : ITerms) (W : ℕ)
    (h16 : v 16 = packedInput (encITerms ((c, e) :: ls)))
    (hv : ∀ i, v i ≤ W) (i : Fin 70) : parseTerm70.effect v i ≤ 32 * W := by
  have houter : v 16 = packedInput (pair (encITerm (c, e)) (encITerms ls)) := by
    simpa only [encITerms, List.map_cons, frame_cons, pair] using h16
  have hv1 := parseTermOuter_values_le v _ _ W houter hv
  have h1 : parseTermOuter.effect v 0 = packedInput (pair (encInt c) (encNat e)) := by
    simpa only [encITerm] using (parseTermOuter_spec v _ _ houter).2.1
  have hv2 := parseTermCoefficient_values_le _ _ _ _ h1 hv1
  have h2 : parseTermCoefficient.effect (parseTermOuter.effect v) 0 =
      packedInput (pair [decide (c < 0)] (encNat c.natAbs)) := by
    simpa only [encInt] using (parseTermCoefficient_spec _ _ _ h1).2.1
  have hv3 := parseTermSignMagnitude_values_le _ _ _ _ h2 hv2
  have h := (clearRegisters_effect_le [23, 24, 25, 29, 30, 31]
    (parseTermSignMagnitude.effect (parseTermCoefficient.effect (parseTermOuter.effect v))) i).trans (hv3 i)
  simpa only [parseTerm70, seq, show 2 * (4 * (4 * W)) = 32 * W by omega] using h

/-- The complete parser has an all-prefix auxiliary-space bound linear in
binary register width, even though its loops may take exponential time. -/
theorem parseTerm70_space (c : ℕ → ℤ) (e : ℕ → ℕ) (ls : ℕ → ITerms)
    {S W : ℕ → ℕ} {v : ℕ → BinaryValues 70}
    (h16 : ∀ j, v j 16 = packedInput (encITerms ((c j, e j) :: ls j)))
    (hv : ∀ j i, v j i ≤ W j) : SpaceBoundByWidthAt parseTerm70 S v W := by
  have houter : ∀ j, v j 16 = packedInput (pair (encITerm (c j, e j)) (encITerms (ls j))) := by
    intro j; simpa only [encITerms, List.map_cons, frame_cons, pair] using h16 j
  have hv1 := fun j ↦ parseTermOuter_values_le (v j) _ _ (W j) (houter j) (hv j)
  have h1 : ∀ j, parseTermOuter.effect (v j) 0 =
      packedInput (pair (encInt (c j)) (encNat (e j))) := by
    intro j; simpa only [encITerm] using (parseTermOuter_spec (v j) _ _ (houter j)).2.1
  have hv2 := fun j ↦ parseTermCoefficient_values_le _ _ _ _ (h1 j) (hv1 j)
  have h2 : ∀ j, parseTermCoefficient.effect (parseTermOuter.effect (v j)) 0 =
      packedInput (pair [decide (c j < 0)] (encNat (c j).natAbs)) := by
    intro j; simpa only [encInt] using (parseTermCoefficient_spec _ _ _ (h1 j)).2.1
  have hv3 := fun j ↦ parseTermSignMagnitude_values_le _ _ _ _ (h2 j) (hv2 j)
  apply SpaceBoundByWidthAt.seq
  · exact parseTermOuter_space _ _ houter hv
  · apply SpaceBoundByWidthAt.seq
    · apply spaceWidth_mul_add 4
      exact (parseTermCoefficient_space _ _ h1 hv1).mono (by intro j; omega)
    · apply SpaceBoundByWidthAt.seq
      · apply spaceWidth_mul_add 16
        exact (parseTermSignMagnitude_space _ _ h2 hv2).mono (by intro j; omega)
      · apply spaceWidth_mul_add 32
        exact (clearRegisters_space _ hv3).mono (by intro j; omega)

end SparseIrred.UpperBounds.Machine
