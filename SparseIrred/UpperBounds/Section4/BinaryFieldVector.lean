import SparseIrred.UpperBounds.Section4.BinaryFieldPrime
import SparseIrred.UpperBounds.Section4.FieldBounds

/-!
# Fixed-length vectors of binary prime-field coefficients

The number of coefficients is obtained from a framed template. Every operation
rebuilds exactly that many coefficients, with each output reduced modulo the
input characteristic. This gives uniform bounds even on malformed operands.
-/

namespace SparseIrred.UpperBounds.Section4

open Complexity SparseDiv SparseDiv.StringArith SparseGcd SparseGcd.TermsStr

/-- Enumerate the template's coefficient positions as unary block addresses. -/
def vectorIndicesStr (template : List Bool) : List Bool := idxBlocks (countBlocks template)

def vectorZeroStr (template : List Bool) : List Bool := mapBlocks (fun _ ↦ []) template

def vectorRedStr (p template a : List Bool) : List Bool :=
  mapBlocks (fun i ↦ redStr (nthBlockStr i a) p) (vectorIndicesStr template)

def vectorAddStr (p template a b : List Bool) : List Bool :=
  mapBlocks (fun i ↦ primeAddStr p (nthBlockStr i a) (nthBlockStr i b))
    (vectorIndicesStr template)

def vectorScaleStr (p template c a : List Bool) : List Bool :=
  mapBlocks (fun i ↦ primeMulStr p c (nthBlockStr i a)) (vectorIndicesStr template)

def vectorNegStr (p template a : List Bool) : List Bool :=
  mapBlocks (fun i ↦ primeNegStr p (nthBlockStr i a)) (vectorIndicesStr template)

def vectorSubStr (p template a b : List Bool) : List Bool :=
  vectorAddStr p template a (vectorNegStr p template b)

theorem cobham_vectorIndicesStr_comp {n : ℕ} {t : (Fin n → List Bool) → List Bool}
    (ht : Cobham t) : Cobham fun v ↦ vectorIndicesStr (t v) :=
  cobham_idxBlocks_comp (cobham_countBlocks_comp ht)

theorem cobham_vectorZeroStr_comp {n : ℕ} {t : (Fin n → List Bool) → List Bool}
    (ht : Cobham t) : Cobham fun v ↦ vectorZeroStr (t v) :=
  TermsStr.cobham_mapBlocks_comp (F := fun _ _ ↦ []) (Cobham.const []) ht

theorem cobham_vectorRedStr_comp {n : ℕ} {p t a : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (ht : Cobham t) (ha : Cobham a) :
    Cobham fun v ↦ vectorRedStr (p v) (t v) (a v) := by
  apply TermsStr.cobham_mapBlocks_comp (F := fun i v ↦ redStr (nthBlockStr i (a v)) (p v))
    _ (cobham_vectorIndicesStr_comp ht)
  exact cobham_redStr_comp
    (TermsStr.cobham_nthBlockStr_comp (.proj 0) (TermsStr.cobham_tail_comp ha))
    (TermsStr.cobham_tail_comp hp)

theorem cobham_vectorAddStr_comp {n : ℕ} {p t a b : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (ht : Cobham t) (ha : Cobham a) (hb : Cobham b) :
    Cobham fun v ↦ vectorAddStr (p v) (t v) (a v) (b v) := by
  apply TermsStr.cobham_mapBlocks_comp
    (F := fun i v ↦ primeAddStr (p v) (nthBlockStr i (a v)) (nthBlockStr i (b v)))
    _ (cobham_vectorIndicesStr_comp ht)
  exact cobham_primeAddStr_comp (TermsStr.cobham_tail_comp hp)
    (TermsStr.cobham_nthBlockStr_comp (.proj 0) (TermsStr.cobham_tail_comp ha))
    (TermsStr.cobham_nthBlockStr_comp (.proj 0) (TermsStr.cobham_tail_comp hb))

theorem cobham_vectorScaleStr_comp {n : ℕ} {p t c a : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (ht : Cobham t) (hc : Cobham c) (ha : Cobham a) :
    Cobham fun v ↦ vectorScaleStr (p v) (t v) (c v) (a v) := by
  apply TermsStr.cobham_mapBlocks_comp
    (F := fun i v ↦ primeMulStr (p v) (c v) (nthBlockStr i (a v)))
    _ (cobham_vectorIndicesStr_comp ht)
  exact cobham_primeMulStr_comp (TermsStr.cobham_tail_comp hp) (TermsStr.cobham_tail_comp hc)
    (TermsStr.cobham_nthBlockStr_comp (.proj 0) (TermsStr.cobham_tail_comp ha))

theorem cobham_vectorNegStr_comp {n : ℕ} {p t a : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (ht : Cobham t) (ha : Cobham a) :
    Cobham fun v ↦ vectorNegStr (p v) (t v) (a v) := by
  apply TermsStr.cobham_mapBlocks_comp
    (F := fun i v ↦ primeNegStr (p v) (nthBlockStr i (a v)))
    _ (cobham_vectorIndicesStr_comp ht)
  exact cobham_primeNegStr_comp (TermsStr.cobham_tail_comp hp)
    (TermsStr.cobham_nthBlockStr_comp (.proj 0) (TermsStr.cobham_tail_comp ha))

theorem cobham_vectorSubStr_comp {n : ℕ} {p t a b : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (ht : Cobham t) (ha : Cobham a) (hb : Cobham b) :
    Cobham fun v ↦ vectorSubStr (p v) (t v) (a v) (b v) :=
  cobham_vectorAddStr_comp hp ht ha (cobham_vectorNegStr_comp hp ht hb)

theorem vectorIndicesStr_frame (ts : List (List Bool)) :
    vectorIndicesStr (frame ts) = frame ((List.range ts.length).map unaryN) := by
  rw [vectorIndicesStr, countBlocks_frame, idxBlocks_unaryN]

theorem nthBlockStr_encodeNumerals (a : List ℕ) (i : ℕ) :
    nthBlockStr (unaryN i) (encodeNumerals a) = encNat (a.getD i 0) := by
  rw [encodeNumerals, nthBlockStr_frame]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases a[i]? <;> rfl

theorem vectorZeroStr_frame (ts : List (List Bool)) :
    vectorZeroStr (frame ts) = encodeNumerals (List.replicate ts.length 0) := by
  simp [vectorZeroStr, mapBlocks_frame, encodeNumerals]
  rfl

theorem map_range_eq_ofFn {α : Type*} (d : ℕ) (f : ℕ → α) :
    (List.range d).map f = List.ofFn (fun i : Fin d ↦ f i.val) := by
  apply List.ext_getElem
  · simp
  · intros; simp

theorem vectorRedStr_spec (p : ℕ) [NeZero p] (ts : List (List Bool)) (a : List ℕ) :
    vectorRedStr (encNat p) (frame ts) (encodeNumerals a) =
      encodeNumerals (List.ofFn (fun i : Fin ts.length ↦ (a.getD i.val 0 : ZMod p).val)) := by
  rw [vectorRedStr, vectorIndicesStr_frame, mapBlocks_frame]
  simp only [List.map_map, Function.comp_def, nthBlockStr_encodeNumerals,
    redStr_eq_zmod_val, decNat_encNat]
  rw [map_range_eq_ofFn]
  simp [encodeNumerals, List.map_ofFn, Function.comp_def]

theorem vectorAddStr_spec (p : ℕ) [NeZero p] (ts : List (List Bool)) (a b : List ℕ) :
    vectorAddStr (encNat p) (frame ts) (encodeNumerals a) (encodeNumerals b) =
      encodeNumerals (List.ofFn (fun i : Fin ts.length ↦
        ((a.getD i.val 0 : ZMod p) + b.getD i.val 0).val)) := by
  rw [vectorAddStr, vectorIndicesStr_frame, mapBlocks_frame]
  simp only [List.map_map, Function.comp_def, nthBlockStr_encodeNumerals,
    primeAddStr_eq_zmod_val, decNat_encNat]
  rw [map_range_eq_ofFn]
  simp [encodeNumerals, List.map_ofFn, Function.comp_def]

theorem vectorScaleStr_spec (p : ℕ) [NeZero p] (ts : List (List Bool))
    (c : ℕ) (a : List ℕ) :
    vectorScaleStr (encNat p) (frame ts) (encNat c) (encodeNumerals a) =
      encodeNumerals (List.ofFn (fun i : Fin ts.length ↦
        ((c : ZMod p) * a.getD i.val 0).val)) := by
  rw [vectorScaleStr, vectorIndicesStr_frame, mapBlocks_frame]
  simp only [List.map_map, Function.comp_def, nthBlockStr_encodeNumerals,
    primeMulStr_eq_zmod_val, decNat_encNat]
  rw [map_range_eq_ofFn]
  simp [encodeNumerals, List.map_ofFn, Function.comp_def]

theorem vectorNegStr_spec (p : ℕ) [NeZero p] (ts : List (List Bool)) (a : List ℕ) :
    vectorNegStr (encNat p) (frame ts) (encodeNumerals a) =
      encodeNumerals (List.ofFn (fun i : Fin ts.length ↦ (-(a.getD i.val 0 : ZMod p)).val)) := by
  rw [vectorNegStr, vectorIndicesStr_frame, mapBlocks_frame]
  simp only [List.map_map, Function.comp_def, nthBlockStr_encodeNumerals,
    primeNegStr_eq_zmod_val, decNat_encNat]
  rw [map_range_eq_ofFn]
  simp [encodeNumerals, List.map_ofFn, Function.comp_def]

theorem vectorIndicesStr_eq (t : List Bool) :
    vectorIndicesStr t = frame ((List.range (blocks t).length).map unaryN) := by
  have hc : countBlocks t = countBlocks (frame (blocks t)) := by
    simp [countBlocks, foldBlocks, blocks_frame]
  rw [vectorIndicesStr, hc, countBlocks_frame, idxBlocks_unaryN]

theorem framed_map_length_le (xs : List (List Bool)) (f : List Bool → List Bool) (w : ℕ)
    (hf : ∀ x ∈ xs, (f x).length ≤ w) : (frame (xs.map f)).length ≤ (2 * w + 2) * xs.length := by
  induction xs with
  | nil => simp [frame_nil]
  | cons a xs ih =>
      have ha := hf a (by simp)
      have hi := ih (fun b hb ↦ hf b (by simp [hb]))
      simp only [List.map_cons, frame_cons, List.length_append, delimit_length, List.length_cons]
      nlinarith

/-- Uniform output bound: independent of the size of either operand. -/
theorem vectorAddStr_length (p t a b : List Bool) :
    (vectorAddStr p t a b).length ≤ (2 * p.length + 2) * (blocks t).length := by
  rw [vectorAddStr, vectorIndicesStr_eq, mapBlocks_frame]
  simpa only [List.length_map, List.length_range] using
    framed_map_length_le ((List.range (blocks t).length).map unaryN) _ p.length
      (fun i _ ↦ primeAddStr_length p _ _)

theorem vectorScaleStr_length (p t c a : List Bool) :
    (vectorScaleStr p t c a).length ≤ (2 * p.length + 2) * (blocks t).length := by
  rw [vectorScaleStr, vectorIndicesStr_eq, mapBlocks_frame]
  simpa only [List.length_map, List.length_range] using
    framed_map_length_le ((List.range (blocks t).length).map unaryN) _ p.length
      (fun i _ ↦ primeMulStr_length p _ _)

theorem vectorNegStr_length (p t a : List Bool) :
    (vectorNegStr p t a).length ≤ (2 * p.length + 2) * (blocks t).length := by
  rw [vectorNegStr, vectorIndicesStr_eq, mapBlocks_frame]
  simpa only [List.length_map, List.length_range] using
    framed_map_length_le ((List.range (blocks t).length).map unaryN) _ p.length
      (fun i _ ↦ primeNegStr_length p _)

theorem vectorRedStr_length (p t a : List Bool) :
    (vectorRedStr p t a).length ≤ (2 * p.length + 2) * (blocks t).length := by
  rw [vectorRedStr, vectorIndicesStr_eq, mapBlocks_frame]
  simpa only [List.length_map, List.length_range] using
    framed_map_length_le ((List.range (blocks t).length).map unaryN) _ p.length
      (fun i _ ↦ length_redStr_le _ _)

theorem vectorAddStr_encoded (c : FieldCode) [Fact c.Valid] (ts : List (List Bool))
    (ht : ts.length = c.degree) (x y : c.Carrier) :
    vectorAddStr (encNat c.characteristic) (frame ts)
        (encodeNumerals (c.encodeElement x)) (encodeNumerals (c.encodeElement y)) =
      encodeNumerals (c.encodeElement (x + y)) := by
  rw [vectorAddStr_spec]
  congr 1
  apply List.ext_getElem
  · simp [FieldCode.encodeElement, ht]
  · intro i hi hj
    have hi' : i < c.degree := by simpa [FieldCode.encodeElement] using hj
    simp [FieldCode.encodeElement, List.getElem_ofFn, hi', ht]

theorem vectorRedStr_encoded (c : FieldCode) [Fact c.Valid] (ts : List (List Bool))
    (ht : ts.length = c.degree) (x : c.Carrier) :
    vectorRedStr (encNat c.characteristic) (frame ts)
        (encodeNumerals (c.encodeElement x)) = encodeNumerals (c.encodeElement x) := by
  rw [vectorRedStr_spec]
  congr 1
  apply List.ext_getElem
  · simp [FieldCode.encodeElement, ht]
  · intro i hi hj
    have hi' : i < c.degree := by simpa [FieldCode.encodeElement] using hj
    simp [FieldCode.encodeElement, List.getElem_ofFn, hi', ht]

theorem vectorNegStr_encoded (c : FieldCode) [Fact c.Valid] (ts : List (List Bool))
    (ht : ts.length = c.degree) (x : c.Carrier) :
    vectorNegStr (encNat c.characteristic) (frame ts)
        (encodeNumerals (c.encodeElement x)) = encodeNumerals (c.encodeElement (-x)) := by
  rw [vectorNegStr_spec]
  congr 1
  apply List.ext_getElem
  · simp [FieldCode.encodeElement, ht]
  · intro i hi hj
    have hi' : i < c.degree := by simpa [FieldCode.encodeElement] using hj
    simp [FieldCode.encodeElement, List.getElem_ofFn, hi', ht]

theorem vectorScaleStr_encoded (c : FieldCode) [Fact c.Valid] (ts : List (List Bool))
    (ht : ts.length = c.degree) (a : ℕ) (x : c.Carrier) :
    vectorScaleStr (encNat c.characteristic) (frame ts) (encNat a)
        (encodeNumerals (c.encodeElement x)) =
      encodeNumerals (c.encodeElement ((a : ZMod c.characteristic) • x)) := by
  rw [vectorScaleStr_spec]
  congr 1
  apply List.ext_getElem
  · simp [FieldCode.encodeElement, ht]
  · intro i hi hj
    have hi' : i < c.degree := by simpa [FieldCode.encodeElement] using hj
    simp [FieldCode.encodeElement, List.getElem_ofFn, hi', ht]

end SparseIrred.UpperBounds.Section4
