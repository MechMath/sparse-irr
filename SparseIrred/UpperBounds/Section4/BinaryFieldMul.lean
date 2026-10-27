import SparseIrred.UpperBounds.Section4.BinaryFieldShift
import SparseIrred.UpperBounds.Section4.BinaryList

/-! # Horner multiplication and arbitrary-vector reduction in polynomial time -/

namespace SparseIrred.UpperBounds.Section4

open Polynomial Complexity SparseDiv SparseDiv.StringArith SparseGcd SparseGcd.TermsStr

set_option backward.isDefEq.respectTransparency false

def fieldZeroStr (h : List Bool) : List Bool := vectorZeroStr (fieldTemplateStr h)
def fieldConstStr (p h a : List Bool) : List Bool := vectorRedStr p (fieldTemplateStr h) (delimit a)
def fieldOneStr (p h : List Bool) : List Bool := fieldConstStr p h [true]

def fieldMulStepStr (p h a acc digit : List Bool) : List Bool :=
  vectorAddStr p (fieldTemplateStr h) (fieldShiftStr p h acc)
    (vectorScaleStr p (fieldTemplateStr h) digit a)

def fieldMulStr (p h a b : List Bool) : List Bool :=
  foldBlocks (fieldMulStepStr p h a) (fieldZeroStr h) (revBlocks b)

/-- Horner evaluation also reduces input vectors of arbitrary length. -/
def fieldNormalizeStr (p h a : List Bool) : List Bool := fieldMulStr p h (fieldOneStr p h) a

theorem cobham_fieldZeroStr_comp {n : ℕ} {h : (Fin n → List Bool) → List Bool}
    (hh : Cobham h) : Cobham fun v ↦ fieldZeroStr (h v) :=
  cobham_vectorZeroStr_comp (cobham_fieldTemplateStr_comp hh)

theorem cobham_fieldConstStr_comp {n : ℕ} {p h a : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (hh : Cobham h) (ha : Cobham a) :
    Cobham fun v ↦ fieldConstStr (p v) (h v) (a v) :=
  cobham_vectorRedStr_comp hp (cobham_fieldTemplateStr_comp hh) (SparseGcd.cobham_delimit_comp ha)

theorem cobham_fieldOneStr_comp {n : ℕ} {p h : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (hh : Cobham h) : Cobham fun v ↦ fieldOneStr (p v) (h v) :=
  cobham_fieldConstStr_comp hp hh (.const [true])

theorem cobham_fieldMulStepStr_comp {n : ℕ}
    {p h a acc digit : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (hh : Cobham h) (ha : Cobham a) (hr : Cobham acc) (hd : Cobham digit) :
    Cobham fun v ↦ fieldMulStepStr (p v) (h v) (a v) (acc v) (digit v) :=
  cobham_vectorAddStr_comp hp (cobham_fieldTemplateStr_comp hh)
    (cobham_fieldShiftStr_comp hp hh hr)
    (cobham_vectorScaleStr_comp hp (cobham_fieldTemplateStr_comp hh) hd ha)

theorem fieldMulStepStr_length (p h a acc digit : List Bool) :
    (fieldMulStepStr p h a acc digit).length ≤
      (2 * p.length + 2) * (blocks (fieldTemplateStr h)).length :=
  vectorAddStr_length _ _ _ _

theorem blocks_length_le_input (s : List Bool) : (blocks s).length ≤ s.length := by
  obtain ⟨bs, rem, rfl, hrem⟩ := exists_frame_append s
  rcases hrem with rfl | hbad
  · simpa only [List.append_nil, blocks_frame] using length_le_length_frame bs
  · by_cases hne : rem = []
    · subst rem
      simpa only [List.append_nil, blocks_frame] using length_le_length_frame bs
    · rw [blocks_frame_append_of_bad bs hne hbad]
      simp

theorem fieldTemplateStr_blocks (s : List Bool) :
    blocks (fieldTemplateStr s) = (blocks s).dropLast := by
  have hr : revBlocks s = frame (blocks s).reverse := by
    have he : revBlocks s = revBlocks (frame (blocks s)) := by
      simp [revBlocks, foldBlocks, blocks_frame]
    rw [he, revBlocks_frame]
  rw [fieldTemplateStr, hr]
  have ht : pairSnd (frame (blocks s).reverse) = frame (blocks s).reverse.tail := by
    cases (blocks s).reverse <;> simp [SparseGcd.frame_cons_eq_pair, frame_nil]
    rfl
  rw [ht, revBlocks_frame, blocks_frame]
  simp

theorem fieldMulStepStr_length_input (p h a acc digit : List Bool) :
    (fieldMulStepStr p h a acc digit).length ≤ (2 * p.length + 2) * h.length := by
  have hlen : (blocks (fieldTemplateStr h)).length ≤ h.length := by
    rw [fieldTemplateStr_blocks, List.length_dropLast]
    exact (Nat.sub_le _ _).trans (blocks_length_le_input h)
  exact (fieldMulStepStr_length p h a acc digit).trans (Nat.mul_le_mul_left _ hlen)

theorem cobham_fieldMulStr :
    Cobham fun v : Fin 4 → List Bool ↦ fieldMulStr (v 0) (v 1) (v 2) (v 3) := by
  have hfold := cobham_foldBlocks_bounded
    (step := fun u : Fin 5 → List Bool ↦ fieldMulStepStr (u 2) (u 3) (u 4) (u 0) (u 1))
    (cobham_fieldMulStepStr_comp (.proj 2) (.proj 3) (.proj 4) (.proj 0) (.proj 1))
    (initial := fun u : Fin 3 → List Bool ↦ fieldZeroStr (u 1))
    (cobham_fieldZeroStr_comp (.proj 1))
    (2 * Polynomial.X ^ 2 + 2 * Polynomial.X) (by
      intro u
      have h := fieldMulStepStr_length_input (u 2) (u 3) (u 4) (u 0) (u 1)
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_ofNat]
      have hp : (u 2).length ≤ ∑ i : Fin 4, (Fin.tail u i).length := by
        change (Fin.tail u (1 : Fin 4)).length ≤ _
        exact Finset.single_le_sum (f := fun i : Fin 4 ↦ (Fin.tail u i).length)
          (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ (1 : Fin 4))
      have hh : (u 3).length ≤ ∑ i : Fin 4, (Fin.tail u i).length := by
        change (Fin.tail u (2 : Fin 4)).length ≤ _
        exact Finset.single_le_sum (f := fun i : Fin 4 ↦ (Fin.tail u i).length)
          (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ (2 : Fin 4))
      nlinarith)
  refine (Cobham.comp hfold
    (gs := fun i (v : Fin 4 → List Bool) ↦ ![revBlocks (v 3), v 0, v 1, v 2] i)
    (by intro i; fin_cases i
        exact cobham_revBlocks_comp (.proj 3)
        exact Cobham.proj 0
        exact Cobham.proj 1
        exact Cobham.proj 2)).of_eq ?_
  intro v
  rfl

theorem cobham_fieldMulStr_comp {n : ℕ} {p h a b : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (hh : Cobham h) (ha : Cobham a) (hb : Cobham b) :
    Cobham fun v ↦ fieldMulStr (p v) (h v) (a v) (b v) := by
  exact (Cobham.comp cobham_fieldMulStr
    (gs := fun i v ↦ ![p v, h v, a v, b v] i)
    (by intro i; fin_cases i; exact hp; exact hh; exact ha; exact hb)).of_eq fun _ ↦ rfl

theorem cobham_fieldNormalizeStr_comp {n : ℕ} {p h a : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (hh : Cobham h) (ha : Cobham a) :
    Cobham fun v ↦ fieldNormalizeStr (p v) (h v) (a v) :=
  cobham_fieldMulStr_comp hp hh (cobham_fieldOneStr_comp hp hh) ha

theorem FieldCode.template_length (c : FieldCode) [Fact c.Valid] :
    (c.modulus.map encNat).dropLast.length = c.degree := by
  simp only [List.length_dropLast, List.length_map]
  exact (FieldCode.Valid.structural (Fact.out : c.Valid)).degree_eq.symm

theorem fieldZeroStr_encoded (c : FieldCode) [Fact c.Valid] :
    fieldZeroStr (encodeNumerals c.modulus) = encodeNumerals (c.encodeElement 0) := by
  rw [fieldZeroStr, encodeNumerals, fieldTemplateStr_frame, vectorZeroStr_frame]
  rw [c.template_length, c.encodeElement_zero]

theorem FieldCode.scalar_coordinate (c : FieldCode) [Fact c.Valid]
    (a : ZMod c.characteristic) (i : Fin c.degree) :
    c.coordinateBasis.repr (algebraMap (ZMod c.characteristic) c.Carrier a) i =
      if i.val = 0 then a else 0 := by
  change (AdjoinRoot.modByMonicHom (Fact.out : c.Valid).monic
    (AdjoinRoot.mk c.polynomial (C a))).coeff i.val = _
  rw [AdjoinRoot.modByMonicHom_mk]
  have hd : (C a).degree < c.polynomial.degree := by
    apply lt_of_le_of_lt Polynomial.degree_C_le
    rw [Polynomial.degree_eq_natDegree (Fact.out : c.Valid).monic.ne_zero]
    exact_mod_cast c.degree_pos
  rw [(Polynomial.modByMonic_eq_self_iff (Fact.out : c.Valid).monic).mpr hd, coeff_C]

theorem fieldConstStr_encoded (c : FieldCode) [Fact c.Valid] (a : ℕ) :
    fieldConstStr (encNat c.characteristic) (encodeNumerals c.modulus) (encNat a) =
      encodeNumerals (c.encodeElement (algebraMap (ZMod c.characteristic) c.Carrier a)) := by
  unfold fieldConstStr
  rw [encodeNumerals, fieldTemplateStr_frame]
  have he : delimit (encNat a) = encodeNumerals [a] := by simp [encodeNumerals, frame]
  rw [he]
  rw [vectorRedStr_spec]
  congr 1
  apply List.ext_getElem
  · simp [FieldCode.encodeElement, c.template_length]
  · intro i hi hj
    simp only [FieldCode.encodeElement, List.getElem_ofFn]
    rw [c.scalar_coordinate]
    cases i <;> simp

theorem fieldOneStr_encoded (c : FieldCode) [Fact c.Valid] :
    fieldOneStr (encNat c.characteristic) (encodeNumerals c.modulus) =
      encodeNumerals (c.encodeElement 1) := by
  change fieldConstStr _ _ (encNat 1) = _
  rw [fieldConstStr_encoded]
  simp

theorem FieldCode.element_cons (c : FieldCode) [Fact c.Valid] (a : ℕ) (as : List ℕ) :
    c.element (a :: as) = (a : c.Carrier) + c.generator * c.element as := by
  change AdjoinRoot.mk c.polynomial (C (a : ZMod c.characteristic) + X * densePolynomial as) = _
  rw [map_add, map_mul, AdjoinRoot.mk_X]
  rfl

theorem fieldMulStepStr_encoded (c : FieldCode) [Fact c.Valid] (x r : c.Carrier) (a : ℕ) :
    fieldMulStepStr (encNat c.characteristic) (encodeNumerals c.modulus)
        (encodeNumerals (c.encodeElement x)) (encodeNumerals (c.encodeElement r)) (encNat a) =
      encodeNumerals (c.encodeElement (c.generator * r + (a : c.Carrier) * x)) := by
  unfold fieldMulStepStr
  rw [fieldShiftStr_encoded]
  have ht : fieldTemplateStr (encodeNumerals c.modulus) =
      frame (c.modulus.map encNat).dropLast := fieldTemplateStr_frame _
  rw [ht, vectorScaleStr_encoded c _ c.template_length,
    vectorAddStr_encoded c _ c.template_length]
  congr 2
  rw [Algebra.smul_def, map_natCast]

/-- The Horner fold invariant includes arbitrary nonzero initial accumulators. -/
theorem fieldMul_fold_encoded (c : FieldCode) [Fact c.Valid]
    (x r : c.Carrier) (as : List ℕ) :
    ((as.map encNat).reverse.foldl
      (fieldMulStepStr (encNat c.characteristic) (encodeNumerals c.modulus)
        (encodeNumerals (c.encodeElement x))) (encodeNumerals (c.encodeElement r))) =
      encodeNumerals (c.encodeElement (c.generator ^ as.length * r + c.element as * x)) := by
  induction as with
  | nil => simp [FieldCode.element, densePolynomial]
  | cons a as ih =>
      rw [List.map_cons, List.reverse_cons, List.foldl_append, ih, List.foldl_cons,
        fieldMulStepStr_encoded, List.foldl_nil, List.length_cons, c.element_cons]
      congr 2
      ring

/-- Multiplication is correct even when the second input coefficient vector is
longer than the extension degree or has unreduced natural digits. -/
theorem fieldMulStr_encoded_right (c : FieldCode) [Fact c.Valid] (x : c.Carrier) (as : List ℕ) :
    fieldMulStr (encNat c.characteristic) (encodeNumerals c.modulus)
        (encodeNumerals (c.encodeElement x)) (encodeNumerals as) =
      encodeNumerals (c.encodeElement (x * c.element as)) := by
  unfold fieldMulStr
  rw [fieldZeroStr_encoded]
  have he : revBlocks (encodeNumerals as) = frame (as.map encNat).reverse := revBlocks_frame _
  rw [he, foldBlocks_frame, fieldMul_fold_encoded]
  simp [mul_comm]

theorem fieldMulStr_encoded (c : FieldCode) [Fact c.Valid] (x y : c.Carrier) :
    fieldMulStr (encNat c.characteristic) (encodeNumerals c.modulus)
        (encodeNumerals (c.encodeElement x)) (encodeNumerals (c.encodeElement y)) =
      encodeNumerals (c.encodeElement (x * y)) := by
  rw [fieldMulStr_encoded_right, c.element_encodeElement]

/-- Full modular reduction of arbitrary dense natural coefficient lists, with
canonical fixed-length output and polynomial-time implementation. -/
theorem fieldNormalizeStr_encoded (c : FieldCode) [Fact c.Valid] (as : List ℕ) :
    fieldNormalizeStr (encNat c.characteristic) (encodeNumerals c.modulus) (encodeNumerals as) =
      encodeNumerals (c.encodeElement (c.element as)) := by
  rw [fieldNormalizeStr, fieldOneStr_encoded, fieldMulStr_encoded_right]
  simp

theorem vectorZeroStr_length (t : List Bool) :
    (vectorZeroStr t).length ≤ 2 * (blocks t).length := by
  unfold vectorZeroStr mapBlocks
  simpa using framed_map_length_le (blocks t) (fun _ ↦ []) 0 (by simp)

theorem fieldZeroStr_length (h : List Bool) : (fieldZeroStr h).length ≤ 2 * h.length := by
  have hb := vectorZeroStr_length (fieldTemplateStr h)
  rw [fieldTemplateStr_blocks, List.length_dropLast] at hb
  exact hb.trans (Nat.mul_le_mul_left _ ((Nat.sub_le _ _).trans (blocks_length_le_input h)))

theorem fieldConstStr_length (p h a : List Bool) :
    (fieldConstStr p h a).length ≤ (2 * p.length + 2) * h.length := by
  have hb := vectorRedStr_length p (fieldTemplateStr h) (delimit a)
  rw [fieldTemplateStr_blocks, List.length_dropLast] at hb
  exact hb.trans (Nat.mul_le_mul_left _ ((Nat.sub_le _ _).trans (blocks_length_le_input h)))

/-- The multiplication loop keeps the same fixed output bound at every iteration,
including malformed bit-string operands. -/
theorem fieldMulStr_length (p h a b : List Bool) :
    (fieldMulStr p h a b).length ≤ (2 * p.length + 2) * h.length := by
  have hf (bs : List (List Bool)) (acc : List Bool)
      (ha : acc.length ≤ (2 * p.length + 2) * h.length) :
      (bs.foldl (fieldMulStepStr p h a) acc).length ≤ (2 * p.length + 2) * h.length := by
    induction bs generalizing acc with
    | nil => exact ha
    | cons digit bs ih =>
        rw [List.foldl_cons]
        exact ih _ (fieldMulStepStr_length_input p h a acc digit)
  apply hf
  have hz := fieldZeroStr_length h
  nlinarith

end SparseIrred.UpperBounds.Section4
