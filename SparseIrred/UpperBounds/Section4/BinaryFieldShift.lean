import SparseIrred.UpperBounds.Section4.BinaryFieldVector
import SparseIrred.UpperBounds.Section4.HeaderBounds

/-! # Multiplication by the quotient root on fixed-length binary coefficient vectors -/

namespace SparseIrred.UpperBounds.Section4

set_option backward.isDefEq.respectTransparency false

open Polynomial Complexity SparseDiv SparseDiv.StringArith SparseGcd SparseGcd.TermsStr

/-- Drop the final framed coefficient, obtaining the modulus's lower coefficients. -/
def fieldTemplateStr (modulus : List Bool) : List Bool :=
  revBlocks (pairSnd (revBlocks modulus))

theorem cobham_fieldTemplateStr_comp {n : ℕ} {h : (Fin n → List Bool) → List Bool}
    (hh : Cobham h) : Cobham fun v ↦ fieldTemplateStr (h v) :=
  cobham_revBlocks_comp (cobham_pairSnd_comp (cobham_revBlocks_comp hh))

theorem fieldTemplateStr_frame (hs : List (List Bool)) :
    fieldTemplateStr (frame hs) = frame hs.dropLast := by
  rw [fieldTemplateStr, revBlocks_frame]
  have htail : pairSnd (frame hs.reverse) = frame hs.reverse.tail := by
    cases hs.reverse <;> simp [SparseGcd.frame_cons_eq_pair, frame_nil]
    rfl
  rw [htail, revBlocks_frame]
  congr 1
  simp

/-- Read the coefficient of degree `d-1`, where `d` is the template length. -/
def vectorHighStr (template a : List Bool) : List Bool :=
  nthBlockStr (countBlocks template).tail a

theorem cobham_vectorHighStr_comp {n : ℕ} {t a : (Fin n → List Bool) → List Bool}
    (ht : Cobham t) (ha : Cobham a) : Cobham fun v ↦ vectorHighStr (t v) (a v) :=
  TermsStr.cobham_nthBlockStr_comp
    (Cobham.tailFn (cobham_countBlocks_comp ht)) ha

/-- Shift once and cancel the top coefficient with the monic input modulus. -/
def fieldShiftStr (p modulus a : List Bool) : List Bool :=
  let t := fieldTemplateStr modulus
  vectorSubStr p t (pair [] a) (vectorScaleStr p t (vectorHighStr t a) modulus)

theorem cobham_fieldShiftStr_comp {n : ℕ} {p h a : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (hh : Cobham h) (ha : Cobham a) :
    Cobham fun v ↦ fieldShiftStr (p v) (h v) (a v) :=
  cobham_vectorSubStr_comp hp (cobham_fieldTemplateStr_comp hh)
    (cobham_pair_comp (.const []) ha)
    (cobham_vectorScaleStr_comp hp (cobham_fieldTemplateStr_comp hh)
      (cobham_vectorHighStr_comp (cobham_fieldTemplateStr_comp hh) ha) hh)

theorem fieldShiftStr_length (p h a : List Bool) :
    (fieldShiftStr p h a).length ≤
      (2 * p.length + 2) * (blocks (fieldTemplateStr h)).length :=
  vectorAddStr_length _ _ _ _

theorem FieldCode.encodeElement_coeff (c : FieldCode) [Fact c.Valid]
    (x : c.Carrier) (i : ℕ) (hi : i < c.degree) :
    (c.encodeElement x).getD i 0 = (c.coordinateBasis.repr x ⟨i, hi⟩).val := by
  simp [FieldCode.encodeElement, hi]

theorem vectorHighStr_encoded (c : FieldCode) [Fact c.Valid]
    (ts : List (List Bool)) (ht : ts.length = c.degree) (x : c.Carrier) :
    vectorHighStr (frame ts) (encodeNumerals (c.encodeElement x)) =
      encNat ((c.encodeElement x).getD (c.degree - 1) 0) := by
  unfold vectorHighStr
  rw [countBlocks_frame]
  have hu : (unaryN ts.length).tail = unaryN (ts.length - 1) := by
    simp [unaryN, List.tail_replicate]
  rw [hu, nthBlockStr_encodeNumerals, ht]

/-- Reconstruct a polynomial from the base-prime values of its low coefficients. -/
theorem densePolynomial_coeff_vector (p d : ℕ) [NeZero p]
    (f : (ZMod p)[X]) (hf : f.degree < d) :
    densePolynomial (List.ofFn (fun i : Fin d ↦ (f.coeff i.val).val)) = f := by
  ext i
  rw [densePolynomial_coeff]
  by_cases hi : i < d
  · simp [hi]
  · have hfi : f.coeff i = 0 := (Polynomial.degree_lt_iff_coeff_zero f d).mp hf i (by omega)
    simp [hi, hfi]

/-- Cancelling the top coefficient after a shift leaves degree strictly below the modulus. -/
theorem shifted_reduced_degree (c : FieldCode) [Fact c.Valid] (a : List ℕ)
    (ha : a.length = c.degree) :
    (X * densePolynomial (R := ZMod c.characteristic) a -
      C (a.getD (c.degree - 1) 0 : ZMod c.characteristic) * c.polynomial).degree <
        (c.degree : WithBot ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro i hi
  have hd := c.degree_pos
  have hip : 0 < i := by omega
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hip)
  rw [Polynomial.coeff_sub, coeff_X_mul, densePolynomial_coeff, coeff_C_mul]
  by_cases he : j + 1 = c.degree
  · have hj : j = c.degree - 1 := by omega
    rw [hj, show (c.degree - 1).succ = c.polynomial.natDegree by change _ = c.degree; omega]
    rw [Polynomial.coeff_natDegree, (Fact.out : c.Valid).monic.leadingCoeff]
    simp
  · have ha0 : a.getD j 0 = 0 := List.getD_eq_default a 0 (by omega)
    have hf0 : c.polynomial.coeff (j + 1) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt
      (by change c.degree < j + 1; omega)
    rw [ha0, hf0]
    simp

noncomputable def FieldCode.generator (c : FieldCode) : c.Carrier := AdjoinRoot.root c.polynomial

/-- The formula used by the binary shift computes precisely multiplication by the
quotient root; this is proved in the actual presented finite field. -/
theorem FieldCode.root_mul_coordinate (c : FieldCode) [Fact c.Valid] (x : c.Carrier)
    (i : Fin c.degree) :
    c.coordinateBasis.repr (c.generator * x) i =
      ((0 :: c.encodeElement x).getD i.val 0 : ZMod c.characteristic) -
        ((c.encodeElement x).getD (c.degree - 1) 0 : ZMod c.characteristic) *
          (c.modulus.getD i.val 0 : ZMod c.characteristic) := by
  let a := c.encodeElement x
  let r : (ZMod c.characteristic)[X] := X * densePolynomial a -
    C (a.getD (c.degree - 1) 0 : ZMod c.characteristic) * c.polynomial
  have hr : r.degree < (c.degree : WithBot ℕ) :=
    shifted_reduced_degree c a (c.encodeElement_canonical x).1
  have he : (AdjoinRoot.mk c.polynomial r : c.Carrier) =
      c.generator * x := by
    dsimp only [r]
    rw [map_sub, map_mul, AdjoinRoot.mk_X, map_mul, AdjoinRoot.mk_self, mul_zero, sub_zero]
    congr 1
    exact c.element_encodeElement x
  rw [← he]
  change (AdjoinRoot.modByMonicHom (Fact.out : c.Valid).monic
    (AdjoinRoot.mk c.polynomial r)).coeff i.val = _
  rw [AdjoinRoot.modByMonicHom_mk,
    (Polynomial.modByMonic_eq_self_iff (Fact.out : c.Valid).monic).mpr
      (by simpa only [Polynomial.degree_eq_natDegree (Fact.out : c.Valid).monic.ne_zero,
        FieldCode.degree] using hr)]
  simp only [r, Polynomial.coeff_sub, coeff_C_mul]
  rw [show c.polynomial = densePolynomial c.modulus from rfl, densePolynomial_coeff]
  congr 1
  cases hi : i.val with
  | zero => simp [coeff_X_mul, hi]
  | succ j => simp [coeff_X_mul, densePolynomial_coeff, hi, a]

theorem fieldShiftStr_encoded (c : FieldCode) [Fact c.Valid] (x : c.Carrier) :
    fieldShiftStr (encNat c.characteristic) (encodeNumerals c.modulus)
        (encodeNumerals (c.encodeElement x)) =
      encodeNumerals (c.encodeElement (c.generator * x)) := by
  have ht : (c.modulus.map encNat).dropLast.length = c.degree := by
    simp only [List.length_dropLast, List.length_map]
    exact (FieldCode.Valid.structural (Fact.out : c.Valid)).degree_eq.symm
  unfold fieldShiftStr
  rw [encodeNumerals, fieldTemplateStr_frame]
  dsimp only
  rw [vectorHighStr_encoded c _ ht x]
  have hp : pair [] (encodeNumerals (c.encodeElement x)) =
      encodeNumerals (0 :: c.encodeElement x) := rfl
  rw [hp]
  unfold vectorSubStr
  change vectorAddStr (encNat c.characteristic) (frame (c.modulus.map encNat).dropLast)
    (encodeNumerals (0 :: c.encodeElement x))
    (vectorNegStr (encNat c.characteristic) (frame (c.modulus.map encNat).dropLast)
      (vectorScaleStr (encNat c.characteristic) (frame (c.modulus.map encNat).dropLast)
        (encNat ((c.encodeElement x).getD (c.degree - 1) 0)) (encodeNumerals c.modulus))) = _
  rw [vectorScaleStr_spec, vectorNegStr_spec, vectorAddStr_spec]
  congr 1
  apply List.ext_getElem
  · simp [FieldCode.encodeElement, ht]
  · intro i hi hj
    have hi' : i < c.degree := by simpa [FieldCode.encodeElement] using hj
    rw [List.getElem_ofFn]
    simp only [List.length_dropLast, List.length_map] at ht
    have hcoord := c.root_mul_coordinate x ⟨i, hi'⟩
    simp only [FieldCode.encodeElement, List.getElem_ofFn]
    rw [hcoord]
    simp [ht, hi', sub_eq_add_neg, FieldCode.encodeElement]

end SparseIrred.UpperBounds.Section4
