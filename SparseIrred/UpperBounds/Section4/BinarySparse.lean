import SparseIrred.UpperBounds.Section4.BinaryFieldMul
import SparseIrred.UpperBounds.Section4.BinaryInput

/-!
# Sparse coefficient queries without a dense polynomial

One query scans the input's term list, reducing each selected coefficient vector
in the encoded field and adding all contributions at the queried exponent.
Repeated exponents, zero terms and arbitrary coefficient-vector lengths are
handled by the same program.
-/

namespace SparseIrred.UpperBounds.Section4

open Polynomial Complexity SparseDiv SparseDiv.StringArith
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

def sparseCoefficientStepStr (p h index acc term : List Bool) : List Bool :=
  vectorAddStr p (fieldTemplateStr h) acc
    (binaryEq (pairSnd term) index (fieldNormalizeStr p h (pairFst term)) (fieldZeroStr h))

def sparseCoefficientStr (p h terms index : List Bool) : List Bool :=
  foldBlocks (sparseCoefficientStepStr p h index) (fieldZeroStr h) terms

theorem cobham_sparseCoefficientStepStr {n : ℕ}
    {p h i a t : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (hh : Cobham h) (hi : Cobham i) (ha : Cobham a) (ht : Cobham t) :
    Cobham fun u ↦ sparseCoefficientStepStr (p u) (h u) (i u) (a u) (t u) :=
  cobham_vectorAddStr_comp hp (cobham_fieldTemplateStr_comp hh) ha
    (cobham_binaryEq (cobham_pairSnd_comp ht) hi
      (cobham_fieldNormalizeStr_comp hp hh (cobham_pairFst_comp ht))
      (cobham_fieldZeroStr_comp hh))

theorem sparseCoefficientStepStr_length (p h i a t : List Bool) :
    (sparseCoefficientStepStr p h i a t).length ≤ (2 * p.length + 2) * h.length := by
  have hs := vectorAddStr_length p (fieldTemplateStr h) a
    (binaryEq (pairSnd t) i (fieldNormalizeStr p h (pairFst t)) (fieldZeroStr h))
  have hb : (blocks (fieldTemplateStr h)).length ≤ h.length := by
    rw [fieldTemplateStr_blocks, List.length_dropLast]
    exact (Nat.sub_le _ _).trans (blocks_length_le_input h)
  exact hs.trans (Nat.mul_le_mul_left _ hb)

theorem cobham_sparseCoefficientStr :
    Cobham fun u : Fin 4 → List Bool ↦ sparseCoefficientStr (u 0) (u 1) (u 2) (u 3) := by
  have hf := cobham_foldBlocks_bounded
    (step := fun u : Fin 5 → List Bool ↦ sparseCoefficientStepStr (u 2) (u 3) (u 4) (u 0) (u 1))
    (cobham_sparseCoefficientStepStr (.proj 2) (.proj 3) (.proj 4) (.proj 0) (.proj 1))
    (initial := fun u : Fin 3 → List Bool ↦ fieldZeroStr (u 1))
    (cobham_fieldZeroStr_comp (.proj 1)) (2 * Polynomial.X ^ 2 + 2 * Polynomial.X) (by
      intro u
      have hb := sparseCoefficientStepStr_length (u 2) (u 3) (u 4) (u 0) (u 1)
      have hp : (u 2).length ≤ ∑ i : Fin 4, (Fin.tail u i).length := by
        change (Fin.tail u (1 : Fin 4)).length ≤ _
        exact Finset.single_le_sum (fun i _ ↦ Nat.zero_le ((Fin.tail u i).length))
          (Finset.mem_univ (1 : Fin 4))
      have hh : (u 3).length ≤ ∑ i : Fin 4, (Fin.tail u i).length := by
        change (Fin.tail u (2 : Fin 4)).length ≤ _
        exact Finset.single_le_sum (fun i _ ↦ Nat.zero_le ((Fin.tail u i).length))
          (Finset.mem_univ (2 : Fin 4))
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_ofNat]
      nlinarith [Nat.mul_le_mul hp hh])
  exact (Cobham.comp hf (gs := fun i u ↦ (![u 2, u 0, u 1, u 3] : Fin 4 → List Bool) i)
    (fun i ↦ by fin_cases i <;> exact Cobham.proj _)).of_eq (fun _ ↦ rfl)

theorem cobham_sparseCoefficientStr_comp {n : ℕ}
    {p h t i : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (hh : Cobham h) (ht : Cobham t) (hi : Cobham i) :
    Cobham fun u ↦ sparseCoefficientStr (p u) (h u) (t u) (i u) :=
  (Cobham.comp cobham_sparseCoefficientStr
    (gs := fun j u ↦ (![p u, h u, t u, i u] : Fin 4 → List Bool) j)
    (fun j ↦ by fin_cases j <;> assumption)).of_eq (fun _ ↦ rfl)

theorem sparseCoefficientStepStr_encoded (c : FieldCode) [Fact c.Valid]
    (i : ℕ) (a : c.Carrier) (t : List ℕ × ℕ) :
    sparseCoefficientStepStr (encNat c.characteristic) (encodeNumerals c.modulus) (encNat i)
      (encodeNumerals (c.encodeElement a)) (encodeTerm t) =
      encodeNumerals (c.encodeElement (a + if t.2 = i then c.element t.1 else 0)) := by
  simp only [sparseCoefficientStepStr, encodeTerm, pairFst_pair, pairSnd_pair, binaryEq,
    decNat_encNat, fieldNormalizeStr_encoded, fieldZeroStr_encoded]
  have ht : fieldTemplateStr (encodeNumerals c.modulus) =
      frame ((c.modulus.map encNat).dropLast) := fieldTemplateStr_frame _
  rw [ht]
  split_ifs <;> exact vectorAddStr_encoded c _ c.template_length _ _

theorem sparseCoefficient_fold_encoded (c : FieldCode) [Fact c.Valid]
    (ts : SparseTerms) (i : ℕ) (a : c.Carrier) :
    (ts.map encodeTerm).foldl
      (sparseCoefficientStepStr (encNat c.characteristic) (encodeNumerals c.modulus) (encNat i))
      (encodeNumerals (c.encodeElement a)) =
      encodeNumerals (c.encodeElement (a + (c.sparsePolynomial ts).coeff i)) := by
  induction ts generalizing a with
  | nil => simp [FieldCode.sparsePolynomial]
  | cons t ts ih =>
    rw [List.map_cons, List.foldl_cons, sparseCoefficientStepStr_encoded, ih]
    congr 2
    simp [FieldCode.sparsePolynomial, coeff_monomial, add_assoc]

theorem sparseCoefficientStr_encoded (c : FieldCode) [Fact c.Valid] (ts : SparseTerms) (i : ℕ) :
    sparseCoefficientStr (encNat c.characteristic) (encodeNumerals c.modulus)
      (frame (ts.map encodeTerm)) (encNat i) =
      encodeNumerals (c.encodeElement ((c.sparsePolynomial ts).coeff i)) := by
  rw [sparseCoefficientStr, foldBlocks_frame, fieldZeroStr_encoded, sparseCoefficient_fold_encoded]
  simp

end SparseIrred.UpperBounds.Section4
