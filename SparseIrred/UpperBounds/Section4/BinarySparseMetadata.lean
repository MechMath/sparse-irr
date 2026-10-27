import SparseIrred.UpperBounds.Section4.BinarySparse
import SparseIrred.UpperBounds.Section4.BinaryDegree
import SparseIrred.UpperBounds.Section4.BinaryField

/-! # Sparse degrees and leading coefficients computed by binary scans -/

namespace SparseIrred.UpperBounds.Section4

open Polynomial Complexity SparseDiv SparseDiv.StringArith
open scoped BigOperators

def sparseExponentsStr (derivative : Bool) (terms : List Bool) : List Bool :=
  mapBlocks (fun term ↦ if derivative then canonBits (subBits (pairSnd term) [true])
    else canonBits (pairSnd term)) terms

theorem cobham_sparseExponentsStr {n : ℕ} (d : Bool)
    {s : (Fin n → List Bool) → List Bool} (hs : Cobham s) :
    Cobham fun u ↦ sparseExponentsStr d (s u) := by
  have hfun : Cobham fun u : Fin 1 → List Bool ↦
      if d then canonBits (subBits (pairSnd (u 0)) [true]) else canonBits (pairSnd (u 0)) := by
    cases d
    · exact cobham_canonBits_comp (cobham_pairSnd_comp (.proj 0))
    · exact cobham_canonBits_comp (cobham_subBits_comp (cobham_pairSnd_comp (.proj 0)) (.const _))
  have hm := cobham_mapBlocks (n := 0) hfun (Polynomial.X + Polynomial.C 3) (by
    intro u
    have ht := pairSnd_length_le (u 0)
    have hsum : (u 0).length ≤ ∑ i, (u i).length :=
      Finset.single_le_sum (f := fun i ↦ (u i).length)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ 0)
    cases d <;> simp only [Bool.false_eq_true, ↓reduceIte, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C, Fin.sum_univ_one]
    ·
      have hc := length_canonBits_le (pairSnd (u 0))
      omega
    ·
      have hc := length_canonBits_le (subBits (pairSnd (u 0)) [true])
      have hb := length_subBits_le (pairSnd (u 0)) [true]
      simp only [List.length_cons, List.length_nil] at hb
      omega)
  exact (Cobham.comp hm (fun _ ↦ hs)).of_eq (fun _ ↦ rfl)

theorem sparseExponentsStr_encoded (d : Bool) (ts : SparseTerms) :
    sparseExponentsStr d (frame (ts.map encodeTerm)) =
      encodeNumerals (ts.map (fun t ↦ if d then t.2 - 1 else t.2)) := by
  simp only [sparseExponentsStr, mapBlocks_frame, encodeNumerals, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t ht
  cases d <;> simp only [Function.comp_apply, Bool.false_eq_true, Bool.true_eq, ↓reduceIte,
    encodeTerm, pairSnd_pair, canonBits, decNat_subBits, decNat_encNat]
  rfl

def sparseDerivativeCoefficientStr (p h terms i : List Bool) : List Bool :=
  let next := canonBits (succBits i)
  fieldMulStr p h (sparseCoefficientStr p h terms next) (fieldConstStr p h next)

theorem cobham_sparseDerivativeCoefficientStr {n : ℕ}
    {p h t i : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (hh : Cobham h) (ht : Cobham t) (hi : Cobham i) :
    Cobham fun u ↦ sparseDerivativeCoefficientStr (p u) (h u) (t u) (i u) :=
  cobham_fieldMulStr_comp hp hh
    (cobham_sparseCoefficientStr_comp hp hh ht (cobham_canonBits_comp (cobham_succBits_comp hi)))
    (cobham_fieldConstStr_comp hp hh (cobham_canonBits_comp (cobham_succBits_comp hi)))

theorem sparseDerivativeCoefficientStr_encoded (c : FieldCode) [Fact c.Valid]
    (ts : SparseTerms) (i : ℕ) :
    sparseDerivativeCoefficientStr (encNat c.characteristic) (encodeNumerals c.modulus)
      (frame (ts.map encodeTerm)) (encNat i) =
      encodeNumerals (c.encodeElement ((c.sparsePolynomial ts).derivative.coeff i)) := by
  have hn : canonBits (succBits (encNat i)) = encNat (i + 1) := by
    rw [canonBits, decNat_succBits, decNat_encNat]
  simp only [sparseDerivativeCoefficientStr, hn, sparseCoefficientStr_encoded,
    fieldConstStr_encoded, fieldMulStr_encoded, coeff_derivative]
  simp

def sparseCoefficientZeroStr (derivative : Bool) (p h terms i : List Bool) : List Bool :=
  fieldZeroFlagStr h (if derivative then sparseDerivativeCoefficientStr p h terms i
    else sparseCoefficientStr p h terms i)

def sparseDegreeStr (derivative : Bool) (p h terms : List Bool) : List Bool :=
  degreeScanStr (sparseCoefficientZeroStr derivative p h terms) (sparseExponentsStr derivative terms)

theorem cobham_sparseCoefficientZeroStr {n : ℕ} (d : Bool)
    {p h t i : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (hh : Cobham h) (ht : Cobham t) (hi : Cobham i) :
    Cobham fun u ↦ sparseCoefficientZeroStr d (p u) (h u) (t u) (i u) := by
  cases d
  · exact cobham_fieldZeroFlagStr_comp hh (cobham_sparseCoefficientStr_comp hp hh ht hi)
  · exact cobham_fieldZeroFlagStr_comp hh (cobham_sparseDerivativeCoefficientStr hp hh ht hi)

theorem cobham_sparseDegreeStr {n : ℕ} (d : Bool)
    {p h t : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (hh : Cobham h) (ht : Cobham t) :
    Cobham fun u ↦ sparseDegreeStr d (p u) (h u) (t u) := by
  have lift {f : (Fin n → List Bool) → List Bool} (hf : Cobham f) :
      Cobham fun u : Fin (n + 1) → List Bool ↦ f (Fin.tail u) :=
    (Cobham.comp hf (fun i ↦ Cobham.proj i.succ)).of_eq (fun _ ↦ rfl)
  exact cobham_degreeScanStr (cobham_sparseCoefficientZeroStr d (lift hp) (lift hh) (lift ht) (.proj 0))
    (cobham_sparseExponentsStr d ht)

theorem FieldCode.sparsePolynomial_coeff_zero_of_not_mem (c : FieldCode) (ts : SparseTerms)
    (i : ℕ) (hi : i ∉ ts.map Prod.snd) : (c.sparsePolynomial ts).coeff i = 0 := by
  induction ts with
  | nil => simp [FieldCode.sparsePolynomial]
  | cons t ts ih =>
    have ht : t.2 ≠ i := by intro he; exact hi (by simp [he])
    have hs : i ∉ ts.map Prod.snd := by intro he; exact hi (by simp [he])
    change (monomial t.2 (c.element t.1) + c.sparsePolynomial ts).coeff i = 0
    rw [coeff_add, coeff_monomial, if_neg ht, ih hs, zero_add]

theorem FieldCode.sparsePolynomial_support (c : FieldCode) (ts : SparseTerms) (i : ℕ)
    (hi : (c.sparsePolynomial ts).coeff i ≠ 0) : i ∈ ts.map Prod.snd := by
  by_contra h
  exact hi (c.sparsePolynomial_coeff_zero_of_not_mem ts i h)

theorem FieldCode.sparsePolynomial_derivative_support (c : FieldCode) (ts : SparseTerms) (i : ℕ)
    (hi : (c.sparsePolynomial ts).derivative.coeff i ≠ 0) :
    i ∈ ts.map (fun t ↦ t.2 - 1) := by
  have hc : (c.sparsePolynomial ts).coeff (i + 1) ≠ 0 := by
    intro hc
    exact hi (by simp [coeff_derivative, hc])
  obtain ⟨t, ht, he⟩ := List.mem_map.mp (c.sparsePolynomial_support ts (i + 1) hc)
  exact List.mem_map.mpr ⟨t, ht, by simp_all⟩

theorem sparseDegreeStr_encoded (c : FieldCode) [Fact c.Valid] [DecidableEq c.Carrier]
    (d : Bool) (ts : SparseTerms) :
    sparseDegreeStr d (encNat c.characteristic) (encodeNumerals c.modulus)
      (frame (ts.map encodeTerm)) =
      encNat (if d then (c.sparsePolynomial ts).derivative.natDegree else (c.sparsePolynomial ts).natDegree) := by
  rw [sparseDegreeStr, sparseExponentsStr_encoded]
  cases d with
  | false =>
    apply degreeScanStr_polynomial (c.sparsePolynomial ts)
    · intro i
      simp only [sparseCoefficientZeroStr, Bool.false_eq_true, ↓reduceIte,
        sparseCoefficientStr_encoded, fieldZeroFlagStr_encoded]
    · exact c.sparsePolynomial_support ts
  | true =>
    apply degreeScanStr_polynomial (c.sparsePolynomial ts).derivative
    · intro i
      simp only [sparseCoefficientZeroStr, ↓reduceIte,
        sparseDerivativeCoefficientStr_encoded, fieldZeroFlagStr_encoded]
    · exact c.sparsePolynomial_derivative_support ts

def sparseLeadingInverseStr (p h terms : List Bool) : List Bool :=
  fieldInvStr p h (sparseCoefficientStr p h terms (sparseDegreeStr false p h terms))

theorem cobham_sparseLeadingInverseStr {n : ℕ}
    {p h t : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (hh : Cobham h) (ht : Cobham t) :
    Cobham fun u ↦ sparseLeadingInverseStr (p u) (h u) (t u) :=
  cobham_fieldInvStr_comp hp hh (cobham_sparseCoefficientStr_comp hp hh ht
    (cobham_sparseDegreeStr false hp hh ht))

theorem sparseLeadingInverseStr_encoded (c : FieldCode) [Fact c.Valid] [DecidableEq c.Carrier]
    (ts : SparseTerms) :
    sparseLeadingInverseStr (encNat c.characteristic) (encodeNumerals c.modulus)
      (frame (ts.map encodeTerm)) =
      encodeNumerals (c.encodeElement (c.sparsePolynomial ts).leadingCoeff⁻¹) := by
  simp only [sparseLeadingInverseStr, sparseDegreeStr_encoded, Bool.false_eq_true, if_false,
    sparseCoefficientStr_encoded, fieldInvStr_encoded]
  rfl

end SparseIrred.UpperBounds.Section4
