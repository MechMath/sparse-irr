import SparseIrred.UpperBounds.Section4.BinaryField
import SparseIrred.UpperBounds.Section4.BinaryDegree

/-! # Binary coefficient and degree oracles for the dense prime-field modulus -/

namespace SparseIrred.UpperBounds.Section4

open Polynomial Complexity SparseDiv SparseDiv.StringArith SparseGcd SparseGcd.TermsStr

def primePolynomialCoeffStr (p h i : List Bool) : List Bool := redStr (blockAtStr i h) p

def primePolynomialDerivativeCoeffStr (p h i : List Bool) : List Bool :=
  let j := canonBits (addBits i [true])
  primeMulStr p (primePolynomialCoeffStr p h j) j

def primePolynomialDegreeStr (h : List Bool) : List Bool :=
  canonBits (subBits (blockCountStr h) [true])

/-- Every position in the explicit modulus list is a derivative-degree candidate. -/
def denseExponentsStr (h : List Bool) : List Bool :=
  mapBlocks unaryToBinStr (vectorIndicesStr h)

def primePolynomialDerivativeDegreeStr (p h : List Bool) : List Bool :=
  degreeScanStr (fun i ↦ isZeroBits (primePolynomialDerivativeCoeffStr p h i))
    (denseExponentsStr h)

theorem cobham_primePolynomialCoeffStr {n : ℕ} {p h i : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (hh : Cobham h) (hi : Cobham i) :
    Cobham fun v ↦ primePolynomialCoeffStr (p v) (h v) (i v) :=
  cobham_redStr_comp (cobham_blockAtStr hi hh) hp

theorem cobham_primePolynomialDerivativeCoeffStr {n : ℕ}
    {p h i : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (hh : Cobham h) (hi : Cobham i) :
    Cobham fun v ↦ primePolynomialDerivativeCoeffStr (p v) (h v) (i v) := by
  have hj := cobham_canonBits_comp (cobham_addBits_comp hi (.const [true]))
  exact cobham_primeMulStr_comp hp (cobham_primePolynomialCoeffStr hp hh hj) hj

theorem cobham_primePolynomialDegreeStr {n : ℕ} {h : (Fin n → List Bool) → List Bool}
    (hh : Cobham h) : Cobham fun v ↦ primePolynomialDegreeStr (h v) :=
  cobham_canonBits_comp (cobham_subBits_comp (cobham_blockCountStr hh) (.const [true]))

theorem cobham_denseExponentsStr {n : ℕ} {h : (Fin n → List Bool) → List Bool}
    (hh : Cobham h) : Cobham fun v ↦ denseExponentsStr (h v) := by
  exact TermsStr.cobham_mapBlocks_comp (F := fun b _ ↦ unaryToBinStr b)
    ((Cobham.comp cobham_unaryToBinStr (fun _ : Fin 1 ↦ Cobham.proj 0)).of_eq (fun _ ↦ rfl))
    (cobham_vectorIndicesStr_comp hh)

theorem cobham_primePolynomialDerivativeDegreeStr {n : ℕ}
    {p h : (Fin n → List Bool) → List Bool} (hp : Cobham p) (hh : Cobham h) :
    Cobham fun v ↦ primePolynomialDerivativeDegreeStr (p v) (h v) := by
  exact cobham_degreeScanStr
    (zero := fun v i ↦ isZeroBits (primePolynomialDerivativeCoeffStr (p v) (h v) i))
    (cobham_isZeroBits_comp (cobham_primePolynomialDerivativeCoeffStr
      (TermsStr.cobham_tail_comp hp) (TermsStr.cobham_tail_comp hh) (.proj 0)))
    (cobham_denseExponentsStr hh)

theorem primePolynomialCoeffStr_encoded (p : ℕ) [NeZero p] (h : List ℕ) (i : ℕ) :
    primePolynomialCoeffStr (encNat p) (encodeNumerals h) (encNat i) =
      encNat ((densePolynomial (R := ZMod p) h).coeff i).val := by
  rw [primePolynomialCoeffStr, encodeNumerals, blockAtStr_frame]
  have he : (h.map encNat).getD i [] = encNat (h.getD i 0) := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases h[i]? <;> rfl
  rw [he, redStr_eq_zmod_val, decNat_encNat, densePolynomial_coeff]

theorem primePolynomialDerivativeCoeffStr_encoded (p : ℕ) [NeZero p]
    (h : List ℕ) (i : ℕ) :
    primePolynomialDerivativeCoeffStr (encNat p) (encodeNumerals h) (encNat i) =
      encNat ((densePolynomial (R := ZMod p) h).derivative.coeff i).val := by
  unfold primePolynomialDerivativeCoeffStr
  have hj : canonBits (addBits (encNat i) [true]) = encNat (i + 1) := by
    rw [canonBits, decNat_addBits, decNat_encNat]
    rfl
  rw [hj]
  dsimp only
  rw [primePolynomialCoeffStr_encoded, primeMulStr_eq_zmod_val, decNat_encNat, decNat_encNat,
    ZMod.natCast_zmod_val, Polynomial.coeff_derivative]
  simp

theorem primePolynomialDegreeStr_correct (c : FieldCode) (hc : c.Structural) :
    primePolynomialDegreeStr (encodeNumerals c.modulus) = encNat c.degree := by
  rw [primePolynomialDegreeStr, encodeNumerals, blockCountStr_frame, canonBits,
    decNat_subBits, decNat_encNat, List.length_map, hc.degree_eq]
  rfl

theorem denseExponentsStr_encoded (h : List ℕ) :
    denseExponentsStr (encodeNumerals h) = encodeNumerals (List.range h.length) := by
  rw [denseExponentsStr, encodeNumerals, vectorIndicesStr_frame, mapBlocks_frame]
  simp only [List.length_map, List.map_map, Function.comp_def, unaryToBinStr_unaryN]
  rfl

theorem isZeroBits_encNat_zmod_val (p : ℕ) [NeZero p] (x : ZMod p) :
    isZeroBits (encNat x.val) = [decide (x = 0)] := by
  by_cases hx : x = 0
  · subst x
    simp [ZMod.val_zero]
    exact (isZeroBits_eq_true_iff _).mpr (by simp)
  · have hv : x.val ≠ 0 := fun h ↦ hx (ZMod.val_injective p (by simpa using h))
    simpa [hx] using isZeroBits_eq_false (p := encNat x.val) (by simpa using hv)

theorem primePolynomialDerivativeDegreeStr_correct (c : FieldCode) (hc : c.Structural)
    [Fact c.characteristic.Prime] :
    primePolynomialDerivativeDegreeStr (encNat c.characteristic) (encodeNumerals c.modulus) =
      encNat c.polynomial.derivative.natDegree := by
  rw [primePolynomialDerivativeDegreeStr, denseExponentsStr_encoded]
  apply degreeScanStr_polynomial c.polynomial.derivative
  · intro i
    rw [primePolynomialDerivativeCoeffStr_encoded, isZeroBits_encNat_zmod_val]
    rfl
  · intro i hi
    apply List.mem_range.mpr
    have hle := Polynomial.le_natDegree_of_ne_zero hi
    have hder := Polynomial.natDegree_derivative_le c.polynomial
    have hd := hc.degree_lt_length
    change c.polynomial.natDegree < c.modulus.length at hd
    omega

end SparseIrred.UpperBounds.Section4
