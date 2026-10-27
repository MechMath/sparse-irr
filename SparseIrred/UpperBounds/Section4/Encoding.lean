import SparseIrred.UpperBounds.FiniteFieldTest
import SparseDivComplexity.StringArith.Blocks
import SparseDivComplexity.Encoding

/-!
# Uniform binary inputs for finite-field sparse irreducibility

A field is presented by a binary prime and a dense monic irreducible polynomial
over that prime field. Elements are coefficient vectors in its power basis.
Both the characteristic and extension degree are part of the input; the final
language is not restricted to one hardwired finite field.
-/

namespace SparseIrred.UpperBounds.Section4

open Polynomial Complexity SparseDiv SparseDiv.StringArith
open scoped BigOperators

/-- Low-degree-first natural coefficients interpreted in a semiring. -/
noncomputable def densePolynomial {R : Type*} [Semiring R] : List ℕ → R[X]
  | [] => 0
  | a :: as => C (a : R) + X * densePolynomial as

theorem densePolynomial_coeff {R : Type*} [Semiring R] (as : List ℕ) (i : ℕ) :
    (densePolynomial (R := R) as).coeff i = (as.getD i 0 : R) := by
  induction as generalizing i with
  | nil => simp [densePolynomial]
  | cons a as ih =>
      cases i <;> simp [densePolynomial, ih, coeff_X_mul]

theorem densePolynomial_natDegree_lt {R : Type*} [Semiring R] (as : List ℕ)
    (h : densePolynomial (R := R) as ≠ 0) : (densePolynomial (R := R) as).natDegree < as.length := by
  by_contra hlen
  have hc := leadingCoeff_ne_zero.mpr h
  rw [leadingCoeff, densePolynomial_coeff,
    List.getD_eq_default as 0 (Nat.le_of_not_gt hlen), Nat.cast_zero] at hc
  exact hc rfl

/-- A standard power-basis presentation, with no field table in the input. -/
structure FieldCode where
  characteristic : ℕ
  modulus : List ℕ
  deriving DecidableEq

noncomputable def FieldCode.polynomial (c : FieldCode) : (ZMod c.characteristic)[X] :=
  densePolynomial c.modulus

/-- Validity of a field description is mathematical data, not an extra axiom. -/
structure FieldCode.Valid (c : FieldCode) : Prop where
  prime : c.characteristic.Prime
  monic : c.polynomial.Monic
  irreducible : Irreducible c.polynomial
  coefficients : ∀ a ∈ c.modulus, a < c.characteristic
  trailing : c.modulus.getLast? = some 1

instance fieldCode_prime (c : FieldCode) [Fact c.Valid] : Fact c.characteristic.Prime :=
  ⟨(Fact.out : c.Valid).prime⟩

instance fieldCode_irreducible (c : FieldCode) [Fact c.Valid] : Fact (Irreducible c.polynomial) :=
  ⟨(Fact.out : c.Valid).irreducible⟩

def FieldCode.Carrier (c : FieldCode) := AdjoinRoot c.polynomial

noncomputable instance fieldCode_commRing (c : FieldCode) : CommRing c.Carrier :=
  inferInstanceAs (CommRing (AdjoinRoot c.polynomial))

noncomputable instance fieldCode_field (c : FieldCode) [Fact c.Valid] : Field c.Carrier :=
  inferInstanceAs (Field (AdjoinRoot c.polynomial))

noncomputable instance fieldCode_algebra (c : FieldCode) : Algebra (ZMod c.characteristic) c.Carrier :=
  inferInstanceAs (Algebra (ZMod c.characteristic) (AdjoinRoot c.polynomial))

noncomputable def FieldCode.degree (c : FieldCode) : ℕ := c.polynomial.natDegree

noncomputable def FieldCode.powerBasis (c : FieldCode) [Fact c.Valid] :
    PowerBasis (ZMod c.characteristic) c.Carrier :=
  AdjoinRoot.powerBasis (Fact.out : Irreducible c.polynomial).ne_zero

noncomputable instance fieldCode_fintype (c : FieldCode) [Fact c.Valid] : Fintype c.Carrier :=
  Fintype.ofEquiv (Fin c.degree → ZMod c.characteristic) c.powerBasis.basis.equivFun.symm.toEquiv

theorem FieldCode.card_carrier (c : FieldCode) [Fact c.Valid] :
    Fintype.card c.Carrier = c.characteristic ^ c.degree := by
  rw [Fintype.card_congr c.powerBasis.basis.equivFun.toEquiv]
  simp [FieldCode.powerBasis, FieldCode.degree]

theorem FieldCode.degree_pos (c : FieldCode) [Fact c.Valid] : 0 < c.degree :=
  (Fact.out : Irreducible c.polynomial).natDegree_pos

theorem FieldCode.degree_lt_modulus_length (c : FieldCode) [Fact c.Valid] :
    c.degree < c.modulus.length :=
  densePolynomial_natDegree_lt _ (Fact.out : Irreducible c.polynomial).ne_zero

/-- The semantic value of a coefficient vector in the presented finite field. -/
noncomputable def FieldCode.element (c : FieldCode) (a : List ℕ) : c.Carrier :=
  AdjoinRoot.mk c.polynomial (densePolynomial a)

def FieldCode.CanonicalElement (c : FieldCode) (a : List ℕ) : Prop :=
  a.length = c.degree ∧ ∀ b ∈ a, b < c.characteristic

abbrev SparseTerms := List (List ℕ × ℕ)

noncomputable def FieldCode.sparsePolynomial (c : FieldCode) (terms : SparseTerms) : c.Carrier[X] :=
  terms.foldr (fun t f ↦ monomial t.2 (c.element t.1) + f) 0

/-- The characteristic, extension description, and sparse polynomial are encoded together. -/
structure Input where
  field : FieldCode
  terms : SparseTerms
  deriving DecidableEq

def encodeNumerals (as : List ℕ) : List Bool := frame (as.map encNat)
def decodeNumerals (s : List Bool) : List ℕ := (blocks s).map decNat

@[simp] theorem decodeNumerals_encode (as : List ℕ) : decodeNumerals (encodeNumerals as) = as := by
  simp [decodeNumerals, encodeNumerals, blocks_frame, List.map_map, Function.comp_def]

def encodeTerm (t : List ℕ × ℕ) : List Bool := pair (encodeNumerals t.1) (encNat t.2)
def decodeTerm (s : List Bool) : List ℕ × ℕ := (decodeNumerals (pairFst s), decNat (pairSnd s))

@[simp] theorem decodeTerm_encode (t : List ℕ × ℕ) : decodeTerm (encodeTerm t) = t := by
  simp [decodeTerm, encodeTerm]

def Input.encode (x : Input) : List Bool :=
  pair (encNat x.field.characteristic)
    (pair (encodeNumerals x.field.modulus) (frame (x.terms.map encodeTerm)))

def Input.decode (s : List Bool) : Input :=
  ⟨⟨decNat (pairFst s), decodeNumerals (pairFst (pairSnd s))⟩,
    (blocks (pairSnd (pairSnd s))).map decodeTerm⟩

@[simp] theorem Input.decode_encode (x : Input) : Input.decode x.encode = x := by
  cases x with
  | mk field terms =>
      cases field
      simp [Input.decode, Input.encode, blocks_frame, List.map_map, Function.comp_def]

theorem Input.encode_injective : Function.Injective Input.encode := by
  intro x y h
  simpa using congrArg Input.decode h

end SparseIrred.UpperBounds.Section4
