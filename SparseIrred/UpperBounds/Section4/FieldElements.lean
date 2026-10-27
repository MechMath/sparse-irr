import SparseIrred.UpperBounds.Section4.Encoding
import Mathlib.Data.List.OfFn

/-!
# Canonical coefficient vectors for the encoded finite field

Each presented field element has exactly one vector of `degree` base-prime digits.
The forward encoding extracts the actual quotient power-basis coordinates, and the
decoding is the polynomial evaluation already used by the sparse input language.
-/

namespace SparseIrred.UpperBounds.Section4

open Polynomial

/-- The monic quotient basis, used to read reduced polynomial coefficients. -/
noncomputable def FieldCode.coordinateBasis (c : FieldCode) [Fact c.Valid] :
    Module.Basis (Fin c.degree) (ZMod c.characteristic) c.Carrier :=
  AdjoinRoot.powerBasisAux' (Fact.out : c.Valid).monic

theorem FieldCode.coordinateBasis_eq (c : FieldCode) [Fact c.Valid] :
    c.coordinateBasis = c.powerBasis.basis := by
  ext i
  exact ((AdjoinRoot.powerBasis' (Fact.out : c.Valid).monic).basis_eq_pow i).trans
    (c.powerBasis.basis_eq_pow i).symm

/-- A short coefficient vector is already reduced modulo the field polynomial. -/
theorem FieldCode.densePolynomial_mod_eq_self (c : FieldCode) [Fact c.Valid]
    (a : List ℕ) (hlen : a.length ≤ c.degree) :
    densePolynomial (R := ZMod c.characteristic) a %ₘ c.polynomial = densePolynomial a := by
  apply (Polynomial.modByMonic_eq_self_iff (Fact.out : c.Valid).monic).mpr
  by_cases ha : densePolynomial (R := ZMod c.characteristic) a = 0
  · rw [ha, Polynomial.degree_zero]
    exact bot_lt_iff_ne_bot.mpr
      (Polynomial.degree_ne_bot.mpr (Fact.out : Irreducible c.polynomial).ne_zero)
  · apply Polynomial.degree_lt_degree
    exact (densePolynomial_natDegree_lt a ha).trans_le hlen

/-- The coordinates of a short vector are exactly its digits modulo the prime. -/
theorem FieldCode.coordinateBasis_element (c : FieldCode) [Fact c.Valid]
    (a : List ℕ) (hlen : a.length ≤ c.degree) (i : Fin c.degree) :
    c.coordinateBasis.repr (c.element a) i = (a.getD i.val 0 : ZMod c.characteristic) := by
  change (AdjoinRoot.modByMonicHom (Fact.out : c.Valid).monic
    (AdjoinRoot.mk c.polynomial (densePolynomial a))).coeff i.val = _
  rw [AdjoinRoot.modByMonicHom_mk,
    c.densePolynomial_mod_eq_self a hlen, densePolynomial_coeff]

/-- Fixed-length, low-degree-first canonical coordinates. -/
noncomputable def FieldCode.encodeElement (c : FieldCode) [Fact c.Valid]
    (x : c.Carrier) : List ℕ :=
  List.ofFn (fun i : Fin c.degree ↦ (c.coordinateBasis.repr x i).val)

theorem FieldCode.encodeElement_canonical (c : FieldCode) [Fact c.Valid] (x : c.Carrier) :
    c.CanonicalElement (c.encodeElement x) := by
  constructor
  · simp [encodeElement]
  · intro b hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    exact ZMod.val_lt _

theorem FieldCode.element_encodeElement (c : FieldCode) [Fact c.Valid] (x : c.Carrier) :
    c.element (c.encodeElement x) = x := by
  apply c.coordinateBasis.repr.injective
  ext i
  rw [c.coordinateBasis_element _ (c.encodeElement_canonical x).1.le]
  simp [encodeElement]

theorem FieldCode.encodeElement_element (c : FieldCode) [Fact c.Valid]
    (a : List ℕ) (ha : c.CanonicalElement a) :
    c.encodeElement (c.element a) = a := by
  apply List.ext_getElem
  · simp [encodeElement, ha.1]
  · intro i hi hj
    have hidx : i < c.degree := by simpa [encodeElement] using hi
    simp only [encodeElement, List.getElem_ofFn]
    rw [c.coordinateBasis_element a ha.1.le]
    rw [List.getD_eq_getElem a 0 hj, ZMod.val_natCast_of_lt (ha.2 _ (List.getElem_mem hj))]

/-- Decoding canonical coefficient vectors is a bijection onto the represented field. -/
noncomputable def FieldCode.elementEquiv (c : FieldCode) [Fact c.Valid] :
    {a : List ℕ // c.CanonicalElement a} ≃ c.Carrier where
  toFun a := c.element a.val
  invFun x := ⟨c.encodeElement x, c.encodeElement_canonical x⟩
  left_inv a := Subtype.ext (c.encodeElement_element a.val a.property)
  right_inv x := c.element_encodeElement x

theorem FieldCode.element_injective_on_canonical (c : FieldCode) [Fact c.Valid]
    {a b : List ℕ} (ha : c.CanonicalElement a) (hb : c.CanonicalElement b) :
    c.element a = c.element b ↔ a = b := by
  constructor
  · intro h
    simpa only [c.encodeElement_element a ha, c.encodeElement_element b hb] using
      congrArg c.encodeElement h
  · exact congrArg c.element

/-- The canonical zero vector has exactly the presentation's extension degree. -/
theorem FieldCode.encodeElement_zero (c : FieldCode) [Fact c.Valid] :
    c.encodeElement 0 = List.replicate c.degree 0 := by
  simp [encodeElement]

theorem FieldCode.element_zero_vector (c : FieldCode) [Fact c.Valid] :
    c.element (List.replicate c.degree 0) = 0 := by
  rw [← c.encodeElement_zero]
  exact c.element_encodeElement 0

theorem densePolynomial_replicate_zero {R : Type*} [Semiring R] (n : ℕ) :
    densePolynomial (R := R) (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, densePolynomial, ih]

/-- The coefficient vector of the multiplicative identity. -/
noncomputable def FieldCode.oneElement (c : FieldCode) : List ℕ :=
  1 :: List.replicate (c.degree - 1) 0

theorem FieldCode.oneElement_canonical (c : FieldCode) [Fact c.Valid] :
    c.CanonicalElement c.oneElement := by
  constructor
  · simp only [oneElement, List.length_cons, List.length_replicate]
    have := c.degree_pos
    omega
  · intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact (Fact.out : c.Valid).prime.one_lt
    · have : b = 0 := (List.mem_replicate.mp hb).2
      rw [this]
      exact (Fact.out : c.Valid).prime.pos

theorem FieldCode.element_oneElement (c : FieldCode) [Fact c.Valid] :
    c.element c.oneElement = 1 := by
  simp [element, oneElement, densePolynomial, densePolynomial_replicate_zero]
  rfl

/-- Coordinatewise addition, reducing each digit modulo the characteristic. -/
noncomputable def FieldCode.addElements (c : FieldCode) (a b : List ℕ) : List ℕ :=
  List.ofFn (fun i : Fin c.degree ↦ (a.getD i.val 0 + b.getD i.val 0) % c.characteristic)

theorem FieldCode.addElements_canonical (c : FieldCode) [Fact c.Valid] (a b : List ℕ) :
    c.CanonicalElement (c.addElements a b) := by
  constructor
  · simp [addElements]
  · intro v hv
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
    exact Nat.mod_lt _ (Fact.out : c.Valid).prime.pos

theorem FieldCode.element_addElements (c : FieldCode) [Fact c.Valid]
    (a b : List ℕ) (ha : a.length ≤ c.degree) (hb : b.length ≤ c.degree) :
    c.element (c.addElements a b) = c.element a + c.element b := by
  apply c.coordinateBasis.repr.injective
  ext i
  rw [c.coordinateBasis_element _ (c.addElements_canonical a b).1.le]
  simp only [map_add, Finsupp.add_apply, c.coordinateBasis_element a ha,
    c.coordinateBasis_element b hb]
  simp [addElements, ZMod.natCast_mod]

/-- Canonical coefficients of a polynomial reduced modulo the presentation. -/
noncomputable def FieldCode.reduceCoefficients (c : FieldCode)
    (p : (ZMod c.characteristic)[X]) : List ℕ :=
  List.ofFn (fun i : Fin c.degree ↦ ((p %ₘ c.polynomial).coeff i.val).val)

theorem FieldCode.reduceCoefficients_eq_encode (c : FieldCode) [Fact c.Valid]
    (p : (ZMod c.characteristic)[X]) :
    c.reduceCoefficients p = c.encodeElement (AdjoinRoot.mk c.polynomial p) := rfl

theorem FieldCode.reduceCoefficients_canonical (c : FieldCode) [Fact c.Valid]
    (p : (ZMod c.characteristic)[X]) : c.CanonicalElement (c.reduceCoefficients p) := by
  rw [c.reduceCoefficients_eq_encode]
  exact c.encodeElement_canonical _

theorem FieldCode.element_reduceCoefficients (c : FieldCode) [Fact c.Valid]
    (p : (ZMod c.characteristic)[X]) :
    c.element (c.reduceCoefficients p) = AdjoinRoot.mk c.polynomial p := by
  rw [c.reduceCoefficients_eq_encode]
  exact c.element_encodeElement _

/-- Multiplication by polynomial convolution followed by reduction modulo the
presentation; all output coefficients are base-prime digits. -/
noncomputable def FieldCode.mulElements (c : FieldCode) (a b : List ℕ) : List ℕ :=
  c.reduceCoefficients (densePolynomial a * densePolynomial b)

theorem FieldCode.mulElements_canonical (c : FieldCode) [Fact c.Valid] (a b : List ℕ) :
    c.CanonicalElement (c.mulElements a b) :=
  c.reduceCoefficients_canonical _

theorem FieldCode.element_mulElements (c : FieldCode) [Fact c.Valid] (a b : List ℕ) :
    c.element (c.mulElements a b) = c.element a * c.element b := by
  rw [mulElements, c.element_reduceCoefficients, map_mul]
  rfl

/-- Additive negation followed by canonical reduction. -/
noncomputable def FieldCode.negElement (c : FieldCode) (a : List ℕ) : List ℕ :=
  c.reduceCoefficients (-densePolynomial a)

theorem FieldCode.negElement_canonical (c : FieldCode) [Fact c.Valid] (a : List ℕ) :
    c.CanonicalElement (c.negElement a) :=
  c.reduceCoefficients_canonical _

theorem FieldCode.element_negElement (c : FieldCode) [Fact c.Valid] (a : List ℕ) :
    c.element (c.negElement a) = -c.element a := by
  rw [negElement, c.element_reduceCoefficients, map_neg]
  rfl

end SparseIrred.UpperBounds.Section4
