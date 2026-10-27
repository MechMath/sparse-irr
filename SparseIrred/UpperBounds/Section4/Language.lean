import SparseIrred.UpperBounds.Section4.Decision
import SparseIrred.UpperBounds.Section4.FieldBounds

/-!
# The uniform binary language in Theorem 18

The finite-field description is included in the input and is checked. Invalid
binary encodings and invalid field descriptions are rejected. Sparse terms may
be unordered, repeated, or zero: the interpretation adds all listed monomials.
-/

namespace SparseIrred.UpperBounds.Section4

open Polynomial Complexity

/-- Validity imposes canonical coefficient vectors, but no sortedness or
nonzero-term restriction on the sparse representation. -/
structure Input.Valid (x : Input) : Prop where
  field : x.field.Valid
  coefficients : ∀ t ∈ x.terms, x.field.CanonicalElement t.1

/-- The characteristic and extension degree are both input data. -/
def UniformIrredLang : Language :=
  {s | ∃ x : Input, x.encode = s ∧ x.Valid ∧ Irreducible (x.field.sparsePolynomial x.terms)}

theorem mem_UniformIrredLang_iff (s : List Bool) :
    s ∈ UniformIrredLang ↔
      (Input.decode s).encode = s ∧ (Input.decode s).Valid ∧
        Irreducible ((Input.decode s).field.sparsePolynomial (Input.decode s).terms) := by
  constructor
  · rintro ⟨x, rfl, hx, hi⟩
    rw [Input.decode_encode]
    exact ⟨rfl, hx, hi⟩
  · rintro ⟨hs, hv, hi⟩
    exact ⟨Input.decode s, hs, hv, hi⟩

theorem encode_mem_UniformIrredLang_iff (x : Input) :
    x.encode ∈ UniformIrredLang ↔ x.Valid ∧ Irreducible (x.field.sparsePolynomial x.terms) := by
  rw [mem_UniformIrredLang_iff, Input.decode_encode]
  simp only [true_and]

/-- The fully specified semantic decision, including header validation. Each
irreducibility call is the resultant-and-minors procedure, not an oracle for
the proposition `Irreducible`. Its machine-space theorem is proved separately. -/
noncomputable def uniformDecision (s : List Bool) : Bool := by
  classical
  let x := Input.decode s
  exact if x.encode = s then
    if hh : x.field.headerDecision = true then
      letI : Fact x.field.Valid := ⟨x.field.headerDecision_correct.mp hh⟩
      decide (∀ t ∈ x.terms, x.field.CanonicalElement t.1) &&
        coefficientOracleDecision (x.field.sparsePolynomial x.terms)
    else false
  else false

theorem uniformDecision_correct (s : List Bool) :
    uniformDecision s = true ↔ s ∈ UniformIrredLang := by
  classical
  rw [mem_UniformIrredLang_iff]
  unfold uniformDecision
  dsimp only
  split_ifs with he hh
  · have hv := (Input.decode s).field.headerDecision_correct.mp hh
    letI : Fact (Input.decode s).field.Valid := ⟨hv⟩
    rw [Bool.and_eq_true, decide_eq_true_eq, coefficientOracleDecision_correct]
    constructor
    · rintro ⟨hc, hi⟩
      exact ⟨he, ⟨hv, hc⟩, hi⟩
    · rintro ⟨_, hvalid, hi⟩
      exact ⟨hvalid.coefficients, hi⟩
  · simp only [Bool.false_eq_true, false_iff]
    rintro ⟨_, hv, _⟩
    exact hh ((Input.decode s).field.headerDecision_correct.mpr hv.field)
  · simp only [Bool.false_eq_true, false_iff]
    exact fun h ↦ he h.1

theorem uniformDecision_encode (x : Input) (hv : x.Valid) :
    uniformDecision x.encode = true ↔ Irreducible (x.field.sparsePolynomial x.terms) := by
  rw [uniformDecision_correct, encode_mem_UniformIrredLang_iff]
  simp only [hv, true_and]

end SparseIrred.UpperBounds.Section4
