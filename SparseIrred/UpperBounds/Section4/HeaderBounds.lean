import SparseIrred.UpperBounds.Section4.FieldBounds
import SparseIrred.UpperBounds.Section4.Decision

/-!
# Structural header validation before irreducibility checking

The inexpensive checks here inspect only the natural-number input lists. They
already certify the degree, monicity, and representation bounds of the modulus;
no irreducibility or extension-field instance is needed for these facts.
-/

namespace SparseIrred.UpperBounds.Section4

open Polynomial Complexity SparseDiv

/-- A final digit one gives the actual leading coefficient in any nontrivial semiring. -/
theorem densePolynomial_monic_of_last_one {R : Type*} [Semiring R] [Nontrivial R]
    (a : List ℕ) (ha : a.getLast? = some 1) :
    (densePolynomial (R := R) a).Monic ∧
      (densePolynomial (R := R) a).natDegree = a.length - 1 := by
  have hc : (densePolynomial (R := R) a).coeff (a.length - 1) = 1 := by
    rw [densePolynomial_coeff, List.getD_eq_getElem?_getD,
      ← List.getLast?_eq_getElem?, ha]
    simp
  have hp : densePolynomial (R := R) a ≠ 0 := by
    intro hp
    rw [hp, Polynomial.coeff_zero] at hc
    exact zero_ne_one hc
  have hlow := Polynomial.le_natDegree_of_ne_zero (hc ▸ one_ne_zero)
  have hhigh := densePolynomial_natDegree_lt a hp
  have hdeg : (densePolynomial (R := R) a).natDegree = a.length - 1 := by omega
  refine ⟨?_, hdeg⟩
  change (densePolynomial (R := R) a).leadingCoeff = 1
  rw [Polynomial.leadingCoeff, hdeg, hc]

/-- Conditions that can be checked by reading the field header's natural digits. -/
structure FieldCode.Structural (c : FieldCode) : Prop where
  characteristic : 2 ≤ c.characteristic
  coefficients : ∀ a ∈ c.modulus, a < c.characteristic
  trailing : c.modulus.getLast? = some 1

/-- The cheap validation flag performs only comparisons and a scan of the modulus list. -/
def FieldCode.structuralFlag (c : FieldCode) : Bool :=
  decide (2 ≤ c.characteristic) &&
    c.modulus.all (fun a ↦ decide (a < c.characteristic)) &&
    decide (c.modulus.getLast? = some 1)

theorem FieldCode.structuralFlag_correct (c : FieldCode) :
    c.structuralFlag = true ↔ c.Structural := by
  simp only [structuralFlag, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨⟨hp, hc⟩, ht⟩
    exact ⟨hp, hc, ht⟩
  · intro h
    exact ⟨⟨h.characteristic, h.coefficients⟩, h.trailing⟩

theorem FieldCode.Valid.structural {c : FieldCode} (hc : c.Valid) : c.Structural :=
  ⟨hc.prime.two_le, hc.coefficients, hc.trailing⟩

theorem FieldCode.Structural.monic {c : FieldCode} (hc : c.Structural) :
    c.polynomial.Monic := by
  have : Fact (1 < c.characteristic) := ⟨by have := hc.characteristic; omega⟩
  exact (densePolynomial_monic_of_last_one c.modulus hc.trailing).1

theorem FieldCode.Structural.degree_eq {c : FieldCode} (hc : c.Structural) :
    c.degree = c.modulus.length - 1 := by
  have : Fact (1 < c.characteristic) := ⟨by have := hc.characteristic; omega⟩
  exact (densePolynomial_monic_of_last_one c.modulus hc.trailing).2

theorem FieldCode.Structural.modulus_nonempty {c : FieldCode} (hc : c.Structural) :
    c.modulus ≠ [] := by
  intro h
  simpa [h] using hc.trailing

theorem FieldCode.Structural.degree_lt_length {c : FieldCode} (hc : c.Structural) :
    c.degree < c.modulus.length := by
  rw [hc.degree_eq]
  have := List.length_pos_iff.mpr hc.modulus_nonempty
  omega

/-- Canonical element lengths can be checked before constructing the extension field. -/
theorem FieldCode.Structural.canonicalElement_iff {c : FieldCode} (hc : c.Structural)
    (a : List ℕ) : c.CanonicalElement a ↔
      a.length = c.modulus.length - 1 ∧ ∀ b ∈ a, b < c.characteristic := by
  rw [FieldCode.CanonicalElement, hc.degree_eq]

theorem Input.header_degree_le (x : Input) (hc : x.field.Structural) :
    x.field.degree ≤ x.encode.length :=
  (Nat.le_of_lt hc.degree_lt_length).trans x.modulus_length_le

theorem Input.header_degree_size_le (x : Input) (hc : x.field.Structural) :
    x.field.degree.size ≤ x.encode.length :=
  (Nat.size_le.mpr Nat.lt_two_pow_self).trans (x.header_degree_le hc)

/-- A prime-field scalar already has a short canonical digit before the extension
modulus has passed its irreducibility test. -/
theorem FieldCode.Structural.zmod_scalar_size_le {c : FieldCode} (hc : c.Structural)
    (a : ZMod c.characteristic) : a.val.size ≤ c.characteristic.size := by
  have : NeZero c.characteristic := ⟨by have := hc.characteristic; omega⟩
  exact Nat.size_le_size (Nat.le_of_lt (ZMod.val_lt a))

theorem Input.header_scalar_bits_le (x : Input) (hc : x.field.Structural)
    (a : ZMod x.field.characteristic) : (encNat a.val).length ≤ x.encode.length := by
  rw [length_encNat]
  exact hc.zmod_scalar_size_le a |>.trans x.characteristic_size_le

/-- All candidate extension scalars have a polynomial-length encoding already
after the structural check, before their modulus is proved irreducible. -/
theorem Input.header_candidate_element_bits_le (x : Input) (hc : x.field.Structural)
    (a : List ℕ) (ha : x.field.CanonicalElement a) :
    (encodeNumerals a).length ≤ 2 * x.encode.length ^ 2 + 2 * x.encode.length := by
  have h := x.field.canonical_element_length_le a ha
  have hm := Nat.mul_le_mul
    (show 2 * x.field.characteristic.size + 2 ≤ 2 * x.encode.length + 2 by
      have := x.characteristic_size_le
      omega)
    (x.header_degree_le hc)
  nlinarith

/-- The staged header checker first performs the cheap shape scan, then trial
division, and only then invokes the determinant test over the prime field. -/
noncomputable def FieldCode.stagedHeaderDecision (c : FieldCode) : Bool := by
  classical
  exact if c.structuralFlag then
    if hp : trialPrimeFlag c.characteristic = true then
      letI : Fact c.characteristic.Prime := ⟨(trialPrimeFlag_correct _).mp hp⟩
      coefficientOracleDecision c.polynomial
    else false
  else false

theorem FieldCode.stagedHeaderDecision_correct (c : FieldCode) :
    c.stagedHeaderDecision = true ↔ c.Valid := by
  classical
  by_cases hs : c.structuralFlag = true
  · have hc := (c.structuralFlag_correct).mp hs
    by_cases hp : trialPrimeFlag c.characteristic = true
    · have hprime := (trialPrimeFlag_correct _).mp hp
      have : Fact c.characteristic.Prime := ⟨hprime⟩
      simp only [stagedHeaderDecision, hs, ↓reduceIte, dite_eq_left hp]
      rw [coefficientOracleDecision_correct]
      exact ⟨fun hi ↦ ⟨hprime, hc.monic, hi, hc.coefficients, hc.trailing⟩,
        fun h ↦ h.irreducible⟩
    · have hn : ¬c.Valid := fun h ↦ hp ((trialPrimeFlag_correct _).mpr h.prime)
      simp [stagedHeaderDecision, hs, hp, hn]
  · have hn : ¬c.Valid := fun h ↦ hs (c.structuralFlag_correct.mpr h.structural)
    simp [stagedHeaderDecision, hs, hn]

theorem FieldCode.stagedHeaderDecision_eq (c : FieldCode) :
    c.stagedHeaderDecision = c.headerDecision := by
  apply Bool.eq_iff_iff.mpr
  rw [c.stagedHeaderDecision_correct, c.headerDecision_correct]

end SparseIrred.UpperBounds.Section4
