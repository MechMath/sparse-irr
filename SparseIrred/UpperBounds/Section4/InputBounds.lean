import SparseIrred.UpperBounds.Section4.Encoding

/-!
# Binary size bounds for the uniform field and sparse polynomial input

These inequalities refer to the actual binary encoding. In particular neither
the field cardinality nor the polynomial degree is assumed polynomially bounded.
Only their bit lengths are polynomially bounded.
-/

namespace SparseIrred.UpperBounds.Section4

open Polynomial Complexity SparseDiv SparseDiv.StringArith

theorem pairFst_length_le : ∀ s : List Bool, (pairFst s).length ≤ s.length
  | [] => by simp [pairFst]
  | [b] => by cases b <;> simp [pairFst]
  | false :: false :: s => by have := pairFst_length_le s; simp [pairFst]; omega
  | true :: true :: s => by have := pairFst_length_le s; simp [pairFst]; omega
  | false :: true :: s => by simp [pairFst]
  | true :: false :: s => by simp [pairFst]

/-- Even a malformed input cannot hide a characteristic with more input bits. -/
theorem Input.decoded_characteristic_size_le (s : List Bool) :
    (Input.decode s).field.characteristic.size ≤ s.length := by
  change (decNat (pairFst s)).size ≤ s.length
  exact (Nat.size_le.mpr (decNat_lt_two_pow_length _)).trans (pairFst_length_le s)

theorem length_le_encodeNumerals_length (as : List ℕ) :
    as.length ≤ (encodeNumerals as).length := by
  simpa only [encodeNumerals, List.length_map] using length_le_length_frame (as.map encNat)

theorem size_le_encodeNumerals_length {as : List ℕ} {a : ℕ} (h : a ∈ as) :
    a.size ≤ (encodeNumerals as).length := by
  have := two_mul_length_add_two_le_of_mem_frame
    (b := encNat a) (bs := as.map encNat) (List.mem_map.mpr ⟨a, h, rfl⟩)
  change 2 * (encNat a).length + 2 ≤ (frame (as.map encNat)).length at this
  rw [length_encNat] at this
  change a.size ≤ (frame (as.map encNat)).length
  omega

theorem Input.characteristic_size_le (x : Input) :
    x.field.characteristic.size ≤ x.encode.length := by
  simp only [Input.encode, pair_length, length_encNat]
  omega

theorem Input.modulus_length_le (x : Input) :
    x.field.modulus.length ≤ x.encode.length := by
  have := length_le_encodeNumerals_length x.field.modulus
  simp only [Input.encode, pair_length, length_encNat]
  omega

theorem Input.terms_length_le (x : Input) : x.terms.length ≤ x.encode.length := by
  have := length_le_length_frame (x.terms.map encodeTerm)
  simp only [List.length_map] at this
  simp only [Input.encode, pair_length, length_encNat]
  omega

theorem Input.term_length_le (x : Input) {t : List ℕ × ℕ} (ht : t ∈ x.terms) :
    (encodeTerm t).length ≤ x.encode.length := by
  have := two_mul_length_add_two_le_of_mem_frame
    (b := encodeTerm t) (bs := x.terms.map encodeTerm) (List.mem_map.mpr ⟨t, ht, rfl⟩)
  change 2 * (encodeTerm t).length + 2 ≤ (frame (x.terms.map encodeTerm)).length at this
  simp only [Input.encode, pair_length, length_encNat]
  omega

theorem Input.exponent_size_le (x : Input) {t : List ℕ × ℕ} (ht : t ∈ x.terms) :
    t.2.size ≤ x.encode.length := by
  have := x.term_length_le ht
  simp only [encodeTerm, pair_length, length_encNat] at this
  omega

theorem Input.exponent_lt (x : Input) {t : List ℕ × ℕ} (ht : t ∈ x.terms) :
    t.2 < 2 ^ x.encode.length := Nat.size_le.mp (x.exponent_size_le ht)

theorem FieldCode.sparsePolynomial_natDegree_lt (c : FieldCode) (ts : SparseTerms)
    {b : ℕ} (hb : 0 < b) (ht : ∀ t ∈ ts, t.2 < b) :
    (c.sparsePolynomial ts).natDegree < b := by
  induction ts with
  | nil => simpa [FieldCode.sparsePolynomial] using hb
  | cons t ts ih =>
      have ht' := ht t (by simp)
      have hi := ih (fun t h ↦ ht t (by simp [h]))
      apply lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ hi)
      exact (natDegree_monomial_le _).trans_lt ht'

theorem Input.polynomial_degree_lt (x : Input) :
    (x.field.sparsePolynomial x.terms).natDegree < 2 ^ x.encode.length :=
  x.field.sparsePolynomial_natDegree_lt x.terms (by positivity) (fun _ ↦ x.exponent_lt)

theorem Input.polynomial_degree_size_le (x : Input) :
    (x.field.sparsePolynomial x.terms).natDegree.size ≤ x.encode.length :=
  Nat.size_le.mpr x.polynomial_degree_lt

theorem Input.field_degree_le (x : Input) [Fact x.field.Valid] :
    x.field.degree ≤ x.encode.length :=
  (Nat.le_of_lt x.field.degree_lt_modulus_length).trans x.modulus_length_le

/-- Exponentiation may produce a huge number, but its binary length is at most
the product of the exponent and the base's bit length, plus one for exponent zero. -/
theorem size_pow_le (a b : ℕ) : (a ^ b).size ≤ a.size * b + 1 := by
  apply Nat.size_le.mpr
  have h : a ^ b ≤ (2 ^ a.size) ^ b := Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_size_self a)) b
  rw [← pow_mul] at h
  exact h.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))

theorem Input.field_card_size_le (x : Input) [Fact x.field.Valid] :
    (Fintype.card x.field.Carrier).size ≤ x.encode.length ^ 2 + 1 := by
  rw [FieldCode.card_carrier]
  apply (size_pow_le _ _).trans
  have := Nat.mul_le_mul x.characteristic_size_le x.field_degree_le
  nlinarith

/-- The large exponent used to read Frobenius column `j` still has polynomially
many bits. This is the exponent `q*j` in equation (48). -/
theorem Input.frobenius_exponent_size_le (x : Input) [Fact x.field.Valid] {j : ℕ}
    (hj : j < (x.field.sparsePolynomial x.terms).natDegree) :
    (Fintype.card x.field.Carrier * j).size ≤ x.encode.length ^ 2 + x.encode.length + 1 := by
  apply Nat.size_le.mpr
  have hq := Nat.size_le.mp x.field_card_size_le
  have hj' := hj.trans x.polynomial_degree_lt
  have hprod := Nat.mul_lt_mul_of_lt_of_lt hq hj'
  simpa only [← pow_add, Nat.add_right_comm] using hprod

end SparseIrred.UpperBounds.Section4
