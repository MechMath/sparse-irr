import SparseIrred.UpperBounds.Section4.InputBounds
import SparseIrred.UpperBounds.Section4.FieldElements

/-! # Bit space for the concrete field-element representation -/

namespace SparseIrred.UpperBounds.Section4

open Polynomial Complexity SparseDiv SparseDiv.StringArith

theorem encodeNumerals_length_le (as : List ℕ) (w : ℕ)
    (h : ∀ a ∈ as, a.size ≤ w) : (encodeNumerals as).length ≤ (2 * w + 2) * as.length := by
  induction as with
  | nil => simp [encodeNumerals, frame_nil]
  | cons a as ih =>
      have ha := h a (by simp)
      have hi := ih (fun a ha ↦ h a (by simp [ha]))
      simp only [encodeNumerals, List.map_cons, frame_cons, List.length_append,
        delimit_length, length_encNat] at *
      simp only [List.length_cons]
      nlinarith

theorem FieldCode.canonical_element_length_le (c : FieldCode) (a : List ℕ)
    (ha : c.CanonicalElement a) :
    (encodeNumerals a).length ≤ (2 * c.characteristic.size + 2) * c.degree := by
  rw [← ha.1]
  exact encodeNumerals_length_le _ _
    (fun b hb ↦ Nat.size_le_size (Nat.le_of_lt (ha.2 b hb)))

/-- All intermediate scalars fit this bound, independently of how many arithmetic
operations the determinant evaluation performs. -/
theorem Input.scalar_encoding_length_le (x : Input) [Fact x.field.Valid]
    (a : x.field.Carrier) :
    (encodeNumerals (x.field.encodeElement a)).length ≤
      2 * x.encode.length ^ 2 + 2 * x.encode.length := by
  have h := x.field.canonical_element_length_le _ (x.field.encodeElement_canonical a)
  have hc := x.characteristic_size_le
  have hd := x.field_degree_le
  have hm := Nat.mul_le_mul (show 2 * x.field.characteristic.size + 2 ≤
    2 * x.encode.length + 2 by omega) hd
  nlinarith

/-- The concrete scalar representation is faithful; equality tests on encoded
scalars therefore agree with equality in the actual finite field. -/
theorem FieldCode.scalar_encoding_injective (c : FieldCode) [Fact c.Valid] :
    Function.Injective (fun a : c.Carrier ↦ encodeNumerals (c.encodeElement a)) := by
  intro a b hab
  have h := congrArg decodeNumerals hab
  simp only [decodeNumerals_encode] at h
  have := congrArg c.element h
  simpa only [c.element_encodeElement] using this

end SparseIrred.UpperBounds.Section4
