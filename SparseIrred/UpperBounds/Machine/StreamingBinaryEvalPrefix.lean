import SparseIrred.UpperBounds.Machine.StreamingBinaryEvalSemantics
import SparseIrred.UpperBounds.Machine.StreamingBinaryInput
import SparseDivComplexity.Appendix.IntTermsString

/-! # Prefix invariants for the bounded sparse-input traversal -/

namespace SparseIrred.UpperBounds.Machine

open Complexity SparseDiv SparseDiv.Appendix SparseDiv.StringArith

theorem signedEvalFold_append (deriv : Bool) (a m : ℕ) (l₁ l₂ : ITerms) (acc : ℕ × ℕ) :
    signedEvalFold deriv a m (l₁ ++ l₂) acc =
      signedEvalFold deriv a m l₂ (signedEvalFold deriv a m l₁ acc) :=
  List.foldl_append

theorem signedEvalFold_take_succ (deriv : Bool) (a m : ℕ) (l : ITerms) (i : ℕ)
    (t : ℤ × ℕ) (tail : ITerms) (hdrop : l.drop i = t :: tail) (acc : ℕ × ℕ) :
    signedEvalFold deriv a m (l.take (i + 1)) acc =
      signedEvalStep deriv a m (signedEvalFold deriv a m (l.take i) acc) t := by
  rw [List.take_add, hdrop, signedEvalFold_append]
  rfl

theorem drop_succ_of_drop_cons (l : ITerms) (i : ℕ) (t : ℤ × ℕ) (tail : ITerms)
    (hdrop : l.drop i = t :: tail) : l.drop (i + 1) = tail := by
  rw [← List.drop_drop, hdrop]
  rfl

theorem signedEvalFold_take_of_drop_nil (deriv : Bool) (a m : ℕ) (l : ITerms) (i : ℕ)
    (hdrop : l.drop i = []) (acc : ℕ × ℕ) :
    signedEvalFold deriv a m (l.take i) acc = signedEvalFold deriv a m l acc := by
  rw [List.take_of_length_le (List.drop_eq_nil_iff.mp hdrop)]

theorem input_length_le_packedInput (x : List Bool) : x.length ≤ packedInput x := by
  have hsize : (packedInput x).size ≤ packedInput x := by
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  rw [packedInput_size] at hsize
  omega

/-- The packed table is a sufficient finite bound for traversing all its sparse terms. -/
theorem terms_length_le_packedInput (l : ITerms) : l.length ≤ packedInput (encITerms l) := by
  apply le_trans _ (input_length_le_packedInput _)
  induction l with
  | nil => simp
  | cons t l ih =>
    simp only [encITerms, frame, List.map_cons, List.flatten_cons,
      List.length_cons, List.length_append] at *
    have hlen : 1 ≤ (delimit (encITerm t)).length := by
      rw [delimit_length]
      omega
    omega

theorem signedEvalFold_take_succ_of_drop_nil (deriv : Bool) (a m : ℕ) (l : ITerms) (i : ℕ)
    (hdrop : l.drop i = []) (acc : ℕ × ℕ) :
    signedEvalFold deriv a m (l.take (i + 1)) acc = signedEvalFold deriv a m (l.take i) acc := by
  have hi := List.drop_eq_nil_iff.mp hdrop
  rw [List.take_of_length_le hi, List.take_of_length_le (by omega)]

theorem packedInput_eq_one_iff (x : List Bool) : packedInput x = 1 ↔ x = [] := by
  constructor
  · intro h
    have hs := packedInput_size x
    rw [h] at hs
    have hx : x.length = 0 := by
      rw [show Nat.size 1 = 1 by decide] at hs
      omega
    exact List.length_eq_zero_iff.mp hx
  · rintro rfl
    exact packedInput_nil

/-- The sentinel equals one precisely after the entire sparse table is consumed. -/
theorem packedTerms_eq_one_iff (l : ITerms) : packedInput (encITerms l) = 1 ↔ l = [] := by
  rw [packedInput_eq_one_iff]
  constructor
  · intro h
    have hh := congrArg decITerms h
    simpa [show ([] : List Bool) = encITerms [] from rfl] using hh
  · rintro rfl
    rfl

/-- Removing an initial bitstring never increases its sentinel-terminated numeric value. -/
theorem packedInput_append_right_le (x y : List Bool) :
    packedInput y ≤ packedInput (x ++ y) := by
  induction x with
  | nil => simp
  | cons b x ih =>
    simp only [List.cons_append, packedInput_cons]
    split_ifs <;> omega

theorem packedTerms_tail_le (t : ℤ × ℕ) (l : ITerms) :
    packedInput (encITerms l) ≤ packedInput (encITerms (t :: l)) := by
  simp only [encITerms, frame, List.map_cons, List.flatten_cons]
  exact packedInput_append_right_le _ _

end SparseIrred.UpperBounds.Machine
