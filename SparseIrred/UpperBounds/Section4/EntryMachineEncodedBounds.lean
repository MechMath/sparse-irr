import SparseIrred.UpperBounds.Section4.EntryMachineEncodedBerkowitz
import SparseIrred.UpperBounds.Section4.BerkowitzProgramBounds
import SparseIrred.UpperBounds.Section4.BerkowitzFrobeniusBounds

/-! # Binary address widths for the entire nested determinant computation -/

namespace SparseIrred.UpperBounds.Section4

open Complexity SparseDiv SparseDiv.StringArith

private theorem size_le_of_le_two_mul_add_ten (v N : ℕ) (hv : v ≤ 2 * N + 10) :
    v.size ≤ N.size + 4 := by
  apply Nat.size_le.mpr
  have hn := Nat.lt_size_self N
  have hp : 1 ≤ 2 ^ N.size := Nat.one_le_pow _ _ (by omega)
  rw [pow_add]
  norm_num
  omega

/-- Each address stores at most six registers, each bounded by the original intervals. -/
theorem ProductAddress.binaryCode_length_of_bounded {n : ℕ} (a : ProductAddress n)
    (bound N : ℕ) (ha : a.Bounded bound) (hb : bound ≤ N) (hn : n ≤ N) :
    a.binaryCode.length ≤ 14 * (N.size + 5) := by
  have hf : ∀ v ∈ a.fields, v ≤ 2 * N + 10 := by
    intro v hv
    cases a <;> simp only [Bounded, fields, List.mem_cons, List.not_mem_nil, or_false] at * <;> omega
  have hw := a.binaryCode_length (N.size + 4)
    (fun v hv ↦ size_le_of_le_two_mul_add_ten v N (hf v hv))
  nlinarith

theorem BerkowitzFactorAddress.binaryCode_length_of_bounded {n : ℕ}
    (a : BerkowitzFactorAddress n) (N : ℕ) (ha : a.Bounded) (hn : n ≤ N) :
    a.binaryCode.length ≤ 12 * (N.size + 5) := by
  have hf : ∀ v ∈ a.fields, v ≤ 2 * N + 10 := by
    intro v hv
    cases a <;> simp only [Bounded, fields, List.mem_cons, List.not_mem_nil, or_false] at * <;> omega
  have hw := a.binaryCode_length (N.size + 4)
    (fun v hv ↦ size_le_of_le_two_mul_add_ten v N (hf v hv))
  nlinarith

theorem berkowitzPowerCode_length_of_bounded {n : ℕ} (a : BerkowitzPowerAddress n)
    (N : ℕ) (ha : a.Bounded) (hn : n ≤ N) :
    (berkowitzPowerCode a).length ≤ 16 * (N.size + 5) := by
  have hw := a.2.binaryCode_length_of_bounded n N ha hn (by omega)
  have hi := Nat.size_le_size (show a.1.val ≤ N by have := a.1.isLt; omega)
  simp only [berkowitzPowerCode, familyCode, pair_length, length_encNat]
  omega

theorem berkowitzExpandedFactorCode_length_of_bounded {n : ℕ}
    (a : BerkowitzExpandedFactorAddress n) (N : ℕ) (ha : a.Bounded) (hn : n ≤ N) :
    (berkowitzExpandedFactorCode a).length ≤ 18 * (N.size + 5) := by
  cases a with
  | zero => simp [berkowitzExpandedFactorCode, SubstituteAddress.binaryCode]; omega
  | outer a =>
    have h := a.binaryCode_length_of_bounded N ha hn
    simp only [berkowitzExpandedFactorCode, SubstituteAddress.binaryCode, List.length_cons]
    omega
  | inner a =>
    have h := berkowitzPowerCode_length_of_bounded a N ha hn
    simp only [berkowitzExpandedFactorCode, SubstituteAddress.binaryCode, List.length_cons]
    omega

theorem berkowitzCoreCode_length_of_bounded {n : ℕ} (a : BerkowitzCoreAddress n)
    (N : ℕ) (ha : a.Bounded) (hn : n + 1 ≤ N) :
    (berkowitzCoreCode a).length ≤ 20 * (N.size + 5) := by
  cases a with
  | zero => simp [berkowitzCoreCode, SubstituteAddress.binaryCode]; omega
  | outer a =>
    have h := a.binaryCode_length_of_bounded n N ha (by omega) hn
    simp only [berkowitzCoreCode, SubstituteAddress.binaryCode, List.length_cons]
    omega
  | inner a =>
    have h := berkowitzExpandedFactorCode_length_of_bounded a N ha (by omega)
    simp only [berkowitzCoreCode, SubstituteAddress.binaryCode, List.length_cons]
    omega

/-- All determinant layers together still use only linearly many address bits. -/
theorem BerkowitzAddress.binaryCode_length_of_bounded {n : ℕ} (a : BerkowitzAddress n)
    (N : ℕ) (ha : a.Bounded) (hn : n + 1 ≤ N) :
    a.binaryCode.length ≤ 22 * (N.size + 5) := by
  cases a with
  | initial | sign => simp [binaryCode]; omega
  | core a =>
    have h := berkowitzCoreCode_length_of_bounded a N ha hn
    simp only [binaryCode, List.length_cons]
    omega

theorem FrobeniusEntryAddress.binaryCode_length_of_bounded {n : ℕ}
    (a : FrobeniusEntryAddress n) (q N : ℕ) (ha : a.Bounded q)
    (hn : n ≤ N) (hq : q * n ≤ N) :
    a.binaryCode.length ≤ 16 * (N.size + 5) := by
  cases a with
  | entry i j | delta i j =>
    have hw := encodeNumerals_length_le [i.val, j.val] N.size (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact Nat.size_le_size (by omega)
      · exact Nat.size_le_size (by omega))
    simp only [List.length_cons, List.length_nil] at hw
    simp only [binaryCode, List.length_cons]
    omega
  | power a =>
    have hw := a.binaryCode_length_of_bounded (q * n) N ha hq hn
    simp only [binaryCode, List.length_cons]
    omega

/-- The complete Frobenius minor evaluator has polynomial address width in `log q + log n`. -/
theorem frobeniusMinorCode_length_of_bounded {n : ℕ} (a : FrobeniusMinorAddress n)
    (q N : ℕ)
    (ha : SubstituteAddress.Bounded BerkowitzAddress.Bounded (FrobeniusEntryAddress.Bounded q) a)
    (hn : n ≤ N) (hN : 1 ≤ N) (hq : q * n ≤ N) :
    (frobeniusMinorCode a).length ≤ 24 * (N.size + 5) := by
  cases a with
  | zero => simp [frobeniusMinorCode, SubstituteAddress.binaryCode]; omega
  | outer a =>
    have hw := a.binaryCode_length_of_bounded N ha (by omega)
    simp only [frobeniusMinorCode, SubstituteAddress.binaryCode, List.length_cons]
    omega
  | inner a =>
    have hw := a.binaryCode_length_of_bounded q N ha hn hq
    simp only [frobeniusMinorCode, SubstituteAddress.binaryCode, List.length_cons]
    omega

end SparseIrred.UpperBounds.Section4
