import SparseIrred.UpperBounds.Section4.EntryMachineEncoded
import SparseIrred.UpperBounds.Section4.BerkowitzFrobeniusProgram

/-! # Binary encodings of the determinant and Frobenius address layers -/

namespace SparseIrred.UpperBounds.Section4

open Complexity SparseDiv SparseDiv.StringArith

def BerkowitzFactorAddress.fields {n : ℕ} : BerkowitzFactorAddress n → List ℕ
  | .entry s i j => [0, s.val, i.val, j.val]
  | .rows s e lo count => [1, s.val, e.val, lo, count]
  | .cols s e k lo count => [2, s.val, e.val, k.val, lo, count]
  | .term s e k l => [3, s.val, e.val, k.val, l.val]
  | .weighted s e k l => [4, s.val, e.val, k.val, l.val]
  | .power s e k l => [5, s.val, e.val, k.val, l.val]
  | .row s k => [6, s.val, k.val]
  | .col s k => [7, s.val, k.val]
  | .diag s => [8, s.val]
  | .negOne => [9]
  | .zero => [10]

def BerkowitzFactorAddress.fromFields (n : ℕ) : List ℕ → Option (BerkowitzFactorAddress n)
  | [0, s, i, j] => if h : s < n ∧ i < n + 1 ∧ j < n + 1 then
      some (.entry ⟨s, h.1⟩ ⟨i, h.2.1⟩ ⟨j, h.2.2⟩) else none
  | [1, s, e, lo, count] => if h : s < n ∧ e < n + 1 then
      some (.rows ⟨s, h.1⟩ ⟨e, h.2⟩ lo count) else none
  | [2, s, e, k, lo, count] => if h : s < n ∧ e < n + 1 ∧ k < n - s - 1 then
      some (.cols ⟨s, h.1⟩ ⟨e, h.2.1⟩ ⟨k, h.2.2⟩ lo count) else none
  | [3, s, e, k, l] => if h : s < n ∧ e < n + 1 ∧ k < n - s - 1 ∧ l < n - s - 1 then
      some (.term ⟨s, h.1⟩ ⟨e, h.2.1⟩ ⟨k, h.2.2.1⟩ ⟨l, h.2.2.2⟩) else none
  | [4, s, e, k, l] => if h : s < n ∧ e < n + 1 ∧ k < n - s - 1 ∧ l < n - s - 1 then
      some (.weighted ⟨s, h.1⟩ ⟨e, h.2.1⟩ ⟨k, h.2.2.1⟩ ⟨l, h.2.2.2⟩) else none
  | [5, s, e, k, l] => if h : s < n ∧ e < n + 1 ∧ k < n - s - 1 ∧ l < n - s - 1 then
      some (.power ⟨s, h.1⟩ ⟨e, h.2.1⟩ ⟨k, h.2.2.1⟩ ⟨l, h.2.2.2⟩) else none
  | [6, s, k] => if h : s < n ∧ k < n - s - 1 then
      some (.row ⟨s, h.1⟩ ⟨k, h.2⟩) else none
  | [7, s, k] => if h : s < n ∧ k < n - s - 1 then
      some (.col ⟨s, h.1⟩ ⟨k, h.2⟩) else none
  | [8, s] => if h : s < n then some (.diag ⟨s, h⟩) else none
  | [9] => some .negOne
  | [10] => some .zero
  | _ => none

@[simp] theorem BerkowitzFactorAddress.fromFields_fields {n : ℕ} (a : BerkowitzFactorAddress n) :
    fromFields n a.fields = some a := by
  cases a <;> simp [fields, fromFields, Fin.isLt] <;> omega

def BerkowitzFactorAddress.binaryCode {n : ℕ} (a : BerkowitzFactorAddress n) : List Bool :=
  encodeNumerals a.fields

theorem BerkowitzFactorAddress.binaryCode_injective {n : ℕ} :
    Function.Injective (@BerkowitzFactorAddress.binaryCode n) := by
  intro a b h
  have hh := congrArg (fun s ↦ fromFields n (decodeNumerals s)) h
  simpa only [binaryCode, decodeNumerals_encode, fromFields_fields, Option.some.injEq] using hh

theorem BerkowitzFactorAddress.binaryCode_length {n : ℕ} (a : BerkowitzFactorAddress n)
    (w : ℕ) (hw : ∀ v ∈ a.fields, v.size ≤ w) : a.binaryCode.length ≤ 6 * (2 * w + 2) := by
  have h := encodeNumerals_length_le a.fields w hw
  have hl : a.fields.length ≤ 6 := by cases a <;> simp [fields]
  exact h.trans (by nlinarith)

def berkowitzPowerCode {n : ℕ} : BerkowitzPowerAddress n → List Bool :=
  familyCode (fun _ ↦ ProductAddress.binaryCode)

def berkowitzExpandedFactorCode {n : ℕ} : BerkowitzExpandedFactorAddress n → List Bool :=
  SubstituteAddress.binaryCode BerkowitzFactorAddress.binaryCode berkowitzPowerCode

def berkowitzCoreCode {n : ℕ} : BerkowitzCoreAddress n → List Bool :=
  SubstituteAddress.binaryCode ProductAddress.binaryCode berkowitzExpandedFactorCode

def BerkowitzAddress.binaryCode {n : ℕ} : BerkowitzAddress n → List Bool
  | .initial => [false, false]
  | .sign => [false, true]
  | .core a => true :: berkowitzCoreCode a

theorem berkowitzPowerCode_injective {n : ℕ} :
    Function.Injective (@berkowitzPowerCode n) :=
  familyCode_injective _ (fun _ ↦ ProductAddress.binaryCode_injective)

theorem berkowitzExpandedFactorCode_injective {n : ℕ} :
    Function.Injective (@berkowitzExpandedFactorCode n) :=
  SubstituteAddress.binaryCode_injective _ _
    BerkowitzFactorAddress.binaryCode_injective berkowitzPowerCode_injective

theorem berkowitzCoreCode_injective {n : ℕ} : Function.Injective (@berkowitzCoreCode n) :=
  SubstituteAddress.binaryCode_injective _ _
    ProductAddress.binaryCode_injective berkowitzExpandedFactorCode_injective

theorem BerkowitzAddress.binaryCode_injective {n : ℕ} :
    Function.Injective (@BerkowitzAddress.binaryCode n) := by
  intro a b h
  cases a <;> cases b <;> simp only [binaryCode, List.cons.injEq, Bool.false_eq_true,
    Bool.true_eq_false, false_and, and_false, true_and] at h
  all_goals try contradiction
  all_goals try rfl
  exact congrArg _ (berkowitzCoreCode_injective h)

def FrobeniusEntryAddress.binaryCode {n : ℕ} : FrobeniusEntryAddress n → List Bool
  | .entry i j => false :: false :: encodeNumerals [i.val, j.val]
  | .delta i j => false :: true :: encodeNumerals [i.val, j.val]
  | .power a => true :: a.binaryCode

theorem FrobeniusEntryAddress.binaryCode_injective {n : ℕ} :
    Function.Injective (@FrobeniusEntryAddress.binaryCode n) := by
  intro a b h
  cases a <;> cases b <;> simp only [binaryCode, List.cons.injEq, Bool.false_eq_true,
    Bool.true_eq_false, false_and, and_false, true_and] at h
  all_goals try contradiction
  · have he := congrArg decodeNumerals h
    simp only [decodeNumerals_encode, List.cons.injEq, and_true] at he
    exact congrArg₂ _ (Fin.ext he.1) (Fin.ext he.2)
  · have he := congrArg decodeNumerals h
    simp only [decodeNumerals_encode, List.cons.injEq, and_true] at he
    exact congrArg₂ _ (Fin.ext he.1) (Fin.ext he.2)
  · exact congrArg _ (ProductAddress.binaryCode_injective h)

def frobeniusMinorCode {n : ℕ} : FrobeniusMinorAddress n → List Bool :=
  SubstituteAddress.binaryCode BerkowitzAddress.binaryCode FrobeniusEntryAddress.binaryCode

theorem frobeniusMinorCode_injective {n : ℕ} :
    Function.Injective (@frobeniusMinorCode n) :=
  SubstituteAddress.binaryCode_injective _ _
    BerkowitzAddress.binaryCode_injective FrobeniusEntryAddress.binaryCode_injective

end SparseIrred.UpperBounds.Section4
