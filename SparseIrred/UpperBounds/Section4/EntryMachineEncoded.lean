import SparseIrred.UpperBounds.Section4.FieldBounds
import SparseIrred.UpperBounds.Section4.BerkowitzProgram
import SparseIrred.UpperBounds.Section4.EntryMachineBoolean
import SparseIrred.UpperBounds.Section4.StackFramed

/-!
# Self-delimiting binary codes for all arithmetic address constructors

The natural registers use the project's canonical binary natural encoding,
framed so that every code remains faithful even outside a runtime invariant.
Nested program constructors add only a constant number of tags or one index.
-/

namespace SparseIrred.UpperBounds.Section4

open Complexity SparseDiv SparseDiv.StringArith

private theorem encodeNumerals_inj {s t : List ℕ} (h : encodeNumerals s = encodeNumerals t) : s = t := by
  have hh := congrArg decodeNumerals h
  simpa only [decodeNumerals_encode] using hh

def ProductAddress.fields {n : ℕ} : ProductAddress n → List ℕ
  | .zero => [0]
  | .entry start len i j => [1, start, len, i.val, j.val]
  | .sum start len i j lo count => [2, start, len, i.val, j.val, lo, count]

def ProductAddress.binaryCode {n : ℕ} (a : ProductAddress n) : List Bool :=
  encodeNumerals a.fields

theorem ProductAddress.binaryCode_injective {n : ℕ} :
    Function.Injective (@ProductAddress.binaryCode n) := by
  intro a b h
  have he := encodeNumerals_inj h
  cases a <;> cases b <;> simp only [fields, List.cons.injEq, and_true] at he
  all_goals try omega
  all_goals congr 1 <;> (try apply Fin.ext) <;> omega

theorem ProductAddress.binaryCode_length {n : ℕ} (a : ProductAddress n) (w : ℕ)
    (hw : ∀ v ∈ a.fields, v.size ≤ w) : a.binaryCode.length ≤ 7 * (2 * w + 2) := by
  have h := encodeNumerals_length_le a.fields w hw
  have hl : a.fields.length ≤ 7 := by cases a <;> simp [fields]
  exact h.trans (by nlinarith)

/-- Constructor codes for substituting and composing subprograms. -/
def SubstituteAddress.binaryCode {A B : Type*} (encA : A → List Bool) (encB : B → List Bool) :
    SubstituteAddress A B → List Bool
  | .outer a => false :: encA a
  | .inner b => true :: false :: encB b
  | .zero => [true, true]

theorem SubstituteAddress.binaryCode_injective {A B : Type*}
    (encA : A → List Bool) (encB : B → List Bool)
    (hA : Function.Injective encA) (hB : Function.Injective encB) :
    Function.Injective (SubstituteAddress.binaryCode encA encB) := by
  intro a b h
  cases a <;> cases b <;> simp only [binaryCode, List.cons.injEq, Bool.false_eq_true,
    Bool.true_eq_false, false_and, true_and] at h
  all_goals try contradiction
  all_goals try rfl
  · exact congrArg _ (hA h)
  · exact congrArg _ (hB h)

def familyCode {m : ℕ} {A : Fin m → Type*} (enc : ∀ i, A i → List Bool)
    (a : Σ i, A i) : List Bool := pair (encNat a.1.val) (enc a.1 a.2)

theorem familyCode_injective {m : ℕ} {A : Fin m → Type*} (enc : ∀ i, A i → List Bool)
    (h : ∀ i, Function.Injective (enc i)) : Function.Injective (familyCode enc) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ he
  obtain ⟨hi, hab⟩ := pair_inj he
  have hij : i = j := Fin.ext (by
    have hh := congrArg decNat hi
    simpa using hh)
  subst j
  exact congrArg (Sigma.mk i) (h i hab)

def TestAddress.binaryCode {A : Type*} (enc : A → List Bool) : TestAddress A → List Bool
  | .test => [false, false]
  | .tag => [false, true]
  | .call a => true :: enc a

def BinaryAddress.binaryCode {A B : Type*} (encA : A → List Bool) (encB : B → List Bool) :
    BinaryAddress A B → List Bool
  | .root => [false, false]
  | .left a => false :: true :: encA a
  | .right b => true :: encB b

def OrAddress.binaryCode {m : ℕ} {A : Fin m → Type*} (enc : ∀ i, A i → List Bool) :
    OrAddress A → List Bool
  | .zero => [true, true]
  | .range lo count => false :: encodeNumerals [lo, count]
  | .call i a => true :: false :: familyCode enc ⟨i, a⟩

def DecisionScalar.binaryCode {K : Type*} (enc : K → List Bool) : DecisionScalar K → List Bool
  | .scalar a => false :: enc a
  | .flag b => [true, false, b]
  | .nonzeroTag => [true, true]

theorem TestAddress.binaryCode_injective {A : Type*} (enc : A → List Bool)
    (henc : Function.Injective enc) : Function.Injective (TestAddress.binaryCode enc) := by
  intro a b h
  cases a <;> cases b <;> simp only [binaryCode, List.cons.injEq, Bool.false_eq_true,
    Bool.true_eq_false, false_and, and_false, true_and] at h
  all_goals try contradiction
  all_goals try rfl
  exact congrArg _ (henc h)

theorem BinaryAddress.binaryCode_injective {A B : Type*}
    (encA : A → List Bool) (encB : B → List Bool)
    (hA : Function.Injective encA) (hB : Function.Injective encB) :
    Function.Injective (BinaryAddress.binaryCode encA encB) := by
  intro a b h
  cases a <;> cases b <;> simp only [binaryCode, List.cons.injEq, Bool.false_eq_true,
    Bool.true_eq_false, false_and, and_false, true_and] at h
  all_goals try contradiction
  all_goals try rfl
  · exact congrArg _ (hA h)
  · exact congrArg _ (hB h)

theorem OrAddress.binaryCode_injective {m : ℕ} {A : Fin m → Type*}
    (enc : ∀ i, A i → List Bool) (henc : ∀ i, Function.Injective (enc i)) :
    Function.Injective (OrAddress.binaryCode enc) := by
  intro a b h
  cases a <;> cases b <;> simp only [binaryCode, List.cons.injEq, Bool.false_eq_true,
    Bool.true_eq_false, false_and, and_false, true_and] at h
  all_goals try contradiction
  all_goals try rfl
  · have he := encodeNumerals_inj h
    simp only [List.cons.injEq, and_true] at he
    exact congrArg₂ OrAddress.range he.1 he.2
  · have he := familyCode_injective enc henc h
    cases he
    rfl

theorem DecisionScalar.binaryCode_injective {K : Type*} (enc : K → List Bool)
    (henc : Function.Injective enc) : Function.Injective (DecisionScalar.binaryCode enc) := by
  intro a b h
  cases a <;> cases b <;> simp only [binaryCode, List.cons.injEq, Bool.false_eq_true,
    Bool.true_eq_false, false_and, and_false, true_and, and_true] at h
  all_goals try contradiction
  all_goals try rfl
  · exact congrArg _ (henc h)
  · exact congrArg _ h

theorem DecisionScalar.binaryCode_length {K : Type*} (enc : K → List Bool) (w : ℕ)
    (hw : ∀ a, (enc a).length ≤ w) (a : DecisionScalar K) :
    (a.binaryCode enc).length ≤ w + 3 := by
  cases a with
  | scalar a => have := hw a; simp only [binaryCode, List.length_cons]; omega
  | flag b => simp [binaryCode]
  | nonzeroTag => simp [binaryCode]

end SparseIrred.UpperBounds.Section4
