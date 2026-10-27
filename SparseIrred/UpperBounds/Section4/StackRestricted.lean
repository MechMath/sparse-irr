import SparseIrred.UpperBounds.Section4.StackEvaluator

/-!
# Restricting an address program to a closed address invariant

Fixed-width encodings are faithful on bounded addresses. Restricting the typed
address space removes unreachable out-of-range addresses before invoking the
local-step machine interface, whose laws quantify over all typed states.
-/

namespace SparseIrred.UpperBounds.Section4

variable {A R : Type*} [Add R] [Mul R]

/-- An address invariant closed under the two children of every arithmetic instruction. -/
def EntryProgram.Closed (P : EntryProgram A R) (B : A → Prop) : Prop :=
  ∀ a op l r, B a → P.instruction a = .branch op l r → B l ∧ B r

def EntryProgram.restrictInstruction (P : EntryProgram A R) (B : A → Prop)
    (hB : P.Closed B) (a : {a // B a}) : EntryInstruction {a // B a} R :=
  match he : P.instruction a.val with
  | .value v => .value v
  | .branch op l r => .branch op
      ⟨l, (hB _ _ _ _ a.property he).1⟩ ⟨r, (hB _ _ _ _ a.property he).2⟩

def EntryProgram.restrict (P : EntryProgram A R) (B : A → Prop) (hB : P.Closed B) :
    EntryProgram {a // B a} R where
  instruction := P.restrictInstruction B hB
  rank a := P.rank a.val
  descend a op l r h := by
    unfold restrictInstruction at h
    split at h <;> rename_i he
    · cases h
    · cases h
      exact P.descend _ _ _ _ he

/-- Restricting to valid addresses does not alter the meaning of any address. -/
theorem EntryProgram.restrict_value (P : EntryProgram A R) (B : A → Prop) (hB : P.Closed B)
    (a : {a // B a}) : (P.restrict B hB).value a = P.value a.val := by
  apply (P.restrict B hB).value_eq_of_equations (fun a ↦ P.value a.val)
  intro b
  cases he : P.instruction b.val with
  | value v =>
    have hh : P.restrictInstruction B hB b = .value v := by
      unfold restrictInstruction
      split <;> rename_i hh <;> have heq := hh.symm.trans he <;> simp_all
    simp only [restrict, hh]
    rw [value, he]
  | branch op l r =>
    have hh : P.restrictInstruction B hB b = .branch op
        ⟨l, (hB _ _ _ _ b.property he).1⟩ ⟨r, (hB _ _ _ _ b.property he).2⟩ := by
      unfold restrictInstruction
      split <;> rename_i hh <;> have heq := hh.symm.trans he <;> simp_all
    simp only [restrict, hh]
    rw [value, he]

@[simp] theorem EntryProgram.restrict_rank (P : EntryProgram A R) (B : A → Prop)
    (hB : P.Closed B) (a : {a // B a}) : (P.restrict B hB).rank a = P.rank a.val := rfl

end SparseIrred.UpperBounds.Section4
