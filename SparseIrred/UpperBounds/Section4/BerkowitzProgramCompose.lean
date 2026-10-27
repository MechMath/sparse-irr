import SparseIrred.UpperBounds.Section4.StackEvaluator

/-!
# Composition of arithmetic address programs

Replacing an expensive leaf by another address program adds the two stack-depth
bounds. No running-time bound or dense intermediate result is assumed.
-/

namespace SparseIrred.UpperBounds.Section4

variable {A B R : Type*} [Semiring R]

/-- Addresses for a program whose selected leaves invoke a second program. -/
inductive SubstituteAddress (A B : Type*) where
  | outer (a : A)
  | inner (b : B)
  | zero

def EntryProgram.substituteInstruction (P : EntryProgram A R) (Q : EntryProgram B R)
    (request : A → Option B) : SubstituteAddress A B →
      EntryInstruction (SubstituteAddress A B) R
  | .zero => .value 0
  | .inner b => match Q.instruction b with
    | .value v => .value v
    | .branch op l r => .branch op (.inner l) (.inner r)
  | .outer a => match P.instruction a with
    | .branch op l r => .branch op (.outer l) (.outer r)
    | .value v => match request a with
      | none => .value v
      | some b => .branch .add (.inner b) .zero

def EntryProgram.substituteRank (P : EntryProgram A R) (Q : EntryProgram B R)
    (K : ℕ) : SubstituteAddress A B → ℕ
  | .zero => 0
  | .inner b => Q.rank b + 1
  | .outer a => P.rank a + K + 2

theorem EntryProgram.substitute_descend (P : EntryProgram A R) (Q : EntryProgram B R)
    (request : A → Option B) (K : ℕ)
    (hK : ∀ a b, request a = some b → Q.rank b ≤ K)
    (a : SubstituteAddress A B) (op : BinaryOp) (l r : SubstituteAddress A B)
    (h : P.substituteInstruction Q request a = .branch op l r) :
    P.substituteRank Q K l < P.substituteRank Q K a ∧
      P.substituteRank Q K r < P.substituteRank Q K a := by
  cases a with
  | zero => simp [substituteInstruction] at h
  | inner b =>
    cases he : Q.instruction b with
    | value v => simp [substituteInstruction, he] at h
    | branch op' l' r' =>
      simp only [substituteInstruction, he, EntryInstruction.branch.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have hd := Q.descend b op' l' r' he
      simp only [substituteRank]
      omega
  | outer a =>
    cases he : P.instruction a with
    | branch op' l' r' =>
      simp only [substituteInstruction, he, EntryInstruction.branch.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have hd := P.descend a op' l' r' he
      simp only [substituteRank]
      omega
    | value v =>
      cases hr : request a with
      | none => simp [substituteInstruction, he, hr] at h
      | some b =>
        simp only [substituteInstruction, he, hr, EntryInstruction.branch.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have hb := hK a b hr
        simp only [substituteRank]
        omega

/-- Replace selected leaf instructions by calls to `Q`; the bound is on call depth only. -/
def EntryProgram.substitute (P : EntryProgram A R) (Q : EntryProgram B R)
    (request : A → Option B) (K : ℕ)
    (hK : ∀ a b, request a = some b → Q.rank b ≤ K) :
    EntryProgram (SubstituteAddress A B) R :=
  ⟨P.substituteInstruction Q request, P.substituteRank Q K,
    P.substitute_descend Q request K hK⟩

def EntryProgram.substituteMeaning (P : EntryProgram A R) (Q : EntryProgram B R) :
    SubstituteAddress A B → R
  | .zero => 0
  | .inner b => Q.value b
  | .outer a => P.value a

/-- Substitution preserves values when the requested program computes each replaced leaf. -/
theorem EntryProgram.substitute_value (P : EntryProgram A R) (Q : EntryProgram B R)
    (request : A → Option B) (K : ℕ)
    (hK : ∀ a b, request a = some b → Q.rank b ≤ K)
    (hvalue : ∀ a b v, P.instruction a = .value v → request a = some b → Q.value b = v)
    (a : SubstituteAddress A B) :
    (P.substitute Q request K hK).value a = P.substituteMeaning Q a := by
  apply EntryProgram.value_eq_of_equations
  intro a
  cases a with
  | zero => rfl
  | inner b =>
    change Q.value b = _
    rw [EntryProgram.value]
    cases he : Q.instruction b <;>
      simp [substitute, substituteInstruction, substituteMeaning, he]
  | outer a =>
    change P.value a = _
    rw [EntryProgram.value]
    cases he : P.instruction a with
    | branch op l r => simp [substitute, substituteInstruction, substituteMeaning, he]
    | value v =>
      cases hr : request a with
      | none => simp [substitute, substituteInstruction, he, hr]
      | some b =>
        simp [substitute, substituteInstruction, substituteMeaning, he, hr,
          BinaryOp.apply, hvalue a b v he hr]

/-- Substituting an oracle adds its depth bound to the original program's depth bound. -/
theorem EntryProgram.substitute_stack_bound (P : EntryProgram A R) (Q : EntryProgram B R)
    (request : A → Option B) (K : ℕ)
    (hK : ∀ a b, request a = some b → Q.rank b ≤ K) (a : A) (t : ℕ) :
    (((P.substitute Q request K hK).step)^[t] (.eval (.outer a) [])).stack.length ≤
      P.rank a + K + 2 :=
  (P.substitute Q request K hK).stack_length_iterate_le (.outer a) t

def EntryProgram.familyInstruction {I : Type*} {As : I → Type*}
    (P : ∀ i, EntryProgram (As i) R) (a : Σ i, As i) : EntryInstruction (Σ i, As i) R :=
  match P a.1 |>.instruction a.2 with
  | .value v => .value v
  | .branch op l r => .branch op ⟨a.1, l⟩ ⟨a.1, r⟩

/-- A family of entry programs, retaining its index in each address. -/
def EntryProgram.family {I : Type*} {As : I → Type*}
    (P : ∀ i, EntryProgram (As i) R) : EntryProgram (Σ i, As i) R where
  instruction := EntryProgram.familyInstruction P
  rank a := (P a.1).rank a.2
  descend a op l r h := by
    rcases a with ⟨i, a⟩
    cases he : (P i).instruction a with
    | value v => simp [familyInstruction, he] at h
    | branch op' l' r' =>
      simp only [familyInstruction, he, EntryInstruction.branch.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact (P i).descend a op' l' r' he

theorem EntryProgram.family_value {I : Type*} {As : I → Type*}
    (P : ∀ i, EntryProgram (As i) R) (a : Σ i, As i) :
    (EntryProgram.family P).value a = (P a.1).value a.2 := by
  apply EntryProgram.value_eq_of_equations
  intro ⟨i, a⟩
  rw [EntryProgram.value]
  cases he : (P i).instruction a <;> simp [family, familyInstruction, he]

end SparseIrred.UpperBounds.Section4
