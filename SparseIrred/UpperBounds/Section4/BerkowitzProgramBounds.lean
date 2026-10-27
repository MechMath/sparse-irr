import SparseIrred.UpperBounds.Section4.BerkowitzProgram
import SparseIrred.UpperBounds.Section4.EntryMachineBounds
import SparseIrred.UpperBounds.Section4.StackRestricted

/-!
# Closed register invariants for the complete Berkowitz program

All sum intervals remain within the current matrix dimension. Product intervals
and exponent intervals remain within the original determinant dimension. The
invariant survives the two layers of program substitution and every stack step.
-/

namespace SparseIrred.UpperBounds.Section4

open Matrix

variable {A B R : Type*}

def SubstituteAddress.Bounded (BA : A → Prop) (BB : B → Prop) :
    SubstituteAddress A B → Prop
  | .outer a => BA a
  | .inner b => BB b
  | .zero => True

section Generic

variable [Semiring R]

/-- Substitution preserves a closed register invariant when every request satisfies
the invariant of the invoked subprogram. -/
theorem EntryProgram.substitute_closed (P : EntryProgram A R) (Q : EntryProgram B R)
    (request : A → Option B) (K : ℕ)
    (hK : ∀ a b, request a = some b → Q.rank b ≤ K)
    (BA : A → Prop) (BB : B → Prop) (hP : P.Closed BA) (hQ : Q.Closed BB)
    (hrequest : ∀ a b, BA a → request a = some b → BB b) :
    (P.substitute Q request K hK).Closed (SubstituteAddress.Bounded BA BB) := by
  intro a op l r ha h
  cases a with
  | zero => simp [substitute, substituteInstruction] at h
  | inner b =>
      cases he : Q.instruction b with
      | value v => simp [substitute, substituteInstruction, he] at h
      | branch op' l' r' =>
          simp only [substitute, substituteInstruction, he, EntryInstruction.branch.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact hQ b op' l' r' ha he
  | outer a =>
      cases he : P.instruction a with
      | branch op' l' r' =>
          simp only [substitute, substituteInstruction, he, EntryInstruction.branch.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact hP a op' l' r' ha he
      | value v =>
          cases hr : request a with
          | none => simp [substitute, substituteInstruction, he, hr] at h
          | some b =>
              simp only [substitute, substituteInstruction, he, hr,
                EntryInstruction.branch.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              exact ⟨hrequest a b ha hr, trivial⟩

omit [Semiring R] in
theorem EntryProgram.family_closed {I : Type*} {As : I → Type*}
    (P : ∀ i, EntryProgram (As i) R) (B : ∀ i, As i → Prop)
    (hP : ∀ i, (P i).Closed (B i)) :
    (EntryProgram.family P).Closed (fun a ↦ B a.1 a.2) := by
  intro a op l r ha h
  rcases a with ⟨i, a⟩
  cases he : (P i).instruction a with
  | value v => simp [family, familyInstruction, he] at h
  | branch op' l' r' =>
      simp only [family, familyInstruction, he, EntryInstruction.branch.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact hP i a op' l' r' ha he

end Generic

variable {n : ℕ}

/-- Only the two explicit sum intervals require bounds beyond their `Fin` indices. -/
def BerkowitzFactorAddress.Bounded : BerkowitzFactorAddress n → Prop
  | .rows s _ lo count => lo + count ≤ n - s.val - 1
  | .cols s _ _ lo count => lo + count ≤ n - s.val - 1
  | _ => True

section CommRing

variable [CommRing R]

theorem berkowitzFactorProgram_closed (M : Matrix (Fin n) (Fin n) R) :
    (berkowitzFactorProgram M).Closed BerkowitzFactorAddress.Bounded := by
  intro a op l r ha h
  change berkowitzFactorInstruction M a = .branch op l r at h
  cases a with
  | zero | negOne | row s k | col s l | diag s | power s e k l =>
      simp [berkowitzFactorInstruction] at h
  | weighted s e k l | term s e k l =>
      cases h
      exact ⟨trivial, trivial⟩
  | cols s e k lo count =>
      simp only [berkowitzFactorInstruction] at h
      split_ifs at h <;> try cases h
      · exact ⟨trivial, trivial⟩
      · simp only [BerkowitzFactorAddress.Bounded] at *
        omega
  | rows s e lo count =>
      simp only [berkowitzFactorInstruction] at h
      split_ifs at h <;> try cases h
      · exact ⟨by simp [BerkowitzFactorAddress.Bounded], trivial⟩
      · simp only [BerkowitzFactorAddress.Bounded] at *
        omega
  | entry s i j =>
      simp only [berkowitzFactorInstruction] at h
      split_ifs at h <;> try cases h
      · exact ⟨trivial, trivial⟩
      · exact ⟨trivial, by simp [BerkowitzFactorAddress.Bounded]⟩

def BerkowitzPowerAddress.Bounded (a : BerkowitzPowerAddress n) : Prop :=
  a.2.Bounded n

theorem berkowitzPowerProgram_closed (M : Matrix (Fin n) (Fin n) R) :
    (berkowitzPowerProgram M).Closed BerkowitzPowerAddress.Bounded := by
  apply EntryProgram.family_closed
    (fun s : Fin n ↦ productProgram (fun _ ↦ berkowitzStrictTail M s))
    (fun s : Fin n ↦ ProductAddress.Bounded (n := n - s.val - 1) n)
  intro s a op l r ha h
  exact productInstruction_bounded _ n a op l r ha h

theorem berkowitzPowerRequest_bounded (a : BerkowitzFactorAddress n)
    (b : BerkowitzPowerAddress n) (_ha : a.Bounded) (h : berkowitzPowerRequest a = some b) :
    b.Bounded := by
  cases a <;> simp only [berkowitzPowerRequest] at h <;> try cases h
  rename_i s e k l
  change 0 + e.val ≤ n
  have := e.isLt
  omega

def BerkowitzExpandedFactorAddress.Bounded : BerkowitzExpandedFactorAddress n → Prop :=
  SubstituteAddress.Bounded BerkowitzFactorAddress.Bounded BerkowitzPowerAddress.Bounded

theorem berkowitzExpandedFactorProgram_closed (M : Matrix (Fin n) (Fin n) R) :
    (berkowitzExpandedFactorProgram M).Closed BerkowitzExpandedFactorAddress.Bounded := by
  exact EntryProgram.substitute_closed _ _ _ _ _ _ _
    (berkowitzFactorProgram_closed M) (berkowitzPowerProgram_closed M)
    berkowitzPowerRequest_bounded

theorem berkowitzFactorRequest_bounded (a : ProductAddress (n + 1))
    (b : BerkowitzExpandedFactorAddress n) (_ha : a.Bounded n)
    (h : berkowitzFactorRequest a = some b) : b.Bounded := by
  cases a with
  | zero | sum _ _ _ _ _ _ => simp [berkowitzFactorRequest] at h
  | entry start len i j =>
      simp only [berkowitzFactorRequest] at h
      split_ifs at h <;> try cases h
      trivial

def BerkowitzCoreAddress.Bounded : BerkowitzCoreAddress n → Prop :=
  SubstituteAddress.Bounded (ProductAddress.Bounded n) BerkowitzExpandedFactorAddress.Bounded

theorem berkowitzCoreProgram_closed (M : Matrix (Fin n) (Fin n) R) :
    (berkowitzCoreProgram M).Closed BerkowitzCoreAddress.Bounded := by
  apply EntryProgram.substitute_closed _ _ _ _ _ _ _
    (fun a op l r ha h ↦ productInstruction_bounded _ n a op l r ha h)
    (berkowitzExpandedFactorProgram_closed M) berkowitzFactorRequest_bounded

theorem berkowitzCoreInitial_bounded (n : ℕ) : (berkowitzCoreInitial n).Bounded := by
  change 0 + n ≤ n
  omega

def BerkowitzAddress.Bounded : BerkowitzAddress n → Prop
  | .initial | .sign => True
  | .core a => a.Bounded

theorem berkowitzProgram_closed (M : Matrix (Fin n) (Fin n) R) :
    (berkowitzProgram M).Closed BerkowitzAddress.Bounded := by
  intro a op l r ha h
  change berkowitzInstruction M a = .branch op l r at h
  cases a with
  | sign => simp [berkowitzInstruction] at h
  | initial =>
      cases h
      exact ⟨trivial, berkowitzCoreInitial_bounded n⟩
  | core a =>
      cases he : (berkowitzCoreProgram M).instruction a with
      | value v => simp [berkowitzInstruction, he] at h
      | branch op' l' r' =>
          simp only [berkowitzInstruction, he, EntryInstruction.branch.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact berkowitzCoreProgram_closed M a op' l' r' ha he

/-- All current and suspended addresses satisfy the register bound at every step. -/
theorem berkowitzProgram_addresses_bounded (M : Matrix (Fin n) (Fin n) R) (t : ℕ) :
    ((berkowitzProgram M).step^[t] (.eval .initial [])).Addresses BerkowitzAddress.Bounded := by
  exact EntryProgram.addresses_iterate _ _ (berkowitzProgram_closed M) .initial trivial t

end CommRing

end SparseIrred.UpperBounds.Section4
