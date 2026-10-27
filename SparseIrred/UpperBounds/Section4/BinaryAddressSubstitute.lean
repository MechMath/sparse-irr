import SparseIrred.UpperBounds.Section4.BinaryAddressCombinators

/-! # A binary dispatcher for inlined subprogram requests -/

namespace SparseIrred.UpperBounds.Section4

open Complexity SparseDiv SparseDiv.StringArith

def binaryOptionCode {B : Type*} (eb : B → List Bool) : Option B → List Bool
  | none => [false]
  | some b => true :: eb b

def binarySubstituteInstruction (outer inner request : List Bool → List Bool)
    (zero addr : List Bool) : List Bool :=
  binaryBit addr
    (binaryBit addr.tail (binaryValue zero) (binaryLift [true, false] (inner addr.tail.tail)))
    (binaryBit (request addr.tail)
      (binaryBranch .add (true :: false :: (request addr.tail).tail) [true, true])
      (binaryLift [false] (outer addr.tail)))

theorem binarySubstituteInstruction_eq {A B R : Type*} [Semiring R]
    (P : EntryProgram A R) (Q : EntryProgram B R) (request : A → Option B) (bound : ℕ)
    (hb : ∀ a b, request a = some b → Q.rank b ≤ bound)
    (ea : A → List Bool) (eb : B → List Bool) (er : R → List Bool)
    (outer inner req : List Bool → List Bool)
    (ho : ∀ a, request a = none → outer (ea a) = (P.instruction a).binaryCode ea er)
    (hi : ∀ b, inner (eb b) = (Q.instruction b).binaryCode eb er)
    (hr : ∀ a, req (ea a) = binaryOptionCode eb (request a))
    (hleaf : ∀ a b, request a = some b → ∃ v, P.instruction a = .value v)
    (a : SubstituteAddress A B) :
    binarySubstituteInstruction outer inner req (er 0) (a.binaryCode ea eb) =
      ((P.substitute Q request bound hb).instruction a).binaryCode
        (SubstituteAddress.binaryCode ea eb) er := by
  cases a with
  | zero => rfl
  | inner b =>
    simp only [binarySubstituteInstruction, SubstituteAddress.binaryCode, binaryBit,
      List.headD_cons, List.tail_cons, ↓reduceIte, hi]
    have h := binaryLift_eq eb (SubstituteAddress.binaryCode ea eb) er SubstituteAddress.inner
      [true, false] (fun _ ↦ rfl) (Q.instruction b)
    cases he : Q.instruction b <;> simpa [EntryProgram.substitute,
      EntryProgram.substituteInstruction, he] using h
  | outer a =>
    cases he : request a with
    | some b =>
      obtain ⟨v, hv⟩ := hleaf a b he
      simp [binarySubstituteInstruction, SubstituteAddress.binaryCode, binaryBit, hr, he,
        binaryOptionCode, binaryBranch, EntryProgram.substitute, EntryProgram.substituteInstruction,
        hv, EntryInstruction.binaryCode, BinaryOp.code]
    | none =>
      simp only [binarySubstituteInstruction, SubstituteAddress.binaryCode, binaryBit,
        List.headD_cons, List.tail_cons, ↓reduceIte, hr, he, binaryOptionCode, ho a he]
      have h := binaryLift_eq ea (SubstituteAddress.binaryCode ea eb) er SubstituteAddress.outer
        [false] (fun _ ↦ rfl) (P.instruction a)
      cases hp : P.instruction a <;> simpa [EntryProgram.substitute,
        EntryProgram.substituteInstruction, hp, he] using h

theorem cobham_binarySubstituteInstruction {n : ℕ}
    {outer inner request : (Fin n → List Bool) → List Bool → List Bool}
    (ho : BinaryCobhamFamily outer) (hi : BinaryCobhamFamily inner) (hr : BinaryCobhamFamily request)
    {zero addr : (Fin n → List Bool) → List Bool} (hz : Cobham zero) (ha : Cobham addr) :
    Cobham fun v ↦ binarySubstituteInstruction (outer v) (inner v) (request v) (zero v) (addr v) := by
  have ht := cobham_binaryTail ha
  have hreq := hr _ ht
  exact cobham_binaryBit ha
    (cobham_binaryBit ht (cobham_binaryValue hz)
      (cobham_binaryLift [true, false] (hi _ (cobham_binaryTail ht))))
    (cobham_binaryBit hreq
      (cobham_binaryBranch .add (cobham_cons true (cobham_cons false (cobham_binaryTail hreq)))
        (.const [true, true]))
      (cobham_binaryLift [false] (ho _ ht)))

theorem binaryFamilyInstruction_eq {R : Type*} [Semiring R] {m : ℕ} {A : Fin m → Type*}
    (P : ∀ i, EntryProgram (A i) R) (ea : ∀ i, A i → List Bool) (er : R → List Bool)
    (inner : List Bool → List Bool)
    (hi : ∀ i a, inner (pair (encNat i.val) (ea i a)) = ((P i).instruction a).binaryCode (ea i) er)
    (a : Σ i, A i) : binaryFamilyInstruction inner (familyCode ea a) =
      ((EntryProgram.family P).instruction a).binaryCode (familyCode ea) er := by
  rcases a with ⟨i, a⟩
  simp only [binaryFamilyInstruction, familyCode, hi]
  have h := binaryInstructionMap_eq (ea i) (familyCode ea) er er (Sigma.mk i) id
    (fun b ↦ pair (pairFst (pair (encNat i.val) (ea i a))) b) id
    (by intro; simp [familyCode]) (fun _ ↦ rfl) ((P i).instruction a)
  cases he : (P i).instruction a <;>
    simpa [EntryProgram.family, EntryProgram.familyInstruction, he,
      binaryInstructionMap, binaryBit, EntryInstruction.binaryCode, binaryValue] using h

end SparseIrred.UpperBounds.Section4
