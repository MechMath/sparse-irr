import SparseIrred.UpperBounds.Section4.EntryMachineEncodedBounds

/-! # Register invariants and binary widths for Boolean program composition -/

namespace SparseIrred.UpperBounds.Section4

open Complexity SparseDiv SparseDiv.StringArith

variable {A B K R : Type*}

def TestAddress.Bounded (BA : A → Prop) : TestAddress A → Prop
  | .call a => BA a
  | _ => True

def BinaryAddress.Bounded (BA : A → Prop) (BB : B → Prop) : BinaryAddress A B → Prop
  | .root => True
  | .left a => BA a
  | .right b => BB b

def OrAddress.Bounded {m : ℕ} {As : Fin m → Type*} (BA : ∀ i, As i → Prop) : OrAddress As → Prop
  | .zero => True
  | .range lo count => lo + count ≤ m
  | .call i a => BA i a

section Closed
variable [Add K] [Mul K] [Zero K] [DecidableEq K] [Add R] [Mul R]

theorem nonzeroProgram_closed (P : EntryProgram A K) (a : A) (BA : A → Prop)
    (hP : P.Closed BA) (ha : BA a) :
    (nonzeroProgram P a).Closed (TestAddress.Bounded BA) := by
  intro c op l r hc he
  cases c with
  | test => cases he; exact ⟨trivial, ha⟩
  | tag => cases he
  | call b =>
    dsimp only [nonzeroProgram] at he
    cases h : P.instruction b with
    | value v => simp only [h] at he; cases he
    | branch op l r =>
      simp only [h] at he
      cases he
      exact hP b op l r hc h

theorem binaryProgram_closed (op : BinaryOp) (P : EntryProgram A R) (Q : EntryProgram B R)
    (a : A) (b : B) (BA : A → Prop) (BB : B → Prop)
    (hP : P.Closed BA) (hQ : Q.Closed BB) (ha : BA a) (hb : BB b) :
    (binaryProgram op P Q a b).Closed (BinaryAddress.Bounded BA BB) := by
  intro c op' l r hc he
  cases c with
  | root => cases he; exact ⟨ha, hb⟩
  | left c =>
    dsimp only [binaryProgram] at he
    cases h : P.instruction c with
    | value v => simp only [h] at he; cases he
    | branch op l r => simp only [h] at he; cases he; exact hP c _ l r hc h
  | right c =>
    dsimp only [binaryProgram] at he
    cases h : Q.instruction c with
    | value v => simp only [h] at he; cases he
    | branch op l r => simp only [h] at he; cases he; exact hQ c _ l r hc h

theorem orProgram_closed {m : ℕ} {As : Fin m → Type*}
    (P : ∀ i, EntryProgram (As i) (DecisionScalar K)) (initial : ∀ i, As i)
    (bound : ℕ) (hbound : ∀ i, (P i).rank (initial i) ≤ bound)
    (BA : ∀ i, As i → Prop) (hP : ∀ i, (P i).Closed (BA i))
    (hinit : ∀ i, BA i (initial i)) :
    (orProgram P initial bound hbound).Closed (OrAddress.Bounded BA) := by
  intro a op l r ha he
  cases a with
  | zero => cases he
  | call i a =>
    dsimp only [orProgram] at he
    cases h : (P i).instruction a with
    | value v => simp only [h] at he; cases he
    | branch op l r => simp only [h] at he; cases he; exact hP i a op l r ha h
  | range lo count =>
    dsimp only [orProgram] at he
    split_ifs at he <;> cases he
    · exact ⟨hinit _, trivial⟩
    · simp only [OrAddress.Bounded] at *
      omega
end Closed

theorem TestAddress.binaryCode_length_of_bounded (enc : A → List Bool) (BA : A → Prop)
    (w : ℕ) (hw : ∀ a, BA a → (enc a).length ≤ w) (a : TestAddress A) (ha : a.Bounded BA) :
    (a.binaryCode enc).length ≤ w + 2 := by
  cases a with
  | test | tag => simp [binaryCode]
  | call a => have h := hw a ha; simp only [binaryCode, List.length_cons]; omega

theorem BinaryAddress.binaryCode_length_of_bounded (encA : A → List Bool) (encB : B → List Bool)
    (BA : A → Prop) (BB : B → Prop) (wa wb : ℕ)
    (hA : ∀ a, BA a → (encA a).length ≤ wa) (hB : ∀ b, BB b → (encB b).length ≤ wb)
    (a : BinaryAddress A B) (ha : a.Bounded BA BB) :
    (a.binaryCode encA encB).length ≤ max wa wb + 2 := by
  cases a with
  | root => simp [binaryCode]
  | left a => have h := hA a ha; simp only [binaryCode, List.length_cons]; omega
  | right b => have h := hB b ha; simp only [binaryCode, List.length_cons]; omega

theorem OrAddress.binaryCode_length_of_bounded {m : ℕ} {As : Fin m → Type*}
    (enc : ∀ i, As i → List Bool) (BA : ∀ i, As i → Prop) (w : ℕ)
    (hw : ∀ i a, BA i a → (enc i a).length ≤ w) (a : OrAddress As) (ha : a.Bounded BA) :
    (a.binaryCode enc).length ≤ w + 4 * m.size + 5 := by
  cases a with
  | zero => simp [binaryCode]
  | call i a =>
    have h := hw i a ha
    have hi := Nat.size_le_size (show i.val ≤ m by omega)
    simp only [binaryCode, familyCode, List.length_cons, pair_length, length_encNat]
    omega
  | range lo count =>
    have hc := encodeNumerals_length_le [lo, count] m.size (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact Nat.size_le_size (by exact Nat.le_trans (Nat.le_add_right _ _) ha)
      · exact Nat.size_le_size (by exact Nat.le_trans (Nat.le_add_left _ _) ha))
    simp only [List.length_cons, List.length_nil] at hc
    simp only [binaryCode, List.length_cons]
    omega

end SparseIrred.UpperBounds.Section4
