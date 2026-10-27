import Mathlib.Tactic

/-!
# An address-based arithmetic stack evaluator

Only addresses and one scalar per suspended call are stored. The expression tree
is never materialized. The program supplies a local instruction for an address,
and a strictly decreasing rank certifies the depth of the unfolding.
-/

namespace SparseIrred.UpperBounds.Section4

inductive BinaryOp where
  | add
  | mul
  deriving DecidableEq

def BinaryOp.apply {R : Type*} [Add R] [Mul R] : BinaryOp → R → R → R
  | .add => (· + ·)
  | .mul => (· * ·)

inductive EntryInstruction (A R : Type*) where
  | value (v : R)
  | branch (op : BinaryOp) (left right : A)

/-- A local instruction decoder with a bound on the nesting of recursive calls. -/
structure EntryProgram (A R : Type*) where
  instruction : A → EntryInstruction A R
  rank : A → ℕ
  descend : ∀ a op l r, instruction a = .branch op l r →
    rank l < rank a ∧ rank r < rank a

variable {A R : Type*} [Add R] [Mul R]

/-- The semantic value of an address, defined by the certified rank. -/
def EntryProgram.value (P : EntryProgram A R) (a : A) : R :=
  match h : P.instruction a with
  | .value v => v
  | .branch op l r => op.apply (P.value l) (P.value r)
termination_by P.rank a
decreasing_by all_goals first | exact (P.descend _ _ _ _ h).1 | exact (P.descend _ _ _ _ h).2

/-- The number of nodes in the unfolded tree. This is a proof measure, not a register. -/
def EntryProgram.treeSize (P : EntryProgram A R) (a : A) : ℕ :=
  match h : P.instruction a with
  | .value _ => 1
  | .branch _ l r => 1 + P.treeSize l + P.treeSize r
termination_by P.rank a
decreasing_by all_goals first | exact (P.descend _ _ _ _ h).1 | exact (P.descend _ _ _ _ h).2

inductive EntryFrame (A R : Type*) where
  | left (op : BinaryOp) (right : A)
  | right (op : BinaryOp) (leftValue : R)

inductive EntryConfig (A R : Type*) where
  | eval (address : A) (stack : List (EntryFrame A R))
  | ret (value : R) (stack : List (EntryFrame A R))

/-- One local transition: inspect one address or pop one continuation. -/
def EntryProgram.step (P : EntryProgram A R) : EntryConfig A R → EntryConfig A R
  | .eval a stack => match P.instruction a with
    | .value v => .ret v stack
    | .branch op l r => .eval l (.left op r :: stack)
  | .ret v [] => .ret v []
  | .ret v (.left op r :: stack) => .eval r (.right op v :: stack)
  | .ret v (.right op l :: stack) => .ret (op.apply l v) stack

def EntryProgram.resume (P : EntryProgram A R) : List (EntryFrame A R) → R → R
  | [], v => v
  | .left op r :: stack, v => P.resume stack (op.apply v (P.value r))
  | .right op l :: stack, v => P.resume stack (op.apply l v)

def EntryProgram.meaning (P : EntryProgram A R) : EntryConfig A R → R
  | .eval a stack => P.resume stack (P.value a)
  | .ret v stack => P.resume stack v

theorem EntryProgram.meaning_step (P : EntryProgram A R) (c : EntryConfig A R) :
    P.meaning (P.step c) = P.meaning c := by
  cases c with
  | eval a stack =>
    cases h : P.instruction a with
    | value v =>
      simp only [step, h, meaning]
      conv_rhs => rw [value, h]
    | branch op l r =>
      simp only [step, h, meaning, EntryProgram.resume]
      conv_rhs => rw [value, h]
  | ret v stack => cases stack with
    | nil => rfl
    | cons f stack => cases f <;> rfl

def EntryProgram.frameWork (P : EntryProgram A R) : EntryFrame A R → ℕ
  | .left _ r => 3 * P.treeSize r + 2
  | .right _ _ => 1

def EntryProgram.work (P : EntryProgram A R) : EntryConfig A R → ℕ
  | .eval a stack => 3 * P.treeSize a + (stack.map P.frameWork).sum
  | .ret _ stack => (stack.map P.frameWork).sum

def EntryConfig.Halted : EntryConfig A R → Prop
  | .ret _ [] => True
  | _ => False

theorem EntryProgram.work_step_lt (P : EntryProgram A R) (c : EntryConfig A R)
    (h : ¬c.Halted) : P.work (P.step c) < P.work c := by
  cases c with
  | eval a stack =>
    cases heq : P.instruction a with
    | value v =>
      simp only [step, heq, work]
      conv_rhs => rw [treeSize, heq]
      dsimp only
      omega
    | branch op l r =>
      simp only [step, heq, work, List.map_cons, List.sum_cons, frameWork]
      conv_rhs => rw [treeSize, heq]
      dsimp only
      omega
  | ret v stack =>
    cases stack with
    | nil => exact (h trivial).elim
    | cons f stack =>
      cases f <;> simp [step, work, frameWork] <;> omega

/-- Every execution reaches a return with empty stack; no runtime clock is assumed. -/
theorem EntryProgram.terminates (P : EntryProgram A R) (c : EntryConfig A R) :
    ∃ t v, P.step^[t] c = .ret v [] := by
  induction hw : P.work c using Nat.strong_induction_on generalizing c with
  | h w ih =>
    by_cases hc : c.Halted
    · cases c with
      | eval a stack => exact hc.elim
      | ret v stack => cases stack with
        | nil => exact ⟨0, v, rfl⟩
        | cons f stack => exact hc.elim
    · obtain ⟨t, v, ht⟩ := ih _ (hw ▸ P.work_step_lt c hc) (P.step c) rfl
      exact ⟨t + 1, v, by simpa [Function.iterate_succ_apply] using ht⟩

theorem EntryProgram.meaning_iterate (P : EntryProgram A R) (c : EntryConfig A R) (t : ℕ) :
    P.meaning (P.step^[t] c) = P.meaning c := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', meaning_step, ih]

/-- The concrete stack evaluator returns the recursively specified value. -/
theorem EntryProgram.correct (P : EntryProgram A R) (a : A) :
    ∃ t, P.step^[t] (.eval a []) = .ret (P.value a) [] := by
  obtain ⟨t, v, ht⟩ := P.terminates (.eval a [])
  have hv := P.meaning_iterate (.eval a []) t
  rw [ht] at hv
  change v = P.value a at hv
  exact ⟨t, hv ▸ ht⟩

/-- A pending right call contributes its rank at its actual position in the stack. -/
def EntryProgram.stackHeight (P : EntryProgram A R) : List (EntryFrame A R) → ℕ
  | [] => 0
  | .left _ r :: stack => max (P.rank r + 1 + stack.length) (P.stackHeight stack)
  | .right _ _ :: stack => max (1 + stack.length) (P.stackHeight stack)

def EntryProgram.height (P : EntryProgram A R) : EntryConfig A R → ℕ
  | .eval a stack => max (P.rank a + stack.length) (P.stackHeight stack)
  | .ret _ stack => max stack.length (P.stackHeight stack)

theorem EntryProgram.height_step_le (P : EntryProgram A R) (c : EntryConfig A R) :
    P.height (P.step c) ≤ P.height c := by
  cases c with
  | eval a stack =>
    cases heq : P.instruction a with
    | value v =>
      simp only [step, heq, height]
      omega
    | branch op l r =>
      have hd := P.descend _ _ _ _ heq
      simp only [step, heq, height, List.length_cons, stackHeight]
      omega
  | ret v stack =>
    cases stack with
    | nil => exact le_rfl
    | cons f stack =>
      cases f <;> simp only [step, height, List.length_cons, stackHeight] <;> omega

def EntryConfig.stack : EntryConfig A R → List (EntryFrame A R)
  | .eval _ stack => stack
  | .ret _ stack => stack

/-- The bound covers every intermediate configuration, including partial sums and products. -/
theorem EntryProgram.stack_length_iterate_le (P : EntryProgram A R) (a : A) (t : ℕ) :
    (P.step^[t] (.eval a [])).stack.length ≤ P.rank a := by
  have hh : P.height (P.step^[t] (.eval a [])) ≤ P.rank a := by
    induction t with
    | zero => simp [height, stackHeight]
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact (P.height_step_le _).trans ih
  cases h : P.step^[t] (.eval a []) <;> simp only [h, height, EntryConfig.stack] at * <;> omega

/-- Local instruction equations determine the returned value uniquely. -/
theorem EntryProgram.value_eq_of_equations (P : EntryProgram A R) (f : A → R)
    (hf : ∀ a, f a = match P.instruction a with
      | .value v => v
      | .branch op l r => op.apply (f l) (f r)) (a : A) : P.value a = f a := by
  induction h : P.rank a using Nat.strong_induction_on generalizing a with
  | h n ih =>
    rw [value, hf a]
    cases he : P.instruction a with
    | value v => rfl
    | branch op l r =>
      dsimp only
      have hd := P.descend _ _ _ _ he
      rw [ih _ (h ▸ hd.1) l rfl, ih _ (h ▸ hd.2) r rfl]

/-- Although the tree may be large, its node count is singly exponential in stack depth. -/
theorem EntryProgram.treeSize_le (P : EntryProgram A R) (a : A) :
    P.treeSize a < 2 ^ (P.rank a + 1) := by
  induction h : P.rank a using Nat.strong_induction_on generalizing a with
  | h n ih =>
    rw [treeSize]
    cases he : P.instruction a with
    | value v =>
      dsimp only
      exact Nat.one_lt_two_pow (by omega)
    | branch op l r =>
      dsimp only
      have hd := P.descend _ _ _ _ he
      have hl := ih _ (h ▸ hd.1) l rfl
      have hr := ih _ (h ▸ hd.2) r rfl
      have hpl : 2 ^ (P.rank l + 1) ≤ 2 ^ P.rank a := Nat.pow_le_pow_right (by omega) (by omega)
      have hpr : 2 ^ (P.rank r + 1) ≤ 2 ^ P.rank a := Nat.pow_le_pow_right (by omega) (by omega)
      have hpow : 2 ^ P.rank a = 2 ^ n := congrArg (2 ^ ·) h
      rw [pow_succ]
      omega

/-- A concrete exponential upper bound on the number of local transitions. -/
theorem EntryProgram.terminates_bounded (P : EntryProgram A R) (c : EntryConfig A R) :
    ∃ t v, t ≤ P.work c ∧ P.step^[t] c = .ret v [] := by
  induction hw : P.work c using Nat.strong_induction_on generalizing c with
  | h w ih =>
    by_cases hc : c.Halted
    · cases c with
      | eval a stack => exact hc.elim
      | ret v stack => cases stack with
        | nil => exact ⟨0, v, Nat.zero_le _, rfl⟩
        | cons f stack => exact hc.elim
    · obtain ⟨t, v, htw, ht⟩ := ih _ (hw ▸ P.work_step_lt c hc) (P.step c) rfl
      refine ⟨t + 1, v, ?_, by simpa [Function.iterate_succ_apply] using ht⟩
      have := P.work_step_lt c hc
      omega

end SparseIrred.UpperBounds.Section4
