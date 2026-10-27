import SparseIrred.UpperBounds.Section4.BinaryAddressBasic
import SparseIrred.UpperBounds.Section4.StackFramed

/-!
# A concrete polynomial-time binary stack transition

The transition parses only the active payload and the top continuation. Its
instruction and arithmetic callbacks are individual local operations. They are
instantiated by the binary address and field routines in the final machine.
-/

namespace SparseIrred.UpperBounds.Section4

open Complexity SparseDiv SparseDiv.StringArith

def binaryEval (a stack : List Bool) : List Bool := false :: pair a stack
def binaryReturn (value stack : List Bool) : List Bool := true :: pair value stack

def binaryPushLeft (op right stack : List Bool) : List Bool :=
  true :: pair (false :: (caseBit₀ op [true] [false] ++ right)) stack

def binaryPushRight (op left stack : List Bool) : List Bool :=
  true :: pair (true :: (caseBit₀ op [true] [false] ++ left)) stack

/-- Execute a decoded instruction, pushing one continuation for a binary operation. -/
def binaryExecute (instruction stack : List Bool) : List Bool :=
  caseBit₀ instruction
    (binaryEval (pairFst instruction.tail.tail)
      (binaryPushLeft instruction.tail (pairSnd instruction.tail.tail) stack))
    (binaryReturn instruction.tail stack)

/-- Return from a child: pop a completed operation or begin its pending right child. -/
def binaryResume (add mul : List Bool → List Bool → List Bool)
    (value stack : List Bool) : List Bool :=
  let frame := pairFst stack.tail
  let rest := pairSnd stack.tail
  caseBit₀ stack
    (caseBit₀ frame
      (binaryReturn (caseBit₀ frame.tail (mul frame.tail.tail value)
        (add frame.tail.tail value)) rest)
      (binaryEval frame.tail.tail (binaryPushRight frame.tail value rest)))
    (binaryReturn value stack)

/-- Total binary transition; malformed states also have a defined result. -/
def binaryStackStep (instruction : List Bool → List Bool)
    (add mul : List Bool → List Bool → List Bool) (state : List Bool) : List Bool :=
  let payload := pairFst state.tail
  let stack := pairSnd state.tail
  caseBit₀ state (binaryResume add mul payload stack)
    (binaryExecute (instruction payload) stack)

theorem cobham_binaryEval {n : ℕ} {a s : (Fin n → List Bool) → List Bool}
    (ha : Cobham a) (hs : Cobham s) : Cobham fun v ↦ binaryEval (a v) (s v) :=
  cobham_cons false (cobham_pair_comp ha hs)

theorem cobham_binaryReturn {n : ℕ} {a s : (Fin n → List Bool) → List Bool}
    (ha : Cobham a) (hs : Cobham s) : Cobham fun v ↦ binaryReturn (a v) (s v) :=
  cobham_cons true (cobham_pair_comp ha hs)

theorem cobham_binaryPushLeft {n : ℕ} {o a s : (Fin n → List Bool) → List Bool}
    (ho : Cobham o) (ha : Cobham a) (hs : Cobham s) :
    Cobham fun v ↦ binaryPushLeft (o v) (a v) (s v) :=
  cobham_cons true (cobham_pair_comp (cobham_cons false
    (Cobham.appendFn (Cobham.iteFn ho (.const _) (.const _)) ha)) hs)

theorem cobham_binaryPushRight {n : ℕ} {o a s : (Fin n → List Bool) → List Bool}
    (ho : Cobham o) (ha : Cobham a) (hs : Cobham s) :
    Cobham fun v ↦ binaryPushRight (o v) (a v) (s v) :=
  cobham_cons true (cobham_pair_comp (cobham_cons true
    (Cobham.appendFn (Cobham.iteFn ho (.const _) (.const _)) ha)) hs)

theorem cobham_binaryExecute {n : ℕ} {i s : (Fin n → List Bool) → List Bool}
    (hi : Cobham i) (hs : Cobham s) : Cobham fun v ↦ binaryExecute (i v) (s v) :=
  Cobham.iteFn hi (cobham_binaryEval (cobham_pairFst_comp (hi.tailFn.tailFn))
    (cobham_binaryPushLeft hi.tailFn (cobham_pairSnd_comp (hi.tailFn.tailFn)) hs))
    (cobham_binaryReturn hi.tailFn hs)

theorem cobham_binaryResume {n : ℕ}
    {add mul : (Fin n → List Bool) → List Bool → List Bool → List Bool}
    (ha : Cobham fun u : Fin (n + 2) → List Bool ↦ add (Fin.tail (Fin.tail u)) (u 0) (u 1))
    (hm : Cobham fun u : Fin (n + 2) → List Bool ↦ mul (Fin.tail (Fin.tail u)) (u 0) (u 1))
    {v s : (Fin n → List Bool) → List Bool} (hv : Cobham v) (hs : Cobham s) :
    Cobham fun u ↦ binaryResume (add u) (mul u) (v u) (s u) := by
  have hf := cobham_pairFst_comp hs.tailFn
  have hr := cobham_pairSnd_comp hs.tailFn
  have hargs : ∀ i : Fin (n + 2), Cobham fun u : Fin n → List Bool ↦
      (Fin.cons (pairFst (s u).tail).tail.tail (Fin.cons (v u) u) : Fin (n + 2) → List Bool) i := by
    intro i
    exact Fin.cases hf.tailFn.tailFn (fun j ↦ Fin.cases hv (fun k ↦ .proj k) j) i
  have hadd := (Cobham.comp ha hargs).of_eq (fun _ ↦ rfl)
  have hmul := (Cobham.comp hm hargs).of_eq (fun _ ↦ rfl)
  exact Cobham.iteFn hs (Cobham.iteFn hf
    (cobham_binaryReturn (Cobham.iteFn hf.tailFn hmul hadd) hr)
    (cobham_binaryEval hf.tailFn.tailFn (cobham_binaryPushRight hf.tailFn hv hr)))
    (cobham_binaryReturn hv hs)

theorem cobham_binaryStackStep {n : ℕ}
    {instruction : (Fin n → List Bool) → List Bool → List Bool}
    {add mul : (Fin n → List Bool) → List Bool → List Bool → List Bool}
    (hi : Cobham fun u : Fin (n + 1) → List Bool ↦ instruction (Fin.tail u) (u 0))
    (ha : Cobham fun u : Fin (n + 2) → List Bool ↦ add (Fin.tail (Fin.tail u)) (u 0) (u 1))
    (hm : Cobham fun u : Fin (n + 2) → List Bool ↦ mul (Fin.tail (Fin.tail u)) (u 0) (u 1))
    {s : (Fin n → List Bool) → List Bool} (hs : Cobham s) :
    Cobham fun u ↦ binaryStackStep (instruction u) (add u) (mul u) (s u) := by
  have hp := cobham_pairFst_comp hs.tailFn
  have hstack := cobham_pairSnd_comp hs.tailFn
  have hinst := (Cobham.comp hi (gs := fun i u ↦
    (Fin.cons (pairFst (s u).tail) u : Fin (n + 1) → List Bool) i)
    (fun i ↦ Fin.cases hp (fun j ↦ .proj j) i)).of_eq (fun _ ↦ rfl)
  exact Cobham.iteFn hs (cobham_binaryResume ha hm hp hstack)
    (cobham_binaryExecute hinst hstack)

theorem binaryExecute_correct {A R : Type*} (encA : A → List Bool) (encR : R → List Bool)
    (i : EntryInstruction A R) (stack : List (EntryFrame A R)) :
    binaryExecute (i.binaryCode encA encR) (encodeFramedStack encA encR stack) =
      (match i with
      | .value v => EntryConfig.ret v stack
      | .branch op l r => .eval l (.left op r :: stack)).framedEncode encA encR := by
  cases i with
  | value v => rfl
  | branch op l r =>
    cases op <;> simp [binaryExecute, EntryInstruction.binaryCode, caseBit₀, BinaryOp.code,
      binaryEval, binaryPushLeft, EntryConfig.framedEncode, encodeFramedStack, EntryFrame.encode]

/-- The concrete binary transition realizes exactly one mathematical stack step. -/
theorem binaryStackStep_correct {A R : Type*} [Add R] [Mul R] (P : EntryProgram A R)
    (encA : A → List Bool) (encR : R → List Bool)
    (instruction : List Bool → List Bool) (add mul : List Bool → List Bool → List Bool)
    (hi : ∀ a, instruction (encA a) = (P.instruction a).binaryCode encA encR)
    (ha : ∀ a b, add (encR a) (encR b) = encR (a + b))
    (hm : ∀ a b, mul (encR a) (encR b) = encR (a * b)) (c : EntryConfig A R) :
    binaryStackStep instruction add mul (c.framedEncode encA encR) =
      (P.step c).framedEncode encA encR := by
  cases c with
  | eval a stack =>
    simp only [binaryStackStep, EntryConfig.framedEncode, List.tail_cons,
      pairFst_pair, pairSnd_pair, caseBit₀, hi]
    exact binaryExecute_correct encA encR (P.instruction a) stack
  | ret v stack =>
    cases stack with
    | nil => simp [binaryStackStep, binaryResume, EntryConfig.framedEncode,
        encodeFramedStack, caseBit₀, binaryReturn, EntryProgram.step]
    | cons f stack =>
      cases f with
      | left op r =>
        cases op <;> simp [binaryStackStep, binaryResume, EntryConfig.framedEncode,
          encodeFramedStack, EntryFrame.encode, BinaryOp.code, caseBit₀, binaryEval,
          binaryPushRight, EntryProgram.step]
      | right op l =>
        cases op <;> simp [binaryStackStep, binaryResume, EntryConfig.framedEncode,
          encodeFramedStack, EntryFrame.encode, BinaryOp.code, caseBit₀, binaryReturn,
          EntryProgram.step, BinaryOp.apply, ha, hm]

end SparseIrred.UpperBounds.Section4
