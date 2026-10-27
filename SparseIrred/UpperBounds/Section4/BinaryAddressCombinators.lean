import SparseIrred.UpperBounds.Section4.BinaryAddressProduct
import SparseIrred.UpperBounds.Section4.EntryMachineBoolean

/-! # Binary dispatch for the finite composition of arithmetic address programs -/

namespace SparseIrred.UpperBounds.Section4

open Complexity SparseDiv SparseDiv.StringArith SparseGcd

def binaryPrefix (pref s : List Bool) : List Bool := pref ++ s

def binaryLift (pref : List Bool) (ins : List Bool) : List Bool :=
  binaryInstructionMap (binaryPrefix pref) id ins

theorem binaryLift_eq {A B R : Type*} (ea : A → List Bool) (eb : B → List Bool)
    (er : R → List Bool) (f : A → B) (pref : List Bool)
    (hf : ∀ a, pref ++ ea a = eb (f a)) (ins : EntryInstruction A R) :
    binaryLift pref (ins.binaryCode ea er) =
      (match ins with
      | .value r => (EntryInstruction.value r : EntryInstruction B R)
      | .branch op a b => .branch op (f a) (f b)).binaryCode eb er :=
  binaryInstructionMap_eq ea eb er er f id (binaryPrefix pref) id hf (fun _ ↦ rfl) ins

theorem cobham_binaryLift {n : ℕ} (pref : List Bool)
    {s : (Fin n → List Bool) → List Bool} (hs : Cobham s) :
    Cobham fun v ↦ binaryLift pref (s v) :=
  cobham_binaryInstructionMap (Cobham.appendFn (Cobham.const pref) (.proj 0)) (.proj 0) hs

def binaryTestInstruction (inner : List Bool → List Bool) (initial addr : List Bool) : List Bool :=
  binaryBit addr
    (binaryInstructionMap (binaryPrefix [true]) (binaryPrefix [false]) (inner addr.tail))
    (binaryBit addr.tail (binaryValue [true, true])
      (binaryBranch .mul [false, true] (true :: initial)))

theorem binaryTestInstruction_eq {A K : Type*} [Zero K] [DecidableEq K]
    (P : EntryProgram A K) (initial : A) (ea : A → List Bool) (er : K → List Bool)
    (inner : List Bool → List Bool)
    (hi : ∀ a, inner (ea a) = (P.instruction a).binaryCode ea er) (a : TestAddress A) :
    binaryTestInstruction inner (ea initial) (a.binaryCode ea) =
      ((nonzeroProgram P initial).instruction a).binaryCode
        (TestAddress.binaryCode ea) (DecisionScalar.binaryCode er) := by
  cases a with
  | test | tag => rfl
  | call a =>
    simp only [binaryTestInstruction, TestAddress.binaryCode, binaryBit, List.headD_cons,
      List.tail_cons, ↓reduceIte, hi]
    have h := binaryInstructionMap_eq ea (TestAddress.binaryCode ea) er
      (DecisionScalar.binaryCode er) TestAddress.call DecisionScalar.scalar
      (binaryPrefix [true]) (binaryPrefix [false]) (fun _ ↦ rfl) (fun _ ↦ rfl) (P.instruction a)
    cases he : P.instruction a <;> simpa [nonzeroProgram, he] using h

def binaryBinaryInstruction (op : BinaryOp) (left right : List Bool → List Bool)
    (linit rinit addr : List Bool) : List Bool :=
  binaryBit addr (binaryLift [true] (right addr.tail))
    (binaryBit addr.tail (binaryLift [false, true] (left addr.tail.tail))
      (binaryBranch op (false :: true :: linit) (true :: rinit)))

theorem binaryBinaryInstruction_eq {A B R : Type*} [Add R] [Mul R]
    (op : BinaryOp) (P : EntryProgram A R) (Q : EntryProgram B R) (ai : A) (bi : B)
    (ea : A → List Bool) (eb : B → List Bool) (er : R → List Bool)
    (left right : List Bool → List Bool)
    (hl : ∀ a, left (ea a) = (P.instruction a).binaryCode ea er)
    (hr : ∀ b, right (eb b) = (Q.instruction b).binaryCode eb er)
    (a : BinaryAddress A B) :
    binaryBinaryInstruction op left right (ea ai) (eb bi) (a.binaryCode ea eb) =
      ((binaryProgram op P Q ai bi).instruction a).binaryCode
        (BinaryAddress.binaryCode ea eb) er := by
  cases a with
  | root => rfl
  | left a =>
    simp only [binaryBinaryInstruction, BinaryAddress.binaryCode, binaryBit, List.headD_cons,
      List.tail_cons, ↓reduceIte, hl]
    have h := binaryLift_eq ea (BinaryAddress.binaryCode ea eb) er BinaryAddress.left
      [false, true] (fun _ ↦ rfl) (P.instruction a)
    cases he : P.instruction a <;> simpa [binaryProgram, he] using h
  | right b =>
    simp only [binaryBinaryInstruction, BinaryAddress.binaryCode, binaryBit, List.headD_cons,
      List.tail_cons, ↓reduceIte, hr]
    have h := binaryLift_eq eb (BinaryAddress.binaryCode ea eb) er BinaryAddress.right
      [true] (fun _ ↦ rfl) (Q.instruction b)
    cases he : Q.instruction b <;> simpa [binaryProgram, he] using h

def binaryOrRange (lo count : List Bool) : List Bool :=
  false :: binaryFields [lo, count]
def binaryOrCall (i a : List Bool) : List Bool := true :: false :: pair i a

def binaryFamilyInstruction (inner : List Bool → List Bool) (addr : List Bool) : List Bool :=
  binaryInstructionMap (fun a ↦ pair (pairFst addr) a) id (inner addr)

def binaryOrInstruction (inner : List Bool → List Bool)
    (dim initial addr : List Bool) : List Bool :=
  let lo := binaryField 0 addr.tail
  let count := binaryField 1 addr.tail
  binaryBit addr
    (binaryBit addr.tail (binaryValue [true, false, false])
      (binaryLift [true, false] (binaryFamilyInstruction inner addr.tail.tail)))
    (binaryEq count (encNat 0) (binaryValue [true, false, false])
      (binaryEq count (encNat 1)
        (binaryLt lo dim (binaryBranch .add (binaryOrCall lo initial) [true, true])
          (binaryValue [true, false, false]))
        (binaryBranch .add (binaryOrRange lo (binaryNatHalf count))
          (binaryOrRange (binaryNatAdd lo (binaryNatHalf count))
            (binaryNatSub count (binaryNatHalf count))))))

theorem binaryOrInstruction_eq {K : Type*} [Add K] [Mul K] [Zero K] [DecidableEq K]
    {m : ℕ} {A : Fin m → Type*} (P : ∀ i, EntryProgram (A i) (DecisionScalar K))
    (initial : ∀ i, A i) (bound : ℕ) (hb : ∀ i, (P i).rank (initial i) ≤ bound)
    (ea : ∀ i, A i → List Bool) (er : K → List Bool) (initialCode : List Bool)
    (hinit : ∀ i, ea i (initial i) = initialCode) (inner : List Bool → List Bool)
    (hi : ∀ i a, inner (pair (encNat i.val) (ea i a)) =
      ((P i).instruction a).binaryCode (ea i) (DecisionScalar.binaryCode er))
    (a : OrAddress A) :
    binaryOrInstruction inner (encNat m) initialCode (a.binaryCode ea) =
      ((orProgram P initial bound hb).instruction a).binaryCode
        (OrAddress.binaryCode ea) (DecisionScalar.binaryCode er) := by
  have hcode : ∀ xs : List ℕ, encodeNumerals xs = binaryFields (xs.map encNat) :=
    fun xs ↦ (binaryFields_encNat xs).symm
  cases a with
  | zero => rfl
  | call i a =>
    simp only [binaryOrInstruction, OrAddress.binaryCode, binaryBit, List.headD_cons,
      List.tail_cons, ↓reduceIte, familyCode, binaryLift, binaryFamilyInstruction, hi]
    rw [binaryInstructionMap_eq (ea i) (fun a ↦ pair (encNat i.val) (ea i a))
      (DecisionScalar.binaryCode er) (DecisionScalar.binaryCode er) id id
      (fun b ↦ pair (pairFst (pair (encNat i.val) (ea i a))) b) id
      (by intro; simp) (fun _ ↦ rfl)]
    cases he : (P i).instruction a with
    | value v => simp [he, binaryInstructionMap, binaryBit, EntryInstruction.binaryCode,
        binaryValue, orProgram]
    | branch op l r => cases op <;> simp [he, binaryInstructionMap, binaryBit,
        EntryInstruction.binaryCode, binaryBranch, binaryPrefix, orProgram,
        OrAddress.binaryCode, familyCode, BinaryOp.code]
  | range lo count =>
    simp only [binaryOrInstruction, OrAddress.binaryCode, binaryBit, List.headD_cons,
      List.tail_cons, ↓reduceIte, hcode, List.map_cons, List.map_nil,
      binaryField_binaryFields, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, binaryEq, binaryLt, decNat_encNat]
    by_cases h0 : count = 0
    · simp [h0, binaryValue, orProgram, EntryInstruction.binaryCode, DecisionScalar.binaryCode]
    · by_cases h1 : count = 1
      · by_cases hl : lo < m
        all_goals simp [h0, h1, hl, binaryValue, binaryBranch, binaryOrCall, orProgram,
          EntryInstruction.binaryCode, OrAddress.binaryCode, DecisionScalar.binaryCode,
          familyCode, hinit]
      · simp [h0, h1, binaryBranch, binaryOrRange, orProgram, EntryInstruction.binaryCode,
          OrAddress.binaryCode, hcode]

theorem cobham_binaryTestInstruction {n : ℕ}
    {inner : (Fin n → List Bool) → List Bool → List Bool} (hi : BinaryCobhamFamily inner)
    {initial addr : (Fin n → List Bool) → List Bool} (hn : Cobham initial) (ha : Cobham addr) :
    Cobham fun v ↦ binaryTestInstruction (inner v) (initial v) (addr v) := by
  have ht := cobham_binaryTail ha
  exact cobham_binaryBit ha
    (cobham_binaryInstructionMap (cobham_cons true (.proj 0))
      (cobham_cons false (.proj 0)) (hi _ ht))
    (cobham_binaryBit ht (Cobham.const (binaryValue [true, true]))
      (cobham_binaryBranch .mul (.const [false, true]) (cobham_cons true hn)))

theorem cobham_binaryBinaryInstruction {n : ℕ} (op : BinaryOp)
    {left right : (Fin n → List Bool) → List Bool → List Bool}
    (hl : BinaryCobhamFamily left) (hr : BinaryCobhamFamily right)
    {li ri addr : (Fin n → List Bool) → List Bool}
    (hli : Cobham li) (hri : Cobham ri) (ha : Cobham addr) :
    Cobham fun v ↦ binaryBinaryInstruction op (left v) (right v) (li v) (ri v) (addr v) := by
  have ht := cobham_binaryTail ha
  exact cobham_binaryBit ha (cobham_binaryLift [true] (hr _ ht))
    (cobham_binaryBit ht (cobham_binaryLift [false, true] (hl _ (cobham_binaryTail ht)))
      (cobham_binaryBranch op (cobham_cons false (cobham_cons true hli)) (cobham_cons true hri)))

theorem cobham_binaryFamilyInstruction {n : ℕ}
    {inner : (Fin n → List Bool) → List Bool → List Bool} (hi : BinaryCobhamFamily inner)
    {addr : (Fin n → List Bool) → List Bool} (ha : Cobham addr) :
    Cobham fun v ↦ binaryFamilyInstruction (inner v) (addr v) :=
  cobham_binaryInstructionMapWith
    (fun _ hq ↦ cobham_pair_comp (cobham_pairFst_comp ha) hq) (fun _ hq ↦ hq) (hi _ ha)

theorem cobham_binaryOrRange {n : ℕ} {l c : (Fin n → List Bool) → List Bool}
    (hl : Cobham l) (hc : Cobham c) : Cobham fun v ↦ binaryOrRange (l v) (c v) :=
  cobham_cons false (cobham_pair_comp hl (cobham_pair_comp hc (.const [])))

theorem cobham_binaryOrCall {n : ℕ} {i a : (Fin n → List Bool) → List Bool}
    (hi : Cobham i) (ha : Cobham a) : Cobham fun v ↦ binaryOrCall (i v) (a v) :=
  cobham_cons true (cobham_cons false (cobham_pair_comp hi ha))

theorem cobham_binaryOrInstruction {n : ℕ}
    {inner : (Fin n → List Bool) → List Bool → List Bool} (hi : BinaryCobhamFamily inner)
    {dim initial addr : (Fin n → List Bool) → List Bool}
    (hd : Cobham dim) (hn : Cobham initial) (ha : Cobham addr) :
    Cobham fun v ↦ binaryOrInstruction (inner v) (dim v) (initial v) (addr v) := by
  have ht := cobham_binaryTail ha
  have hl := cobham_binaryField 0 ht
  have hc := cobham_binaryField 1 ht
  have hh := cobham_binaryNatHalf hc
  have hz : Cobham (n := n) (fun _ ↦ binaryValue [true, false, false]) := .const _
  exact cobham_binaryBit ha (cobham_binaryBit ht hz
    (cobham_binaryLift [true, false] (cobham_binaryFamilyInstruction hi (cobham_binaryTail ht))))
    (cobham_binaryEq hc (.const (encNat 0)) hz
      (cobham_binaryEq hc (.const (encNat 1))
        (cobham_binaryLt hl hd
          (cobham_binaryBranch .add (cobham_binaryOrCall hl hn) (.const [true, true])) hz)
        (cobham_binaryBranch .add (cobham_binaryOrRange hl hh)
          (cobham_binaryOrRange (cobham_binaryNatAdd hl hh) (cobham_binaryNatSub hc hh)))))

end SparseIrred.UpperBounds.Section4
