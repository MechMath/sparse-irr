import SparseIrred.UpperBounds.Section4.EntryMachineEncodedBerkowitz
import SparseIrred.UpperBounds.Machine.CutoffParameters

/-! # Binary instructions and polynomial-time address manipulation primitives -/

namespace SparseIrred.UpperBounds.Section4

open Complexity SparseDiv SparseDiv.StringArith SparseGcd

def EntryInstruction.binaryCode {A R : Type*} (encA : A → List Bool) (encR : R → List Bool) :
    EntryInstruction A R → List Bool
  | .value v => false :: encR v
  | .branch op l r => true :: op.code :: pair (encA l) (encA r)

def binaryValue (v : List Bool) : List Bool := false :: v

def binaryBranch (op : BinaryOp) (l r : List Bool) : List Bool :=
  true :: op.code :: pair l r

def binaryField (i : ℕ) (s : List Bool) : List Bool := pairFst ((pairSnd^[i]) s)

def binaryFields : List (List Bool) → List Bool
  | [] => []
  | b :: bs => pair b (binaryFields bs)

@[simp] theorem binary_pairFst_nil : pairFst [] = [] := rfl
@[simp] theorem binary_pairSnd_nil : pairSnd [] = [] := rfl

theorem binaryFields_eq_frame (bs : List (List Bool)) : binaryFields bs = frame bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [binaryFields, frame_cons, pair, ih]

theorem binaryFields_encNat (xs : List ℕ) : binaryFields (xs.map encNat) = encodeNumerals xs := by
  rw [binaryFields_eq_frame]
  rfl

@[simp] theorem binaryField_binaryFields (i : ℕ) (xs : List (List Bool)) :
    binaryField i (binaryFields xs) = xs[i]?.getD [] := by
  induction i generalizing xs with
  | zero => cases xs <;> simp [binaryField, binaryFields]
  | succ i ih =>
    cases xs with
    | nil =>
      have hnil : (pairSnd^[i]) [] = [] := Function.iterate_fixed (show pairSnd [] = [] from rfl) i
      simp [binaryField, binaryFields, Function.iterate_succ_apply, hnil]
    | cons x xs => simpa [binaryField, binaryFields, Function.iterate_succ_apply] using ih xs

def binaryEq (a b x y : List Bool) : List Bool := if decNat a = decNat b then x else y
def binaryLt (a b x y : List Bool) : List Bool := if decNat a < decNat b then x else y
def binaryBit (a x y : List Bool) : List Bool := if a.headD false then x else y

theorem cobham_binaryValue {n : ℕ} {f : (Fin n → List Bool) → List Bool} (hf : Cobham f) :
    Cobham fun v ↦ binaryValue (f v) := cobham_cons false hf

theorem cobham_binaryBranch {n : ℕ} (op : BinaryOp)
    {f g : (Fin n → List Bool) → List Bool} (hf : Cobham f) (hg : Cobham g) :
    Cobham fun v ↦ binaryBranch op (f v) (g v) :=
  cobham_cons true (cobham_cons op.code (cobham_pair_comp hf hg))

theorem cobham_binaryField {n : ℕ} (i : ℕ)
    {f : (Fin n → List Bool) → List Bool} (hf : Cobham f) :
    Cobham fun v ↦ binaryField i (f v) := by
  apply cobham_pairFst_comp
  induction i with
  | zero => exact hf
  | succ i ih =>
    simpa only [Function.iterate_succ_apply'] using cobham_pairSnd_comp ih

theorem cobham_binaryFields {n : ℕ} (fs : List ((Fin n → List Bool) → List Bool))
    (hf : ∀ f ∈ fs, Cobham f) : Cobham fun v ↦ binaryFields (fs.map (fun f ↦ f v)) := by
  induction fs with
  | nil => exact Cobham.const []
  | cons f fs ih =>
    exact cobham_pair_comp (hf f (by simp))
      (ih (fun g hg ↦ hf g (by simp [hg])))

theorem cobham_binaryEq {n : ℕ} {a b x y : (Fin n → List Bool) → List Bool}
    (ha : Cobham a) (hb : Cobham b) (hx : Cobham x) (hy : Cobham y) :
    Cobham fun v ↦ binaryEq (a v) (b v) (x v) (y v) := by
  refine (Cobham.iteFn (cobham_eqBits_comp ha hb) hx hy).of_eq ?_
  intro v
  rcases eqBits_flag (a v) (b v) with h | h
  · have he := (eqBits_eq_true_iff _ _).mp h
    simp [binaryEq, he, h, caseBit₀]
  · have he : decNat (a v) ≠ decNat (b v) := by
      intro he
      have := (eqBits_eq_true_iff _ _).mpr he
      rw [h] at this
      contradiction
    simp [binaryEq, he, h, caseBit₀]

theorem cobham_binaryLt {n : ℕ} {a b x y : (Fin n → List Bool) → List Bool}
    (ha : Cobham a) (hb : Cobham b) (hx : Cobham x) (hy : Cobham y) :
    Cobham fun v ↦ binaryLt (a v) (b v) (x v) (y v) := by
  refine (Cobham.iteFn (cobham_ltBits_comp ha hb) hx hy).of_eq ?_
  intro v
  rcases ltBits_flag (a v) (b v) with h | h
  · have he := (ltBits_eq_true_iff _ _).mp h
    simp [binaryLt, he, h, caseBit₀]
  · have he := (ltBits_eq_false_iff _ _).mp h
    simp [binaryLt, Nat.not_lt.mpr he, h, caseBit₀]

theorem cobham_binaryBit {n : ℕ} {a x y : (Fin n → List Bool) → List Bool}
    (ha : Cobham a) (hx : Cobham x) (hy : Cobham y) :
    Cobham fun v ↦ binaryBit (a v) (x v) (y v) := by
  refine (Cobham.iteFn ha hx hy).of_eq ?_
  intro v
  cases h : a v with
  | nil => simp [binaryBit, h, caseBit₀]
  | cons b s => cases b <;> simp [binaryBit, h, caseBit₀]

def binaryInstructionMap (addr scalar : List Bool → List Bool) (s : List Bool) : List Bool :=
  binaryBit s
    (binaryBit s.tail
      (binaryBranch .mul (addr (pairFst s.tail.tail)) (addr (pairSnd s.tail.tail)))
      (binaryBranch .add (addr (pairFst s.tail.tail)) (addr (pairSnd s.tail.tail))))
    (binaryValue (scalar s.tail))

theorem cobham_binaryTail {n : ℕ} {f : (Fin n → List Bool) → List Bool} (hf : Cobham f) :
    Cobham fun v ↦ (f v).tail := by
  simpa only [List.length_cons, List.length_nil, Nat.zero_add, List.drop_one] using
    Cobham.dropFn (Cobham.const [false]) hf

theorem cobham_binaryCompose {n : ℕ} {f : List Bool → List Bool}
    {g : (Fin n → List Bool) → List Bool}
    (hf : Cobham fun v : Fin 1 → List Bool ↦ f (v 0)) (hg : Cobham g) :
    Cobham fun v ↦ f (g v) := (Cobham.comp hf (fun _ ↦ hg)).of_eq (fun _ ↦ rfl)

theorem cobham_binaryInstructionMap {n : ℕ}
    {a r : List Bool → List Bool} {s : (Fin n → List Bool) → List Bool}
    (ha : Cobham fun v : Fin 1 → List Bool ↦ a (v 0))
    (hr : Cobham fun v : Fin 1 → List Bool ↦ r (v 0)) (hs : Cobham s) :
    Cobham fun v ↦ binaryInstructionMap a r (s v) := by
  have ht := cobham_binaryTail hs
  have htt := cobham_binaryTail ht
  have hl := cobham_binaryCompose ha (cobham_pairFst_comp htt)
  have hu := cobham_binaryCompose ha (cobham_pairSnd_comp htt)
  exact cobham_binaryBit hs (cobham_binaryBit ht
    (cobham_binaryBranch .mul hl hu) (cobham_binaryBranch .add hl hu))
    (cobham_binaryValue (cobham_binaryCompose hr ht))

/-- Closure under a unary subroutine that also reads the unchanged environment. -/
def BinaryCobhamFamily {n : ℕ} (f : (Fin n → List Bool) → List Bool → List Bool) : Prop :=
  ∀ g : (Fin n → List Bool) → List Bool, Cobham g → Cobham fun v ↦ f v (g v)

theorem cobham_binaryInstructionMapWith {n : ℕ}
    {a r : (Fin n → List Bool) → List Bool → List Bool}
    {s : (Fin n → List Bool) → List Bool}
    (ha : BinaryCobhamFamily a) (hr : BinaryCobhamFamily r) (hs : Cobham s) :
    Cobham fun v ↦ binaryInstructionMap (a v) (r v) (s v) := by
  have ht := cobham_binaryTail hs
  have htt := cobham_binaryTail ht
  have hl := ha _ (cobham_pairFst_comp htt)
  have hu := ha _ (cobham_pairSnd_comp htt)
  exact cobham_binaryBit hs (cobham_binaryBit ht
    (cobham_binaryBranch .mul hl hu) (cobham_binaryBranch .add hl hu))
    (cobham_binaryValue (hr _ ht))

theorem binaryInstructionMap_eq {A B R S : Type*} (encA : A → List Bool) (encB : B → List Bool)
    (encR : R → List Bool) (encS : S → List Bool) (a : A → B) (r : R → S)
    (addr scalar : List Bool → List Bool)
    (ha : ∀ x, addr (encA x) = encB (a x)) (hr : ∀ x, scalar (encR x) = encS (r x))
    (i : EntryInstruction A R) :
    binaryInstructionMap addr scalar (i.binaryCode encA encR) =
      (match i with
       | .value v => (EntryInstruction.value (r v) : EntryInstruction B S)
       | .branch op l u => .branch op (a l) (a u)).binaryCode
        encB encS := by
  cases i with
  | value v => simp [binaryInstructionMap, binaryBit, EntryInstruction.binaryCode, binaryValue, hr]
  | branch op l u => cases op <;>
      simp [binaryInstructionMap, binaryBit, EntryInstruction.binaryCode, binaryBranch, BinaryOp.code, ha]

end SparseIrred.UpperBounds.Section4
