import SparseIrred.UpperBounds.Section4.BinaryStack

/-! # Binary arithmetic and Boolean tags used by the actual decision stack -/

namespace SparseIrred.UpperBounds.Section4

open Complexity SparseDiv SparseDiv.StringArith

def binaryDecisionFlag (b : List Bool) : List Bool :=
  true :: false :: caseBit₀ b [true] [false]

def binaryDecisionAdd (add : List Bool → List Bool → List Bool) (a b : List Bool) : List Bool :=
  caseBit₀ a
    (caseBit₀ b
      (caseBit₀ (orBit a.tail b.tail) (binaryDecisionFlag [false])
        (binaryDecisionFlag (orBit a.tail.tail b.tail.tail)))
      (binaryDecisionFlag [false]))
    (caseBit₀ b (binaryDecisionFlag [false]) (false :: add a.tail b.tail))

def binaryDecisionMul (mul : List Bool → List Bool → List Bool)
    (zero : List Bool → List Bool) (a b : List Bool) : List Bool :=
  caseBit₀ a
    (caseBit₀ b
      (caseBit₀ (orBit a.tail b.tail) (binaryDecisionFlag [false])
        (binaryDecisionFlag (andBit a.tail.tail b.tail.tail)))
      (caseBit₀ a.tail (binaryDecisionFlag (notBit (zero b.tail)))
        (binaryDecisionFlag [false])))
    (caseBit₀ b (binaryDecisionFlag [false]) (false :: mul a.tail b.tail))

theorem cobham_binaryDecisionFlag {n : ℕ} {b : (Fin n → List Bool) → List Bool}
    (hb : Cobham b) : Cobham fun u ↦ binaryDecisionFlag (b u) :=
  cobham_cons true (cobham_cons false (Cobham.iteFn hb (.const _) (.const _)))

theorem cobham_binaryDecisionAdd {n : ℕ}
    {add : (Fin n → List Bool) → List Bool → List Bool → List Bool}
    (ha : Cobham fun u : Fin (n + 2) → List Bool ↦ add (Fin.tail (Fin.tail u)) (u 0) (u 1))
    {a b : (Fin n → List Bool) → List Bool} (hx : Cobham a) (hy : Cobham b) :
    Cobham fun u ↦ binaryDecisionAdd (add u) (a u) (b u) := by
  have hadd := (Cobham.comp ha (gs := fun i u ↦
    (Fin.cons (a u).tail (Fin.cons (b u).tail u) : Fin (n + 2) → List Bool) i)
    (fun i ↦ Fin.cases hx.tailFn (fun j ↦ Fin.cases hy.tailFn (fun k ↦ .proj k) j) i)).of_eq
      (fun _ ↦ rfl)
  exact Cobham.iteFn hx (Cobham.iteFn hy
    (Cobham.iteFn (Cobham.orFn hx.tailFn hy.tailFn) (.const _)
      (cobham_binaryDecisionFlag (Cobham.orFn hx.tailFn.tailFn hy.tailFn.tailFn))) (.const _))
    (Cobham.iteFn hy (.const _) (cobham_cons false hadd))

theorem cobham_binaryDecisionMul {n : ℕ}
    {mul : (Fin n → List Bool) → List Bool → List Bool → List Bool}
    {zero : (Fin n → List Bool) → List Bool → List Bool}
    (hm : Cobham fun u : Fin (n + 2) → List Bool ↦ mul (Fin.tail (Fin.tail u)) (u 0) (u 1))
    (hz : Cobham fun u : Fin (n + 1) → List Bool ↦ zero (Fin.tail u) (u 0))
    {a b : (Fin n → List Bool) → List Bool} (hx : Cobham a) (hy : Cobham b) :
    Cobham fun u ↦ binaryDecisionMul (mul u) (zero u) (a u) (b u) := by
  have hmul := (Cobham.comp hm (gs := fun i u ↦
    (Fin.cons (a u).tail (Fin.cons (b u).tail u) : Fin (n + 2) → List Bool) i)
    (fun i ↦ Fin.cases hx.tailFn (fun j ↦ Fin.cases hy.tailFn (fun k ↦ .proj k) j) i)).of_eq
      (fun _ ↦ rfl)
  have hzero := (Cobham.comp hz (gs := fun i u ↦
    (Fin.cons (b u).tail u : Fin (n + 1) → List Bool) i)
    (fun i ↦ Fin.cases hy.tailFn (fun j ↦ .proj j) i)).of_eq (fun _ ↦ rfl)
  exact Cobham.iteFn hx (Cobham.iteFn hy
    (Cobham.iteFn (Cobham.orFn hx.tailFn hy.tailFn) (.const _)
      (cobham_binaryDecisionFlag (Cobham.andFn hx.tailFn.tailFn hy.tailFn.tailFn)))
    (Cobham.iteFn hx.tailFn (cobham_binaryDecisionFlag (Cobham.notFn hzero)) (.const _)))
    (Cobham.iteFn hy (.const _) (cobham_cons false hmul))

theorem binaryDecisionAdd_correct {K : Type*} [Add K] [Mul K] [Zero K] [DecidableEq K]
    (enc : K → List Bool) (add : List Bool → List Bool → List Bool)
    (ha : ∀ a b, add (enc a) (enc b) = enc (a + b)) (a b : DecisionScalar K) :
    binaryDecisionAdd add (a.binaryCode enc) (b.binaryCode enc) = (a + b).binaryCode enc := by
  cases a <;> cases b <;>
    simp [binaryDecisionAdd, binaryDecisionFlag, DecisionScalar.binaryCode, caseBit₀,
      orBit, ha] <;> try rfl
  all_goals split_ifs <;> simp_all

theorem binaryDecisionMul_correct {K : Type*} [Add K] [Mul K] [Zero K] [DecidableEq K]
    (enc : K → List Bool) (mul : List Bool → List Bool → List Bool)
    (zero : List Bool → List Bool)
    (hm : ∀ a b, mul (enc a) (enc b) = enc (a * b))
    (hz : ∀ a, zero (enc a) = [decide (a = 0)]) (a b : DecisionScalar K) :
    binaryDecisionMul mul zero (a.binaryCode enc) (b.binaryCode enc) = (a * b).binaryCode enc := by
  cases a <;> cases b <;>
    simp [binaryDecisionMul, binaryDecisionFlag, DecisionScalar.binaryCode, caseBit₀,
      orBit, andBit, notBit, hm, hz] <;> try rfl
  all_goals split_ifs <;> simp_all

end SparseIrred.UpperBounds.Section4
