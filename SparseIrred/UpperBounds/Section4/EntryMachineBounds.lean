import SparseIrred.UpperBounds.Section4.EntryMachineProduct
import SparseIrred.UpperBounds.Section4.StackEncoding
import Mathlib.Data.Nat.Bitwise

/-!
# Register bounds for balanced product evaluation

Every address keeps its interval inside the original input interval, and every
partial sum keeps its index interval inside the matrix dimension. These bounds
justify binary address storage throughout the execution.
-/

namespace SparseIrred.UpperBounds.Section4

open Matrix

variable {R : Type*} [Semiring R] {n : ℕ}

/-- Both kinds of interval remain inside their original bounds. -/
def ProductAddress.Bounded (bound : ℕ) : ProductAddress n → Prop
  | .zero => True
  | .entry start len _ _ => start + len ≤ bound
  | .sum start len _ _ lo count => start + len ≤ bound ∧ lo + count ≤ n

theorem productInstruction_bounded (A : ℕ → Matrix (Fin n) (Fin n) R) (bound : ℕ)
    (a : ProductAddress n) (op : BinaryOp) (l r : ProductAddress n)
    (ha : a.Bounded bound) (h : productInstruction A a = .branch op l r) :
    l.Bounded bound ∧ r.Bounded bound := by
  cases a with
  | zero => simp [productInstruction] at h
  | entry start len i j =>
    simp only [productInstruction] at h
    split_ifs at h <;> cases h
    simpa [ProductAddress.Bounded] using ha
  | sum start len i j lo count =>
    simp only [productInstruction] at h
    split_ifs at h <;> cases h
    · simp only [ProductAddress.Bounded] at *
      omega
    · simp only [ProductAddress.Bounded] at *
      omega

/-- All addresses stored in any runtime configuration remain bounded. -/
theorem productProgram_addresses_bounded (A : ℕ → Matrix (Fin n) (Fin n) R)
    (start len : ℕ) (i j : Fin n) (t : ℕ) :
    ((productProgram A).step^[t] (.eval (.entry start len i j) [])).Addresses
      (ProductAddress.Bounded (start + len)) := by
  apply EntryProgram.addresses_iterate
  · intro a op l r ha h
    exact productInstruction_bounded A _ a op l r ha h
  · exact le_rfl

/-- The scalar registers needed to store an address; empty and entry addresses use padding. -/
def ProductAddress.registers : ProductAddress n → List ℕ
  | .zero => [0, 0, 0, 0, 0, 0]
  | .entry start len i j => [start, len, i.val, j.val, 0, 0]
  | .sum start len i j lo count => [start, len, i.val, j.val, lo, count]

@[simp] theorem ProductAddress.registers_length (a : ProductAddress n) : a.registers.length = 6 := by
  cases a <;> rfl

theorem ProductAddress.registers_le (a : ProductAddress n) (bound : ℕ)
    (ha : a.Bounded bound) (v : ℕ) (hv : v ∈ a.registers) : v ≤ bound + n := by
  cases a <;> simp only [ProductAddress.Bounded, registers, List.mem_cons, List.not_mem_nil, or_false] at *
  all_goals rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- Fixed-width little-endian binary storage. -/
def fixedWord (w v : ℕ) : List Bool := List.ofFn (fun i : Fin w ↦ v.testBit i.val)

@[simp] theorem fixedWord_length (w v : ℕ) : (fixedWord w v).length = w := by
  simp [fixedWord]

/-- The fixed-width representation is faithful whenever the register fits. -/
theorem fixedWord_injective (w : ℕ) {u v : ℕ} (hu : u < 2 ^ w) (hv : v < 2 ^ w)
    (h : fixedWord w u = fixedWord w v) : u = v := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < w
  · have hh := congrArg (fun l : List Bool ↦ l[i]?) h
    simpa [fixedWord, hi] using hh
  · have hp : 2 ^ w ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_eq_false_of_lt (hu.trans_le hp),
      Nat.testBit_eq_false_of_lt (hv.trans_le hp)]

/-- The two tag bits are followed by exactly six fixed-width binary registers. -/
def ProductAddress.encode (w : ℕ) (a : ProductAddress n) : List Bool :=
  (match a with
    | .zero => [false, false]
    | .entry _ _ _ _ => [false, true]
    | .sum _ _ _ _ _ _ => [true, false]) ++ (a.registers.map (fixedWord w)).flatten

@[simp] theorem ProductAddress.encode_length (w : ℕ) (a : ProductAddress n) :
    (a.encode w).length = 6 * w + 2 := by
  cases a <;> simp [encode, registers, fixedWord] <;> omega

/-- Every address register fits in the binary width of the global interval bound. -/
theorem ProductAddress.registers_fit (a : ProductAddress n) (bound w : ℕ)
    (ha : a.Bounded bound) (hb : bound + n < 2 ^ w) (v : ℕ) (hv : v ∈ a.registers) :
    v < 2 ^ w := (a.registers_le bound ha v hv).trans_lt hb

/-- A polynomial bound in the binary register width, field width and recursion parameters. -/
theorem productProgram_encoded_space (A : ℕ → Matrix (Fin n) (Fin n) R)
    (encR : R → List Bool) (w qbits : ℕ) (hR : ∀ r, (encR r).length ≤ qbits)
    (start len : ℕ) (i j : Fin n) (t : ℕ) :
    (((productProgram A).step^[t] (.eval (.entry start len i j) [])).encode
      (ProductAddress.encode w) encR).length ≤
      (6 * w + qbits + 2) + (6 * w + qbits + 5) *
        ((len.log2 + 3) * (n.log2 + 4) + 1) + 2 := by
  have hb := productProgram_addresses_bounded A start len i j t
  have hwidth := EntryConfig.encode_length_le (ProductAddress.encode w) encR
    (ProductAddress.Bounded (start + len)) (6 * w + qbits + 2)
    (fun a _ ↦ by simp) (fun r ↦ (hR r).trans (by omega)) _ hb
  have hdepth := productProgram_stack_bound A start len i j t
  exact hwidth.trans (by nlinarith)

end SparseIrred.UpperBounds.Section4
