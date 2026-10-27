import SparseIrred.UpperBounds.Section4.EntryMachineBounds

/-! # Matrix powers evaluated by the concrete address-stack machine -/

namespace SparseIrred.UpperBounds.Section4

open Matrix

variable {R : Type*} [Semiring R] {n : ℕ}

@[simp] theorem intervalProduct_const_fin (A : Matrix (Fin n) (Fin n) R) (start len : ℕ) :
    intervalProduct (fun _ ↦ A) start len = A ^ len := by
  induction len generalizing start with
  | zero => simp [intervalProduct]
  | succ len ih => simp [intervalProduct, ih, pow_succ']

/-- A matrix power uses the product machine with a constant sequence of factors. -/
def powerProgram (A : Matrix (Fin n) (Fin n) R) : EntryProgram (ProductAddress n) R :=
  productProgram (fun _ ↦ A)

@[simp] theorem powerProgram_value (A : Matrix (Fin n) (Fin n) R) (e : ℕ) (i j : Fin n) :
    (powerProgram A).value (.entry 0 e i j) = (A ^ e) i j := by
  simpa only [powerProgram, intervalProduct_const_fin] using
    productProgram_value (fun _ ↦ A) 0 e i j

/-- The machine returns an actual matrix-power entry, including exponent zero. -/
theorem powerProgram_correct (A : Matrix (Fin n) (Fin n) R) (e : ℕ) (i j : Fin n) :
    ∃ t, (powerProgram A).step^[t] (.eval (.entry 0 e i j) []) = .ret ((A ^ e) i j) [] := by
  simpa only [powerProgram, intervalProduct_const_fin] using
    productProgram_correct (fun _ ↦ A) 0 e i j

/-- The nesting is polynomial in the binary lengths of exponent and dimension. -/
theorem powerProgram_stack_bound (A : Matrix (Fin n) (Fin n) R)
    (e : ℕ) (i j : Fin n) (t : ℕ) :
    ((powerProgram A).step^[t] (.eval (.entry 0 e i j) [])).stack.length ≤
      (e.log2 + 3) * (n.log2 + 4) + 1 :=
  productProgram_stack_bound (fun _ ↦ A) 0 e i j t

/-- Every intermediate address has bounded interval registers. -/
theorem powerProgram_addresses_bounded (A : Matrix (Fin n) (Fin n) R)
    (e : ℕ) (i j : Fin n) (t : ℕ) :
    ((powerProgram A).step^[t] (.eval (.entry 0 e i j) [])).Addresses
      (ProductAddress.Bounded e) := by
  simpa only [powerProgram, Nat.zero_add] using
    productProgram_addresses_bounded (fun _ ↦ A) 0 e i j t

end SparseIrred.UpperBounds.Section4
