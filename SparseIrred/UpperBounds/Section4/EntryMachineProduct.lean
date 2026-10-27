import SparseIrred.UpperBounds.Section4.StackEvaluator
import SparseIrred.UpperBounds.SuccinctMatrix

/-!
# Balanced product entries as a finite-stack program

An address names a product entry or a partial scalar product. Splitting both the
matrix interval and the summation interval gives logarithmic nesting in each
parameter, without storing a dense matrix or an unfolded expression tree.
-/

namespace SparseIrred.UpperBounds.Section4

open Matrix

inductive ProductAddress (n : ℕ) where
  | entry (start len : ℕ) (i j : Fin n)
  | sum (start len : ℕ) (i j : Fin n) (lo count : ℕ)
  | zero
  deriving DecidableEq

variable {R : Type*} [Semiring R] {n : ℕ}

private theorem splitDepth_halves (e : ℕ) (he : 1 < e) :
    splitDepth (e / 2) < splitDepth e ∧ splitDepth (e - e / 2) < splitDepth e := by
  have hh : splitDepth e = 1 + max (splitDepth (e / 2)) (splitDepth (e - e / 2)) := by
    rw [splitDepth, if_neg (by omega)]
  omega

/-- The instruction requests at most one entry of the input matrix sequence. -/
def productInstruction (A : ℕ → Matrix (Fin n) (Fin n) R) :
    ProductAddress n → EntryInstruction (ProductAddress n) R
  | .zero => .value 0
  | .entry start len i j =>
    if len = 0 then .value ((1 : Matrix (Fin n) (Fin n) R) i j)
    else if len = 1 then .value (A start i j)
    else .branch .add (.sum start len i j 0 n) .zero
  | .sum start len i j lo count =>
    if len ≤ 1 then .value 0
    else if count = 0 then .value 0
    else if count = 1 then
      if h : lo < n then .branch .mul
        (.entry start (len / 2) i ⟨lo, h⟩)
        (.entry (start + len / 2) (len - len / 2) ⟨lo, h⟩ j)
      else .value 0
    else .branch .add
      (.sum start len i j lo (count / 2))
      (.sum start len i j (lo + count / 2) (count - count / 2))

/-- A polynomial in the binary lengths of dimension and product length. -/
def productRank : ProductAddress n → ℕ
  | .zero => 0
  | .entry _ len _ _ => (splitDepth len + 1) * (splitDepth n + 2) + 1
  | .sum _ len _ _ _ count => splitDepth len * (splitDepth n + 2) + splitDepth count + 1

theorem productInstruction_descend (A : ℕ → Matrix (Fin n) (Fin n) R)
    (a : ProductAddress n) (op : BinaryOp) (l r : ProductAddress n)
    (h : productInstruction A a = .branch op l r) :
    productRank l < productRank a ∧ productRank r < productRank a := by
  cases a with
  | zero => simp [productInstruction] at h
  | entry start len i j =>
    simp only [productInstruction] at h
    split_ifs at h <;> try cases h
    simp only [productRank]
    constructor <;> nlinarith
  | sum start len i j lo count =>
    simp only [productInstruction] at h
    split_ifs at h with he hc0 hc1 hlo <;> try cases h
    · have hd := splitDepth_halves len (by omega)
      simp only [productRank]
      subst count
      have hs : splitDepth 1 = 1 := by rw [splitDepth]; norm_num
      rw [hs]
      constructor <;> nlinarith
    · have hd := splitDepth_halves count (by omega)
      simp only [productRank]
      omega

/-- The actual address machine for an ordered matrix product. -/
def productProgram (A : ℕ → Matrix (Fin n) (Fin n) R) : EntryProgram (ProductAddress n) R :=
  ⟨productInstruction A, productRank, productInstruction_descend A⟩

/-- Mathematical meaning of an address, including the partial-sum addresses. -/
def productAddressValue (A : ℕ → Matrix (Fin n) (Fin n) R) : ProductAddress n → R
  | .zero => 0
  | .entry start len i j => intervalProduct A start len i j
  | .sum start len i j lo count =>
    if len ≤ 1 then 0 else
      ∑ k ∈ Finset.range count, if h : lo + k < n then
        intervalProduct A start (len / 2) i ⟨lo + k, h⟩ *
        intervalProduct A (start + len / 2) (len - len / 2) ⟨lo + k, h⟩ j
      else 0

private theorem rangeSum_split (f : ℕ → R) (lo count : ℕ) :
    (∑ k ∈ Finset.range count, f (lo + k)) =
      (∑ k ∈ Finset.range (count / 2), f (lo + k)) +
      ∑ k ∈ Finset.range (count - count / 2), f (lo + count / 2 + k) := by
  conv_lhs => rw [← Nat.add_sub_of_le (Nat.div_le_self count 2)]
  rw [Finset.sum_range_add]
  simp [Nat.add_assoc]

theorem productAddressValue_equations (A : ℕ → Matrix (Fin n) (Fin n) R)
    (a : ProductAddress n) :
    productAddressValue A a = match productInstruction A a with
      | .value v => v
      | .branch op l r => op.apply (productAddressValue A l) (productAddressValue A r) := by
  cases a with
  | zero => rfl
  | entry start len i j =>
    simp only [productInstruction]
    split_ifs with h0 h1
    · subst len
      rfl
    · subst len
      simp [productAddressValue, intervalProduct]
    · simp only [BinaryOp.apply, productAddressValue, if_neg (show ¬len ≤ 1 by omega), add_zero,
        Nat.zero_add]
      conv_lhs => rw [← Nat.add_sub_of_le (Nat.div_le_self len 2)]
      rw [intervalProduct_split, Matrix.mul_apply]
      rw [Finset.sum_fin_eq_sum_range]
  | sum start len i j lo count =>
    simp only [productInstruction]
    split_ifs with he hc0 hc1 hlo
    · simp [productAddressValue, he]
    · subst count
      simp [productAddressValue, he]
    · subst count
      simp [productAddressValue, he, hlo, BinaryOp.apply]
    · subst count
      simp [productAddressValue, he, hlo]
    · simp only [BinaryOp.apply, productAddressValue, if_neg he]
      exact rangeSum_split (R := R) (fun k ↦ if h : k < n then
        intervalProduct A start (len / 2) i ⟨k, h⟩ *
          intervalProduct A (start + len / 2) (len - len / 2) ⟨k, h⟩ j else 0) lo count

theorem productProgram_value (A : ℕ → Matrix (Fin n) (Fin n) R)
    (start len : ℕ) (i j : Fin n) :
    (productProgram A).value (.entry start len i j) = intervalProduct A start len i j :=
  (productProgram A).value_eq_of_equations (productAddressValue A)
    (by
      intro a
      have h := productAddressValue_equations A a
      cases he : productInstruction A a <;> simpa only [productProgram, he] using h) _

/-- Termination and entry correctness of the explicitly defined stack machine. -/
theorem productProgram_correct (A : ℕ → Matrix (Fin n) (Fin n) R)
    (start len : ℕ) (i j : Fin n) :
    ∃ t, (productProgram A).step^[t] (.eval (.entry start len i j) []) =
      .ret (intervalProduct A start len i j) [] := by
  simpa only [productProgram_value] using (productProgram A).correct (.entry start len i j)

/-- Every intermediate stack has polynomially many address/value frames. -/
theorem productProgram_stack_bound (A : ℕ → Matrix (Fin n) (Fin n) R)
    (start len : ℕ) (i j : Fin n) (t : ℕ) :
    ((productProgram A).step^[t] (.eval (.entry start len i j) [])).stack.length ≤
      (len.log2 + 3) * (n.log2 + 4) + 1 := by
  have h := (productProgram A).stack_length_iterate_le (.entry start len i j) t
  change _ ≤ (splitDepth len + 1) * (splitDepth n + 2) + 1 at h
  have hl := splitDepth_le_log len
  have hn := splitDepth_le_log n
  exact h.trans (by nlinarith)

end SparseIrred.UpperBounds.Section4
