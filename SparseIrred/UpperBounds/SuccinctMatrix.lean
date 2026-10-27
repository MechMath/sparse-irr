module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Tactic

/-!
# Evaluating matrix entries by balanced recursion

The two entry evaluators here implement the recursive identities used in Section 4,
Lemma 17. They request individual input entries and sum over one index at a time.
Their correctness is algebraic: this file does not assert a Turing-machine space bound
or implement the Berkowitz construction of the matrices to be multiplied.
-/

@[expose] public section

namespace SparseIrred.UpperBounds

open Matrix

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Semiring R]

/-- Number of simultaneously nested calls in either balanced entry recursion. -/
def splitDepth (e : ℕ) : ℕ :=
  if e ≤ 1 then 1
  else 1 + max (splitDepth (e / 2)) (splitDepth (e - e / 2))
termination_by e
decreasing_by all_goals omega

/-- Binary-length bound on recursion depth, independent of the number of entries. -/
theorem splitDepth_le_of_le_pow (e b : ℕ) (he : e ≤ 2 ^ b) : splitDepth e ≤ b + 1 := by
  induction b generalizing e with
  | zero =>
    rw [splitDepth]
    simp [show e ≤ 1 by simpa using he]
  | succ b ih =>
    rw [splitDepth]
    split_ifs with h
    · omega
    · have hp : e ≤ 2 * 2 ^ b := by simpa [pow_succ, Nat.mul_comm] using he
      have hu : e / 2 ≤ 2 ^ b := by omega
      have hv : e - e / 2 ≤ 2 ^ b := by omega
      have := ih _ hu
      have := ih _ hv
      omega

/-- Each of the two evaluators has logarithmic stack depth in its exponent/length. -/
theorem splitDepth_le_log (e : ℕ) : splitDepth e ≤ e.log2 + 2 := by
  simpa [Nat.add_assoc] using
    splitDepth_le_of_le_pow e (e.log2 + 1) (Nat.lt_log2_self.le)

/-- An entry of a matrix power, evaluated by splitting the exponent in halves. -/
def powerEntry (A : Matrix ι ι R) (e : ℕ) (i j : ι) : R :=
  if e = 0 then (1 : Matrix ι ι R) i j
  else if e = 1 then A i j
  else ∑ r, powerEntry A (e / 2) i r * powerEntry A (e - e / 2) r j
termination_by e
decreasing_by all_goals omega

/-- Correctness of the repeated-squaring entry oracle, also for exponent zero. -/
theorem powerEntry_eq (A : Matrix ι ι R) (e : ℕ) (i j : ι) :
    powerEntry A e i j = (A ^ e) i j := by
  induction e using Nat.strong_induction_on generalizing i j with
  | h e ih =>
    rw [powerEntry]
    split_ifs with h₀ h₁
    · subst e
      simp
    · subst e
      simp
    · have hu : e / 2 < e := by omega
      have hv : e - e / 2 < e := by omega
      simp_rw [ih _ hu, ih _ hv]
      rw [← Matrix.mul_apply, ← pow_add, Nat.add_sub_of_le (Nat.div_le_self _ _)]

/-- The left-to-right product of an interval of a sequence of matrices. -/
def intervalProduct (A : ℕ → Matrix ι ι R) (start : ℕ) : ℕ → Matrix ι ι R
  | 0 => 1
  | len + 1 => A start * intervalProduct A (start + 1) len

theorem intervalProduct_split (A : ℕ → Matrix ι ι R) (start u v : ℕ) :
    intervalProduct A start (u + v) =
      intervalProduct A start u * intervalProduct A (start + u) v := by
  induction u generalizing start with
  | zero => simp [intervalProduct]
  | succ u ih =>
    rw [Nat.succ_add, intervalProduct, intervalProduct, ih]
    simp [Nat.add_comm, Nat.add_left_comm, mul_assoc]

/-- An entry of an interval product, using a balanced product tree. -/
def productEntry (A : ℕ → Matrix ι ι R) (start len : ℕ) (i j : ι) : R :=
  if len = 0 then (1 : Matrix ι ι R) i j
  else if len = 1 then A start i j
  else ∑ r, productEntry A start (len / 2) i r *
    productEntry A (start + len / 2) (len - len / 2) r j
termination_by len
decreasing_by all_goals omega

/-- The entry recursion preserves the order of noncommuting matrix factors. -/
theorem productEntry_eq (A : ℕ → Matrix ι ι R) (start len : ℕ) (i j : ι) :
    productEntry A start len i j = intervalProduct A start len i j := by
  induction len using Nat.strong_induction_on generalizing start i j with
  | h len ih =>
    rw [productEntry]
    split_ifs with h₀ h₁
    · subst len
      rfl
    · subst len
      simp [intervalProduct]
    · have hu : len / 2 < len := by omega
      have hv : len - len / 2 < len := by omega
      simp_rw [ih _ hu, ih _ hv]
      rw [← Matrix.mul_apply, ← intervalProduct_split,
        Nat.add_sub_of_le (Nat.div_le_self _ _)]

end SparseIrred.UpperBounds
