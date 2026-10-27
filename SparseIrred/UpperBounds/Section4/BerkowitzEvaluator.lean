module

public import SparseIrred.UpperBounds.Section4.BerkowitzProduct
public import SparseIrred.UpperBounds.SuccinctMatrix

/-!
# Entry evaluation for the Berkowitz construction

These are arithmetic entry evaluators and their exact algebraic correctness.
Machine compilation and bit-space accounting are separate from these identities.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped BigOperators

namespace SparseIrred.UpperBounds.Section4

variable {R : Type*} [CommRing R]

/-- A column entry requests individual entries of a matrix power, never a power matrix. -/
def berkowitzColumnEntry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : R) (row col : ι → R) (M : Matrix ι ι R) : ℕ → R
  | 0 => 1
  | 1 => -a
  | k + 2 => - ∑ i, ∑ j, row i * powerEntry M k i j * col j

theorem berkowitzColumnEntry_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : R) (row col : ι → R) (M : Matrix ι ι R) (k : ℕ) :
    berkowitzColumnEntry a row col M k = berkowitzColumn a row col M k := by
  cases k with
  | zero => rfl
  | succ k =>
    cases k with
    | zero => rfl
    | succ k => simp [berkowitzColumnEntry, berkowitzColumn, powerEntry_eq]

/-- Each padded-factor entry uses comparisons, one double sum, and a power-entry oracle. -/
def paddedBerkowitzFactorEntry {n : ℕ} (N : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i j : Fin N) : R :=
  if i.val < n + 2 ∧ j.val < n + 1 ∧ j.val ≤ i.val then
    berkowitzColumnEntry (A 0 0) (fun j ↦ A 0 j.succ) (fun i ↦ A i.succ 0)
      (berkowitzTail A) (i.val - j.val) else 0

theorem paddedBerkowitzFactorEntry_eq {n N : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i j : Fin N) :
    paddedBerkowitzFactorEntry N A i j = paddedBerkowitzFactor N A i j := by
  simp [paddedBerkowitzFactorEntry, paddedBerkowitzFactor, berkowitzColumnEntry_eq]

theorem intervalProduct_eq_ofFn {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ℕ → Matrix ι ι R) (start len : ℕ) :
    intervalProduct A start len = (List.ofFn (fun i : Fin len ↦ A (start + i.val))).prod := by
  induction len generalizing start with
  | zero => simp [intervalProduct]
  | succ len ih =>
    rw [intervalProduct, List.ofFn_succ, List.prod_cons, ih]
    simp [Nat.add_left_comm, Nat.add_comm]

theorem intervalProduct_getD {ι : Type*} [Fintype ι] [DecidableEq ι]
    (As : List (Matrix ι ι R)) :
    intervalProduct (fun j ↦ As[j]?.getD 1) 0 As.length = As.prod := by
  rw [intervalProduct_eq_ofFn]
  congr 1
  simp

/-- The outer balanced product evaluator reads only a single requested factor entry. -/
def berkowitzDeterminantEntry {n : ℕ} (A : Matrix (Fin n) (Fin n) R) : R :=
  (-1) ^ n * productEntry (fun j ↦ (berkowitzFactors (n + 1) A)[j]?.getD 1)
    0 n (Fin.last n) 0

/-- Correctness of the exact Berkowitz determinant evaluation from Lemma 17. -/
theorem berkowitzDeterminantEntry_eq_det {n : ℕ} (A : Matrix (Fin n) (Fin n) R) :
    berkowitzDeterminantEntry A = A.det := by
  have h := intervalProduct_getD (berkowitzFactors (n + 1) A)
  rw [berkowitzFactors_length] at h
  rw [berkowitzDeterminantEntry, productEntry_eq, h]
  exact (berkowitzFactors_det A).symm

end SparseIrred.UpperBounds.Section4
