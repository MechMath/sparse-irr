module

public import SparseIrred.UpperBounds.Section4.BerkowitzEvaluator

/-!
# Direct indexed access to Berkowitz factors

The factor sequence is specified by a list in the algebraic product proof, but
an entry of its `s`th factor can be requested directly from binary indices.
This file eliminates that list from the determinant entry evaluator.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped BigOperators

namespace SparseIrred.UpperBounds.Section4

variable {R : Type*} [CommRing R]

/-- Translate an index in the strict trailing block back to the original matrix. -/
def berkowitzTrailingIndex {n : ℕ} (s : ℕ) (j : Fin (n - s - 1)) : Fin n :=
  ⟨s + 1 + j.val, by omega⟩

/-- Direct access to the `s`th padded factor, using only indexed submatrices. -/
def indexedBerkowitzFactor {n : ℕ} (N : ℕ) (A : Matrix (Fin n) (Fin n) R)
    (s : ℕ) : Matrix (Fin N) (Fin N) R :=
  if hs : s < n then fun i j ↦
    if i.val < n - s + 1 ∧ j.val < n - s ∧ j.val ≤ i.val then
      berkowitzColumnEntry (A ⟨s, hs⟩ ⟨s, hs⟩)
        (fun k ↦ A ⟨s, hs⟩ (berkowitzTrailingIndex s k))
        (fun k ↦ A (berkowitzTrailingIndex s k) ⟨s, hs⟩)
        (A.submatrix (berkowitzTrailingIndex s) (berkowitzTrailingIndex s))
        (i.val - j.val)
    else 0
  else 1

theorem indexedBerkowitzFactor_zero {n N : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    indexedBerkowitzFactor N A 0 = paddedBerkowitzFactor N A := by
  ext i j
  simp only [indexedBerkowitzFactor, Nat.zero_lt_succ, ↓reduceDIte, Nat.sub_zero,
    paddedBerkowitzFactor, berkowitzColumnEntry_eq]
  congr 1
  · congr 1
    · funext k
      congr 1
      apply Fin.ext
      simp [berkowitzTrailingIndex, Nat.add_comm]
    · funext k
      congr 1
      apply Fin.ext
      simp [berkowitzTrailingIndex, Nat.add_comm]
    · ext k l
      simp only [Matrix.submatrix_apply, berkowitzTail]
      congr 1 <;> apply Fin.ext <;> simp [berkowitzTrailingIndex, Nat.add_comm]

theorem indexedBerkowitzFactor_succ {n N : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (s : ℕ) :
    indexedBerkowitzFactor N A (s + 1) =
      indexedBerkowitzFactor N (berkowitzTail A) s := by
  ext i j
  by_cases hs : s < n
  · simp only [indexedBerkowitzFactor, Nat.succ_lt_succ_iff, hs, ↓reduceDIte,
      Nat.succ_sub_succ_eq_sub]
    congr 1
    simp only [berkowitzTrailingIndex, berkowitzTail, Matrix.submatrix]
    congr! 2 <;> simp [Nat.add_sub_add_right, Nat.add_assoc]
    · rename_i x y hxy
      have hv := Fin.val_eq_val_of_heq hxy
      congr 1
      apply Fin.ext
      dsimp
      omega
    · rename_i x y hxy
      have hv := Fin.val_eq_val_of_heq hxy
      congr 1
      apply Fin.ext
      dsimp
      omega
    · apply (Fin.heq_fun₂_iff (by omega) (by omega)).2
      intro k l
      simp only [Matrix.of_apply]
      congr 1 <;> apply Fin.ext <;> dsimp <;> omega
  · simp [indexedBerkowitzFactor, hs]

/-- The indexed oracle agrees exactly with the ordered list used in the algebraic proof. -/
theorem indexedBerkowitzFactor_eq_getD {n : ℕ} (N : ℕ)
    (A : Matrix (Fin n) (Fin n) R) (s : ℕ) :
    indexedBerkowitzFactor N A s = (berkowitzFactors N A)[s]?.getD 1 := by
  induction n generalizing s with
  | zero => simp [indexedBerkowitzFactor, berkowitzFactors]
  | succ n ih =>
    cases s with
    | zero => simp [berkowitzFactors, indexedBerkowitzFactor_zero]
    | succ s =>
      rw [indexedBerkowitzFactor_succ, ih]
      rfl

/-- Determinant evaluator whose input factors are requested directly by index. -/
def indexedBerkowitzDeterminant {n : ℕ} (A : Matrix (Fin n) (Fin n) R) : R :=
  (-1) ^ n * productEntry (indexedBerkowitzFactor (n + 1) A) 0 n (Fin.last n) 0

/-- The direct indexed evaluator computes the determinant in every characteristic. -/
theorem indexedBerkowitzDeterminant_eq_det {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) : indexedBerkowitzDeterminant A = A.det := by
  have h : indexedBerkowitzFactor (n + 1) A =
      fun s ↦ (berkowitzFactors (n + 1) A)[s]?.getD 1 :=
    funext (indexedBerkowitzFactor_eq_getD (n + 1) A)
  simpa only [indexedBerkowitzDeterminant, h, berkowitzDeterminantEntry] using
    berkowitzDeterminantEntry_eq_det A

end SparseIrred.UpperBounds.Section4
