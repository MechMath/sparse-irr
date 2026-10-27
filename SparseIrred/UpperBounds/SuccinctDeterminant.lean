module

public import SparseIrred.UpperBounds.SuccinctMatrix
import all Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Correctness
import all Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Defs

/-!
# A division-free determinant entry oracle

Bird's recurrence is linear in its current matrix. Its transition matrix has dimension
`n²`, but each entry uses only comparisons and two entries of the original matrix.
Balanced powering therefore gives a determinant evaluator with logarithmic recursion
depth in `n`, in arbitrary characteristic. This is an alternative to the Berkowitz
identity used in Section 4, Lemma 17. A machine-level space bound remains separate.
-/

@[expose] public section

open Matrix
open scoped BigOperators

namespace SparseIrred.UpperBounds

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The linear transition of Bird's recurrence, with matrix entries used as coordinates. -/
def birdTransition (A : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) R := fun ij uv ↦
  (if ij.1 < uv.1 then if uv.2 = uv.1 then -A ij.1 ij.2 else 0 else 0) +
    (if uv.1 = ij.1 then if ij.1 < uv.2 then A uv.2 ij.2 else 0 else 0)

theorem birdTransition_mulVec (A F : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (birdTransition A *ᵥ fun uv ↦ F uv.1 uv.2) (i, j) = BirdDet.Spec.stepEntry A F i j := by
  simp only [Matrix.mulVec, dotProduct, birdTransition, Fintype.sum_prod_type, add_mul,
    Finset.sum_add_distrib, ite_mul, zero_mul]
  simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.mem_univ, ite_eq_left,
    Finset.sum_const_zero]
  simp only [BirdDet.Spec.stepEntry, Matrix.of_apply]
  simp only [← Finset.sum_filter, Finset.filter_lt_eq_Ioi]
  rw [← Finset.sum_neg_distrib, Finset.sum_mul]
  congr 1
  · apply Finset.sum_congr rfl
    intro k _
    ring
  · apply Finset.sum_congr rfl
    intro k _
    ring

/-- Iterating Bird's step is the same as powering its transition matrix. -/
theorem birdTransition_pow_mulVec (A : Matrix (Fin n) (Fin n) R) (t : ℕ) (i j : Fin n) :
    (birdTransition A ^ t *ᵥ fun uv ↦ A uv.1 uv.2) (i, j) =
      ((BirdDet.Spec.stepEntry A)^[t] A) i j := by
  induction t generalizing i j with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, Function.iterate_succ_apply']
    have heq : (birdTransition A ^ t *ᵥ fun uv ↦ A uv.1 uv.2) =
        fun uv ↦ ((BirdDet.Spec.stepEntry A)^[t] A) uv.1 uv.2 := by
      funext ⟨k, l⟩
      exact ih k l
    rw [heq, birdTransition_mulVec]

/-- The determinant evaluator requests only individual transition-power entries. -/
def determinantEntry : {n : ℕ} → Matrix (Fin n) (Fin n) R → R
  | 0, _ => 1
  | k + 1, A => (-1) ^ k * ∑ uv : Fin (k + 1) × Fin (k + 1),
      powerEntry (birdTransition A) k (0, 0) uv * A uv.1 uv.2

/-- Correctness of the determinant oracle, in every commutative ring. -/
theorem determinantEntry_eq_det (A : Matrix (Fin n) (Fin n) R) :
    determinantEntry A = A.det := by
  cases n with
  | zero => simp [determinantEntry]
  | succ k =>
    rw [BirdDet.birdDetSpec_eq_det, BirdDet.Spec.birdDetSpec_succ]
    unfold determinantEntry
    simp_rw [powerEntry_eq]
    congr 1
    exact birdTransition_pow_mulVec A k 0 0

end SparseIrred.UpperBounds
