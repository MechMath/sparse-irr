import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic

/-!
# Testing corank one by deleted-row/deleted-column minors

The final algebraic step in Section 4 needs only the `n²` minors obtained by deleting
one row and one column. The statement here includes `1 × 1` matrices and empty minors.
-/

open Matrix

namespace SparseIrred.UpperBounds

/-- A matrix of corank one has a nonzero adjugate. -/
theorem adjugate_ne_zero_of_rank {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (hr : A.rank = n) : A.adjugate ≠ 0 := by
  classical
  intro ha
  obtain ⟨V, U, e, _, _, heq⟩ := Matrix.exists_rank_normal_form A
  have hcard : Fintype.card (Fin (n + 1)) = n + 1 := Fintype.card_fin _
  let d : Fin A.rank ⊕ Fin (Fintype.card (Fin (n + 1)) - A.rank) → K :=
    Sum.elim (fun _ ↦ 1) (fun _ ↦ 0)
  have hd : (fromBlocks 1 0 0 0 :
      Matrix (Fin A.rank ⊕ Fin (Fintype.card (Fin (n + 1)) - A.rank)) _ K) = diagonal d := by
    ext i j
    cases i <;> cases j <;> simp [d, Matrix.fromBlocks, Matrix.diagonal, Matrix.one_apply]
  have hz : 0 < Fintype.card (Fin (n + 1)) - A.rank := by omega
  let z : Fin A.rank ⊕ Fin (Fintype.card (Fin (n + 1)) - A.rank) := Sum.inr ⟨0, hz⟩
  have hadj : (diagonal d).adjugate z z = 1 := by
    rw [adjugate_diagonal, diagonal_apply_eq]
    apply Finset.prod_eq_one
    intro j hj
    rcases j with j | j
    · rfl
    · have hjn : Sum.inr j ≠ z := (Finset.mem_erase.mp hj).1
      have hj0 : j = ⟨0, hz⟩ := Fin.ext (by have := j.isLt; omega)
      exact (hjn (congrArg Sum.inr hj0)).elim
  have hzero : ((diagonal d).submatrix e e).adjugate = 0 := by
    rw [← hd, ← heq, adjugate_mul_distrib, adjugate_mul_distrib, ha, zero_mul, mul_zero]
  rw [adjugate_submatrix_equiv_self] at hzero
  have hz0 := congrArg (fun M ↦ M (e.symm z) (e.symm z)) hzero
  simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply, Matrix.zero_apply] at hz0
  rw [hadj] at hz0
  exact one_ne_zero hz0

/-- The rank test used in Theorem 18, with the existing rank upper bound made explicit. -/
theorem rank_eq_iff_exists_deleted_minor {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (hr : A.rank ≤ n) :
    A.rank = n ↔ ∃ i j : Fin (n + 1), (A.submatrix i.succAbove j.succAbove).det ≠ 0 := by
  classical
  constructor
  · intro he
    have ha := adjugate_ne_zero_of_rank A he
    have hex : ∃ i j, A.adjugate i j ≠ 0 := by
      by_contra hn
      push Not at hn
      exact ha (Matrix.ext fun i j ↦ hn i j)
    obtain ⟨i, j, hij⟩ := hex
    refine ⟨j, i, ?_⟩
    rw [adjugate_fin_succ_eq_det_submatrix] at hij
    exact fun h ↦ hij (by rw [h, mul_zero])
  · rintro ⟨i, j, hij⟩
    have hrank := Matrix.rank_of_det_ne_zero hij
    have hle := Matrix.rank_submatrix_le A i.succAbove j.succAbove
    rw [hrank, Fintype.card_fin] at hle
    omega

end SparseIrred.UpperBounds
