module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Tactic

/-!
# The division-free Berkowitz identity

The proof of equation (47) uses formal power series at zero, with the characteristic
polynomial reversed. This avoids division of coefficients and works over every
commutative ring, including finite fields of arbitrary characteristic.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped BigOperators

namespace SparseIrred.UpperBounds.Section4

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The formal resolvent, whose coefficient of degree `k` is `M ^ k`. -/
def berkowitzResolvent (M : Matrix ι ι R) : Matrix ι ι (PowerSeries R) :=
  fun i j ↦ PowerSeries.mk (fun k ↦ (M ^ k) i j)

/-- The reversed characteristic matrix over formal power series. -/
def berkowitzPencil (M : Matrix ι ι R) : Matrix ι ι (PowerSeries R) :=
  1 - (PowerSeries.X : PowerSeries R) • M.map PowerSeries.C

@[simp] theorem coeff_berkowitzResolvent (M : Matrix ι ι R) (k : ℕ) (i j : ι) :
    PowerSeries.coeff k (berkowitzResolvent M i j) = (M ^ k) i j :=
  PowerSeries.coeff_mk _ _

theorem berkowitzPencil_mul_resolvent (M : Matrix ι ι R) :
    berkowitzPencil M * berkowitzResolvent M = 1 := by
  rw [berkowitzPencil, sub_mul, Matrix.one_mul, Matrix.smul_mul]
  ext i j k
  cases k with
  | zero =>
    simp only [Matrix.sub_apply, map_sub, Matrix.smul_apply, smul_eq_mul,
      PowerSeries.coeff_zero_X_mul, coeff_berkowitzResolvent, pow_zero, sub_zero]
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  | succ k =>
    simp only [Matrix.sub_apply, map_sub, Matrix.smul_apply, smul_eq_mul,
      PowerSeries.coeff_succ_X_mul, coeff_berkowitzResolvent, Matrix.mul_apply, map_sum,
      Matrix.map_apply, PowerSeries.coeff_C_mul]
    rw [← Matrix.mul_apply, ← pow_succ']
    simp [Matrix.one_apply, apply_ite, PowerSeries.coeff_one]

theorem berkowitzResolvent_mul_pencil (M : Matrix ι ι R) :
    berkowitzResolvent M * berkowitzPencil M = 1 := by
  rw [berkowitzPencil, mul_sub, Matrix.mul_one, Matrix.mul_smul]
  ext i j k
  cases k with
  | zero =>
    simp only [Matrix.sub_apply, map_sub, Matrix.smul_apply, smul_eq_mul,
      PowerSeries.coeff_zero_X_mul, coeff_berkowitzResolvent, pow_zero, sub_zero]
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  | succ k =>
    simp only [Matrix.sub_apply, map_sub, Matrix.smul_apply, smul_eq_mul,
      PowerSeries.coeff_succ_X_mul, coeff_berkowitzResolvent, Matrix.mul_apply, map_sum,
      Matrix.map_apply, PowerSeries.coeff_mul_C]
    rw [← Matrix.mul_apply, ← pow_succ]
    simp [Matrix.one_apply, apply_ite, PowerSeries.coeff_one]

/-- A matrix with its leading row and column separated from the trailing block. -/
def berkowitzBlock (a : R) (row col : ι → R) (M : Matrix ι ι R) :
    Matrix (Unit ⊕ ι) (Unit ⊕ ι) R :=
  Matrix.fromBlocks (fun _ _ ↦ a) (fun _ j ↦ row j) (fun i _ ↦ col i) M

/-- The generating series for `1, -a, -R S, -R M S, ...`. -/
def berkowitzSeries (a : R) (row col : ι → R) (M : Matrix ι ι R) : PowerSeries R :=
  1 - PowerSeries.X * PowerSeries.C a - PowerSeries.X * PowerSeries.X *
    ∑ i, ∑ j, PowerSeries.C (row i) * berkowitzResolvent M i j * PowerSeries.C (col j)

theorem det_berkowitzPencil (M : Matrix ι ι R) :
    (berkowitzPencil M).det = (M.charpolyRev : PowerSeries R) := by
  rw [Matrix.charpolyRev]
  change (berkowitzPencil M).det =
    Polynomial.coeToPowerSeries.ringHom ((1 - Polynomial.X • M.map Polynomial.C).det)
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [berkowitzPencil, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, apply_ite]
  ring

/-- Schur's block determinant identity with its inverse expanded explicitly. -/
theorem berkowitz_charpolyRev_series (a : R) (row col : ι → R) (M : Matrix ι ι R) :
    ((berkowitzBlock a row col M).charpolyRev : PowerSeries R) =
      (M.charpolyRev : PowerSeries R) * berkowitzSeries a row col M := by
  let : Invertible (berkowitzPencil M) :=
    ⟨berkowitzResolvent M, berkowitzResolvent_mul_pencil M,
      berkowitzPencil_mul_resolvent M⟩
  have hblock : berkowitzPencil (berkowitzBlock a row col M) =
      Matrix.fromBlocks
        (fun _ _ : Unit ↦ 1 - PowerSeries.X * PowerSeries.C a)
        (fun _ j ↦ -(PowerSeries.X * PowerSeries.C (row j)))
        (fun i _ ↦ -(PowerSeries.X * PowerSeries.C (col i)))
        (berkowitzPencil M) := by
    ext i j
    cases i <;> cases j <;>
      simp [berkowitzPencil, berkowitzBlock, Matrix.sub_apply, Matrix.smul_apply,
        smul_eq_mul, Matrix.one_apply, Matrix.fromBlocks]
  rw [← det_berkowitzPencil, hblock, Matrix.det_fromBlocks₂₂, det_berkowitzPencil,
    Matrix.det_eq_elem_of_subsingleton _ ()]
  congr 1
  simp only [Matrix.sub_apply, Matrix.mul_apply, berkowitzSeries]
  change 1 - PowerSeries.X * PowerSeries.C a -
    (∑ i, (∑ j, -(PowerSeries.X * PowerSeries.C (row j)) *
      berkowitzResolvent M j i) * -(PowerSeries.X * PowerSeries.C (col i))) = _
  congr 1
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The Toeplitz column in equation (47), defined by division-free matrix powers. -/
def berkowitzColumn (a : R) (row col : ι → R) (M : Matrix ι ι R) : ℕ → R
  | 0 => 1
  | 1 => -a
  | k + 2 => - ∑ i, ∑ j, row i * (M ^ k) i j * col j

theorem coeff_berkowitzSeries (a : R) (row col : ι → R) (M : Matrix ι ι R) (k : ℕ) :
    PowerSeries.coeff k (berkowitzSeries a row col M) = berkowitzColumn a row col M k := by
  cases k with
  | zero => simp [berkowitzSeries, berkowitzColumn]
  | succ k =>
    cases k with
    | zero =>
      simp [berkowitzSeries, berkowitzColumn, mul_assoc,
        PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one]
    | succ k =>
      simp [berkowitzSeries, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one,
        PowerSeries.coeff_X, mul_assoc, berkowitzColumn]

/-- The full coefficient convolution underlying equation (47). -/
theorem berkowitz_coeff_recurrence (a : R) (row col : ι → R) (M : Matrix ι ι R) (k : ℕ) :
    (berkowitzBlock a row col M).charpolyRev.coeff k =
      ∑ j ∈ Finset.range (k + 1),
        M.charpolyRev.coeff j * berkowitzColumn a row col M (k - j) := by
  have h := congrArg (PowerSeries.coeff k) (berkowitz_charpolyRev_series a row col M)
  simpa only [Polynomial.coeff_coe, PowerSeries.coeff_mul, coeff_berkowitzSeries,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] using h

theorem charpolyRev_coeff_eq_zero_of_card_lt (M : Matrix ι ι R) {k : ℕ}
    (hk : Fintype.card ι < k) : M.charpolyRev.coeff k = 0 := by
  nontriviality R
  rw [← Matrix.reverse_charpoly]
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt
    (M.charpoly.reverse_natDegree_le.trans (le_of_eq M.charpoly_natDegree_eq_dim)) hk

/-- `charpolyRev` stores the original characteristic coefficients in descending order. -/
theorem charpolyRev_coeff_eq_descending (M : Matrix ι ι R) {k : ℕ}
    (hk : k ≤ Fintype.card ι) :
    M.charpolyRev.coeff k = M.charpoly.coeff (Fintype.card ι - k) := by
  nontriviality R
  rw [← Matrix.reverse_charpoly, Polynomial.coeff_reverse, M.charpoly_natDegree_eq_dim,
    Polynomial.revAt_le hk]

/-- The rectangular lower triangular Toeplitz matrix in equation (47). -/
def berkowitzToeplitz {n : ℕ} (a : R) (row col : Fin n → R)
    (M : Matrix (Fin n) (Fin n) R) : Matrix (Fin (n + 2)) (Fin (n + 1)) R :=
  fun i j ↦ if j.val ≤ i.val then berkowitzColumn a row col M (i.val - j.val) else 0

/-- Equation (47), with exactly the rectangular matrix sizes from the paper. -/
theorem berkowitz_toeplitz_mulVec {n : ℕ} (a : R) (row col : Fin n → R)
    (M : Matrix (Fin n) (Fin n) R) :
    berkowitzToeplitz a row col M *ᵥ (fun j ↦ M.charpolyRev.coeff j.val) =
      (fun i ↦ (berkowitzBlock a row col M).charpolyRev.coeff i.val) := by
  funext i
  rw [berkowitz_coeff_recurrence]
  simp only [Matrix.mulVec, dotProduct, berkowitzToeplitz, ite_mul, zero_mul]
  let f : ℕ → R := fun j ↦ if j ≤ i.val then
    berkowitzColumn a row col M (i.val - j) * M.charpolyRev.coeff j else 0
  change (∑ j : Fin (n + 1), f j.val) = _
  rw [Fin.sum_univ_eq_sum_range]
  change (∑ j ∈ Finset.range (n + 1), f j) = _
  have htop : f (n + 1) = 0 := by
    have hz : M.charpolyRev.coeff (n + 1) = 0 :=
      charpolyRev_coeff_eq_zero_of_card_lt M (by simp)
    simp [f, hz]
  rw [← add_zero (∑ j ∈ Finset.range (n + 1), f j), ← htop,
    ← Finset.sum_range_succ]
  have hext : (∑ j ∈ Finset.range (i.val + 1), f j) =
      ∑ j ∈ Finset.range (n + 1 + 1), f j := by
    apply Finset.sum_subset
    · exact Finset.range_mono (by omega)
    · intro j _ hj
      have hj' : i.val < j := by simpa using hj
      simp [f, Nat.not_le_of_lt hj']
  rw [← hext]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ i.val := by simpa using hj
  simp [f, hj', mul_comm]

/-- Split off index zero, preserving the order of the remaining indices. -/
def berkowitzHeadTailEquiv (n : ℕ) : Unit ⊕ Fin n ≃ Fin (n + 1) where
  toFun := Sum.elim (fun _ ↦ 0) Fin.succ
  invFun := Fin.cases (Sum.inl ()) Sum.inr
  left_inv x := by cases x <;> simp
  right_inv i := by induction i using Fin.cases <;> simp

/-- The trailing principal submatrix after deleting the first row and column. -/
def berkowitzTail {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    Matrix (Fin n) (Fin n) R := A.submatrix Fin.succ Fin.succ

omit [CommRing R] in
theorem berkowitzBlock_head_tail {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    berkowitzBlock (A 0 0) (fun j ↦ A 0 j.succ) (fun i ↦ A i.succ 0)
        (berkowitzTail A) =
      A.submatrix (berkowitzHeadTailEquiv n) (berkowitzHeadTailEquiv n) := by
  ext i j
  cases i <;> cases j <;> rfl

theorem berkowitzBlock_head_tail_charpolyRev {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    (berkowitzBlock (A 0 0) (fun j ↦ A 0 j.succ) (fun i ↦ A i.succ 0)
      (berkowitzTail A)).charpolyRev = A.charpolyRev := by
  rw [berkowitzBlock_head_tail, ← Matrix.reverse_charpoly, ← Matrix.reverse_charpoly]
  congr 1
  exact Matrix.charpoly_reindex (berkowitzHeadTailEquiv n).symm A

/-- Equation (47) for the actual leading block of a finite-indexed matrix. -/
theorem berkowitz_head_tail_mulVec {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    berkowitzToeplitz (A 0 0) (fun j ↦ A 0 j.succ) (fun i ↦ A i.succ 0)
        (berkowitzTail A) *ᵥ (fun j ↦ (berkowitzTail A).charpolyRev.coeff j.val) =
      (fun i ↦ A.charpolyRev.coeff i.val) := by
  rw [berkowitz_toeplitz_mulVec, berkowitzBlock_head_tail_charpolyRev]

end SparseIrred.UpperBounds.Section4
