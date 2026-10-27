module

public import SparseIrred.UpperBounds.Section4.Berkowitz

/-!
# The padded product of Berkowitz factors

Equation (47) is iterated over the trailing principal submatrices. Every factor
is padded with zeroes to a common square size; the product applied to the first
basis vector is exactly the descending characteristic coefficient vector.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped BigOperators

namespace SparseIrred.UpperBounds.Section4

variable {R : Type*} [CommRing R]

/-- The rectangular Berkowitz factor, padded by zeros to a common square size. -/
def paddedBerkowitzFactor {n : ℕ} (N : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) : Matrix (Fin N) (Fin N) R :=
  fun i j ↦ if i.val < n + 2 ∧ j.val < n + 1 ∧ j.val ≤ i.val then
    berkowitzColumn (A 0 0) (fun j ↦ A 0 j.succ) (fun i ↦ A i.succ 0)
      (berkowitzTail A) (i.val - j.val) else 0

/-- The first basis vector, also well-defined in dimension zero. -/
def berkowitzFirstVector (N : ℕ) : Fin N → R := fun i ↦ if i.val = 0 then 1 else 0

/-- Zero padding preserves the coefficient recurrence at every interface. -/
theorem paddedBerkowitzFactor_mulVec {n N : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (hN : n + 2 ≤ N) :
    paddedBerkowitzFactor N A *ᵥ (fun j ↦ (berkowitzTail A).charpolyRev.coeff j.val) =
      (fun i ↦ A.charpolyRev.coeff i.val) := by
  funext i
  by_cases hi : i.val < n + 2
  · let f : ℕ → R := fun j ↦ if j < n + 1 ∧ j ≤ i.val then
        berkowitzColumn (A 0 0) (fun j ↦ A 0 j.succ) (fun i ↦ A i.succ 0)
          (berkowitzTail A) (i.val - j) * (berkowitzTail A).charpolyRev.coeff j else 0
    simp only [Matrix.mulVec, dotProduct, paddedBerkowitzFactor, hi, true_and,
      ite_mul, zero_mul]
    change (∑ j : Fin N, f j.val) = _
    rw [Fin.sum_univ_eq_sum_range]
    have hext : (∑ j ∈ Finset.range (n + 1), f j) = ∑ j ∈ Finset.range N, f j := by
      apply Finset.sum_subset
      · exact Finset.range_mono (by omega)
      · intro j _ hj
        have hj' : ¬j < n + 1 := by simpa using hj
        simp only [f, hj', false_and, ↓reduceIte]
    rw [← hext, ← Fin.sum_univ_eq_sum_range]
    have h := congrFun (berkowitz_head_tail_mulVec A) (⟨i.val, hi⟩ : Fin (n + 2))
    simpa only [Matrix.mulVec, dotProduct, berkowitzToeplitz, f, Fin.isLt, true_and,
      ite_mul, zero_mul] using h
  · have hz : A.charpolyRev.coeff i.val = 0 :=
      charpolyRev_coeff_eq_zero_of_card_lt A (by simpa using (show n + 1 < i.val by omega))
    simp [Matrix.mulVec, dotProduct, paddedBerkowitzFactor, hi, hz]

/-- The factors are in the order `Q₀, Q₁, ..., Qₙ₋₁` of the paper. -/
def berkowitzFactors (N : ℕ) : {n : ℕ} → Matrix (Fin n) (Fin n) R →
    List (Matrix (Fin N) (Fin N) R)
  | 0, _ => []
  | _n + 1, A => paddedBerkowitzFactor N A :: berkowitzFactors N (berkowitzTail A)

@[simp] theorem berkowitzFactors_length (N : ℕ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) : (berkowitzFactors N A).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [berkowitzFactors, ih]

/-- The padded product reconstructs every characteristic coefficient. -/
theorem berkowitzFactors_prod_mulVec (N : ℕ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (hN : n + 1 ≤ N) :
    (berkowitzFactors N A).prod *ᵥ berkowitzFirstVector N =
      (fun i ↦ A.charpolyRev.coeff i.val) := by
  induction n with
  | zero =>
    simp only [berkowitzFactors, List.prod_nil, Matrix.one_mulVec, Matrix.charpolyRev,
      Matrix.det_isEmpty]
    funext i
    simp [berkowitzFirstVector, Polynomial.coeff_one]
  | succ n ih =>
    rw [berkowitzFactors, List.prod_cons, ← Matrix.mulVec_mulVec,
      ih (berkowitzTail A) (by omega), paddedBerkowitzFactor_mulVec A hN]

/-- The final product entry gives the determinant, including the empty matrix case. -/
theorem berkowitzFactors_det {n : ℕ} (A : Matrix (Fin n) (Fin n) R) :
    A.det = (-1) ^ n * (berkowitzFactors (n + 1) A).prod (Fin.last n) 0 := by
  have h := congrFun (berkowitzFactors_prod_mulVec (n + 1) A le_rfl) (Fin.last n)
  have he : (berkowitzFactors (n + 1) A).prod (Fin.last n) 0 =
      A.charpoly.coeff 0 := by
    have h' : (berkowitzFactors (n + 1) A).prod (Fin.last n) 0 =
        A.charpolyRev.coeff n := by
      simpa [Matrix.mulVec, dotProduct, berkowitzFirstVector] using h
    rw [charpolyRev_coeff_eq_descending A (by simp)] at h'
    simpa using h'
  rw [he]
  simpa using Matrix.det_eq_sign_charpoly_coeff A

end SparseIrred.UpperBounds.Section4
