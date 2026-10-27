import SparseIrred.UpperBounds.FiniteFieldTest

/-!
# Coefficient oracles for the quotient's companion matrix

The explicit leading-coefficient normalization in Theorem 18 preserves degree and
irreducibility. The entry oracle below is proved equal to multiplication by the
actual quotient root, and therefore supplies the exact Frobenius entries (48).
-/

open Polynomial Matrix

namespace SparseIrred.UpperBounds

/-- Multiplying by the inverse leading coefficient, without constructing a dense list. -/
noncomputable def monicRepresentative {K : Type*} [Field K] (f : K[X]) : K[X] :=
  f * C f.leadingCoeff⁻¹

theorem monicRepresentative_monic {K : Type*} [Field K] (f : K[X]) (hf : f ≠ 0) :
    (monicRepresentative f).Monic :=
  Polynomial.monic_mul_leadingCoeff_inv hf

theorem monicRepresentative_natDegree {K : Type*} [Field K] (f : K[X]) (hf : f ≠ 0) :
    (monicRepresentative f).natDegree = f.natDegree :=
  Polynomial.natDegree_mul_leadingCoeff_inv f hf

theorem monicRepresentative_coeff {K : Type*} [Field K] (f : K[X]) (i : ℕ) :
    (monicRepresentative f).coeff i = f.coeff i * f.leadingCoeff⁻¹ := by
  simp [monicRepresentative]

/-- The normalization also handles the zero polynomial correctly. -/
theorem monicRepresentative_irreducible_iff {K : Type*} [Field K] (f : K[X]) :
    Irreducible (monicRepresentative f) ↔ Irreducible f :=
  Polynomial.irreducible_mul_leadingCoeff_inv

/-- The concrete companion-matrix oracle, using only a coefficient and the leading
coefficient. It works on nonmonic input by incorporating the normalization. -/
def coefficientCompanion {K : Type*} [Field K] (f : K[X]) :
    Matrix (Fin f.natDegree) (Fin f.natDegree) K := fun i j ↦
  if j.val + 1 = f.natDegree then -(f.coeff i.val * f.leadingCoeff⁻¹)
  else if i.val = j.val + 1 then 1 else 0

/-- The coefficient oracle is the matrix of multiplication by the quotient root. -/
theorem coefficientCompanion_eq_leftMulMatrix {K : Type*} [Field K]
    (f : K[X]) (hf : f ≠ 0) :
    coefficientCompanion f =
      Algebra.leftMulMatrix (AdjoinRoot.powerBasis hf).basis (AdjoinRoot.root f) := by
  ext i j
  have h := generator_matrix_entry (AdjoinRoot.powerBasis hf) i j
  rw [PowerBasis.minpolyGen_eq, AdjoinRoot.minpoly_powerBasis_gen hf] at h
  simpa only [coefficientCompanion, AdjoinRoot.powerBasis_dim, AdjoinRoot.powerBasis_gen,
    coeff_mul_C] using h.symm

/-- For monic input this is precisely the entry formula printed in Theorem 18. -/
theorem coefficientCompanion_of_monic {K : Type*} [Field K]
    (f : K[X]) (hf : f.Monic) (i j : Fin f.natDegree) :
    coefficientCompanion f i j =
      if j.val + 1 = f.natDegree then -f.coeff i.val
      else if i.val = j.val + 1 then 1 else 0 := by
  simp [coefficientCompanion, hf.leadingCoeff]

/-- The entry-by-entry Frobenius oracle of equation (48). -/
noncomputable def coefficientFrobenius {K : Type*} [Field K] [Fintype K]
    (f : K[X]) (hf : 0 < f.natDegree) : Matrix (Fin f.natDegree) (Fin f.natDegree) K :=
  fun i j ↦ powerEntry (coefficientCompanion f) (Fintype.card K * j.val) i ⟨0, hf⟩

theorem coefficientFrobenius_eq_frobeniusMatrix {K : Type*} [Field K] [Fintype K]
    (f : K[X]) (hf : 0 < f.natDegree) :
    coefficientFrobenius f hf =
      frobeniusMatrix (AdjoinRoot.powerBasis (Polynomial.ne_zero_of_natDegree_gt hf)) := by
  ext i j
  have h := frobeniusMatrix_entry
    (AdjoinRoot.powerBasis (Polynomial.ne_zero_of_natDegree_gt hf)) hf i j
  rw [AdjoinRoot.powerBasis_gen, ← coefficientCompanion_eq_leftMulMatrix] at h
  exact h.symm

/-- Explicit entries for `B-I`; no vector of quotient remainders is involved. -/
theorem coefficientFrobenius_sub_one_entry {K : Type*} [Field K] [Fintype K]
    (f : K[X]) (hf : 0 < f.natDegree) (i j : Fin f.natDegree) :
    (coefficientFrobenius f hf - 1) i j =
      powerEntry (coefficientCompanion f) (Fintype.card K * j.val) i ⟨0, hf⟩ -
        if i = j then 1 else 0 := by
  simp [coefficientFrobenius, Matrix.one_apply]

/-- The rank criterion can be evaluated using the coefficient and power oracles. -/
theorem irreducible_iff_coefficientFrobenius_rank {K : Type*} [Field K] [Fintype K]
    (f : K[X]) (hf : 0 < f.natDegree) (hsq : Squarefree f) :
    Irreducible f ↔ (coefficientFrobenius f hf - 1).rank = f.natDegree - 1 := by
  rw [coefficientFrobenius_eq_frobeniusMatrix]
  exact irreducible_iff_frobeniusMatrix_rank f hf hsq

/-- A natural-number entry oracle for the Sylvester matrix. The derivative
coefficient is obtained by one coefficient lookup and multiplication by its index. -/
noncomputable def coefficientSylvesterEntry {K : Type*} [Field K]
    (f : K[X]) (i j : ℕ) : K :=
  if j < f.natDegree then
    if j ≤ i ∧ i ≤ j + f.derivative.natDegree then
      f.coeff (i - j + 1) * ((i - j + 1 : ℕ) : K) else 0
  else
    if j - f.natDegree ≤ i ∧ i ≤ j - f.natDegree + f.natDegree then
      f.coeff (i - (j - f.natDegree)) else 0

theorem coefficientSylvesterEntry_eq {K : Type*} [Field K] (f : K[X])
    (i j : Fin (f.natDegree + f.derivative.natDegree)) :
    coefficientSylvesterEntry f i.val j.val =
      f.sylvester f.derivative f.natDegree f.derivative.natDegree i j := by
  induction j using Fin.addCases with
  | left j =>
      simp [coefficientSylvesterEntry, Polynomial.sylvester, j.isLt, Set.mem_Icc,
        Polynomial.coeff_derivative]
  | right j =>
      simp [coefficientSylvesterEntry, Polynomial.sylvester, Set.mem_Icc]

/-- Reindexing the oracle to a positive dimension makes deletion of rows and columns
available through `Fin.succAbove`, including the degree-one empty minor. -/
noncomputable def positiveCoefficientFrobenius {K : Type*} [Field K] [Fintype K]
    (f : K[X]) (hf : 0 < f.natDegree) :
    Matrix (Fin (f.natDegree - 1 + 1)) (Fin (f.natDegree - 1 + 1)) K :=
  (coefficientFrobenius f hf).submatrix
    (finCongr (by omega)) (finCongr (by omega))

theorem positiveCoefficientFrobenius_eq_toMatrix {K : Type*} [Field K] [Fintype K]
    (f : K[X]) (hf : 0 < f.natDegree) :
    positiveCoefficientFrobenius f hf =
      LinearMap.toMatrix (quotientPowerBasis f hf) (quotientPowerBasis f hf)
        (FiniteField.frobeniusAlgHom K (AdjoinRoot f)).toLinearMap := by
  rw [positiveCoefficientFrobenius, coefficientFrobenius_eq_frobeniusMatrix]
  ext i j
  change frobeniusMatrix (AdjoinRoot.powerBasis (Polynomial.ne_zero_of_natDegree_gt hf))
      (Fin.cast (by change f.natDegree - 1 + 1 = f.natDegree; omega) i)
      (Fin.cast (by change f.natDegree - 1 + 1 = f.natDegree; omega) j) = _
  simp [frobeniusMatrix, LinearMap.toMatrix_apply, quotientPowerBasis,
    Module.Basis.coe_reindex, Module.Basis.repr_reindex]

/-- The complete two-test criterion expressed entirely through the coefficient
oracles and entry determinants. No factorization or dense quotient vector is input. -/
theorem irreducible_iff_coefficient_oracle_tests {K : Type*} [Field K] [Fintype K]
    (f : K[X]) (hf : 0 < f.natDegree) :
    Irreducible f ↔
      determinantEntry (fun i j : Fin (f.natDegree + f.derivative.natDegree) ↦
        coefficientSylvesterEntry f i.val j.val) ≠ 0 ∧
      ∃ i j : Fin (f.natDegree - 1 + 1),
        determinantEntry ((positiveCoefficientFrobenius f hf - 1).submatrix
          i.succAbove j.succAbove) ≠ 0 := by
  have hSyl : (fun i j : Fin (f.natDegree + f.derivative.natDegree) ↦
      coefficientSylvesterEntry f i.val j.val) =
      f.sylvester f.derivative f.natDegree f.derivative.natDegree := by
    ext i j
    exact coefficientSylvesterEntry_eq f i j
  simp only [hSyl, determinantEntry_eq_det, positiveCoefficientFrobenius_eq_toMatrix]
  exact irreducible_iff_resultant_and_minor f hf (quotientPowerBasis f hf)

end SparseIrred.UpperBounds
