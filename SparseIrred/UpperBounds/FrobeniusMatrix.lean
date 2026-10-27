import SparseIrred.UpperBounds.FiniteFieldCriterion
import SparseIrred.UpperBounds.SuccinctMatrix
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The Frobenius matrix as a matrix-power entry oracle

Equation (48) and the rank form of the Berlekamp criterion in Section 4. The power
evaluator is the balanced evaluator from `SuccinctMatrix`, not a dense power operation.
-/

open Polynomial Matrix

namespace SparseIrred.UpperBounds

section PowerBasis

variable {K R : Type*} [Field K] [Fintype K] [CommRing R] [Algebra K R]

/-- The matrix of `q`-power Frobenius in a power basis. -/
noncomputable def frobeniusMatrix (pb : PowerBasis K R) : Matrix (Fin pb.dim) (Fin pb.dim) K :=
  LinearMap.toMatrix pb.basis pb.basis (FiniteField.frobeniusAlgHom K R).toLinearMap

omit [Fintype K] in
/-- Column zero of a multiplication-matrix power represents the corresponding power. -/
theorem generator_matrix_power (pb : PowerBasis K R) (hp : 0 < pb.dim)
    (e : ℕ) (i : Fin pb.dim) :
    (Algebra.leftMulMatrix pb.basis pb.gen ^ e) i ⟨0, hp⟩ =
      pb.basis.repr (pb.gen ^ e) i := by
  rw [← map_pow, Algebra.leftMulMatrix_eq_repr_mul, pb.basis_eq_pow]
  simp

/-- Equation (48): a Frobenius matrix entry is one entry of `C^(q*j)`. -/
theorem frobeniusMatrix_entry (pb : PowerBasis K R) (hp : 0 < pb.dim)
    (i j : Fin pb.dim) :
    frobeniusMatrix pb i j =
      powerEntry (Algebra.leftMulMatrix pb.basis pb.gen) (Fintype.card K * j.val) i ⟨0, hp⟩ := by
  rw [powerEntry_eq, generator_matrix_power]
  unfold frobeniusMatrix
  rw [LinearMap.toMatrix_apply, pb.basis_eq_pow]
  change pb.basis.repr ((pb.gen ^ j.val) ^ Fintype.card K) i = _
  rw [← pow_mul, Nat.mul_comm j.val]

omit [Fintype K] in
/-- The multiplication matrix has the companion-matrix coefficient oracle in the paper. -/
theorem generator_matrix_entry (pb : PowerBasis K R) (i j : Fin pb.dim) :
    Algebra.leftMulMatrix pb.basis pb.gen i j =
      if j.val + 1 = pb.dim then -pb.minpolyGen.coeff i.val
      else if i.val = j.val + 1 then 1 else 0 := by
  rw [pb.leftMulMatrix]
  rfl

end PowerBasis

/-- Rank-nullity for the Frobenius difference, expressed in an arbitrary finite basis. -/
theorem frobenius_rank_add_fixedSpace {K R ι : Type*} [Field K] [Fintype K]
    [CommRing R] [Algebra K R] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K R) :
    (LinearMap.toMatrix b b (FiniteField.frobeniusAlgHom K R).toLinearMap - 1).rank +
      Module.finrank K (frobeniusFixedSpace K R) = Fintype.card ι := by
  have : FiniteDimensional K R := Module.Finite.of_basis b
  have hr := (LinearMap.toMatrix b b (frobeniusDifference K R)).rank_eq_finrank_range_toLin b b
  rw [Matrix.toLin_toMatrix] at hr
  have hm : LinearMap.toMatrix b b (frobeniusDifference K R) =
      LinearMap.toMatrix b b (FiniteField.frobeniusAlgHom K R).toLinearMap - 1 := by
    simp [frobeniusDifference]
  rw [← hm, hr, frobeniusFixedSpace, LinearMap.finrank_range_add_finrank_ker,
    Module.finrank_eq_card_basis b]

/-- The second equivalence in (49), using the quotient's genuine power basis. -/
theorem irreducible_iff_frobeniusMatrix_rank {K : Type*} [Field K] [Fintype K]
    (f : K[X]) (hf : 0 < f.natDegree) (hsq : Squarefree f) :
    Irreducible f ↔
      (frobeniusMatrix (AdjoinRoot.powerBasis
        (Polynomial.ne_zero_of_natDegree_gt hf)) - 1).rank = f.natDegree - 1 := by
  let pb := AdjoinRoot.powerBasis (Polynomial.ne_zero_of_natDegree_gt hf)
  have hdim : pb.dim = f.natDegree := rfl
  have hr := frobenius_rank_add_fixedSpace pb.basis
  simp only [Fintype.card_fin] at hr
  change _ = f.natDegree at hr
  rw [irreducible_iff_frobeniusFixedSpace_finrank f hf hsq]
  change Module.finrank K (frobeniusFixedSpace K (AdjoinRoot f)) = 1 ↔
    (frobeniusMatrix pb - 1).rank = f.natDegree - 1
  change (frobeniusMatrix pb - 1).rank + _ = _ at hr
  omega

end SparseIrred.UpperBounds
