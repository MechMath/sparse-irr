import SparseIrred.UpperBounds.FrobeniusMatrix
import SparseIrred.UpperBounds.CorankOneMinors
import SparseIrred.UpperBounds.SuccinctDeterminant

/-!
# Correctness of the resultant-and-minors irreducibility test

This is the algebraic decision procedure of Theorem 18. It uses the genuine quotient
algebra, the resultant, the Frobenius matrix, and division-free entry determinants.
There is no Turing-machine or sparse-encoding space claim in this module.
-/

open Polynomial Matrix

namespace SparseIrred.UpperBounds

variable {K : Type*} [Field K] [Fintype K]

/-- The rank of `B-I` is at most `n-1` because constants are fixed. -/
theorem frobenius_rank_le {R : Type*} [CommRing R] [Nontrivial R] [Algebra K R]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) K R) :
    (LinearMap.toMatrix b b (FiniteField.frobeniusAlgHom K R).toLinearMap - 1).rank ≤ n := by
  have : FiniteDimensional K R := Module.Finite.of_basis b
  have hfixed : 1 ≤ Module.finrank K (frobeniusFixedSpace K R) := by
    apply Submodule.one_le_finrank_iff.mpr
    intro he
    have hone : (1 : R) ∈ frobeniusFixedSpace K R := by simp
    rw [he, Submodule.mem_bot] at hone
    exact one_ne_zero hone
  have hr := frobenius_rank_add_fixedSpace b
  simp only [Fintype.card_fin] at hr
  omega

/-- For positive degree, the paper's two algebraic tests together are equivalent to
irreducibility. Any basis of the quotient can be used. -/
theorem irreducible_iff_resultant_and_minor (f : K[X]) (hf : 0 < f.natDegree) {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) K (AdjoinRoot f)) :
    Irreducible f ↔ f.resultant f.derivative ≠ 0 ∧
      ∃ i j : Fin (n + 1),
        (Matrix.submatrix
          (LinearMap.toMatrix b b (FiniteField.frobeniusAlgHom K (AdjoinRoot f)).toLinearMap - 1)
          i.succAbove j.succAbove).det ≠ 0 := by
  have hf0 := Polynomial.ne_zero_of_natDegree_gt hf
  have : Nontrivial (AdjoinRoot f) := AdjoinRoot.nontrivial f (by
    rw [Polynomial.degree_eq_natDegree hf0]
    exact_mod_cast hf.ne')
  have hr := frobenius_rank_add_fixedSpace b
  simp only [Fintype.card_fin] at hr
  have hminor := rank_eq_iff_exists_deleted_minor
    (LinearMap.toMatrix b b (FiniteField.frobeniusAlgHom K (AdjoinRoot f)).toLinearMap - 1)
    (frobenius_rank_le b)
  constructor
  · intro hi
    have hsq : Squarefree f := hi.squarefree
    refine ⟨(resultant_derivative_ne_zero_iff f hf0).mpr hsq, hminor.mp ?_⟩
    have hd := (irreducible_iff_frobeniusFixedSpace_finrank f hf hsq).mp hi
    omega
  · rintro ⟨hres, hm⟩
    have hsq := (resultant_derivative_ne_zero_iff f hf0).mp hres
    apply (irreducible_iff_frobeniusFixedSpace_finrank f hf hsq).mpr
    have := hminor.mpr hm
    omega

/-- A finite algebraic test using entry determinants, including the squarefree filter. -/
noncomputable def finiteFieldTest (f : K[X]) {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) K (AdjoinRoot f)) : Bool := by
  classical
  exact decide (
    determinantEntry (f.sylvester f.derivative f.natDegree f.derivative.natDegree) ≠ 0 ∧
      ∃ i j : Fin (n + 1),
        determinantEntry
          (Matrix.submatrix
            (LinearMap.toMatrix b b (FiniteField.frobeniusAlgHom K (AdjoinRoot f)).toLinearMap - 1)
            i.succAbove j.succAbove) ≠ 0)

/-- Correctness includes non-squarefree inputs and all characteristics. -/
theorem finiteFieldTest_correct (f : K[X]) (hf : 0 < f.natDegree) {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) K (AdjoinRoot f)) :
    finiteFieldTest f b = true ↔ Irreducible f := by
  classical
  simp only [finiteFieldTest, decide_eq_true_eq, determinantEntry_eq_det]
  exact (irreducible_iff_resultant_and_minor f hf b).symm

/-- A fixed choice of power basis, reindexed to the successor dimension of the minor test. -/
noncomputable def quotientPowerBasis (f : K[X]) (hf : 0 < f.natDegree) :
    Module.Basis (Fin (f.natDegree - 1 + 1)) K (AdjoinRoot f) :=
  (AdjoinRoot.powerBasis (Polynomial.ne_zero_of_natDegree_gt hf)).basis.reindex
    (finCongr (by change f.natDegree = f.natDegree - 1 + 1; omega))

/-- The semantic test for every finite-field polynomial, with constants rejected. -/
noncomputable def finiteFieldDecision (f : K[X]) : Bool :=
  if hf : 0 < f.natDegree then finiteFieldTest f (quotientPowerBasis f hf) else false

/-- All polynomial boundary cases are included in the semantic decision theorem. -/
theorem finiteFieldDecision_correct (f : K[X]) :
    finiteFieldDecision f = true ↔ Irreducible f := by
  unfold finiteFieldDecision
  split_ifs with hf
  · exact finiteFieldTest_correct f hf _
  · simp only [false_iff]
    exact fun hi ↦ hf hi.natDegree_pos

end SparseIrred.UpperBounds
