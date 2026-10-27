import SparseIrred.UpperBounds.Section4.OracleMachineMatrixSource
import SparseIrred.UpperBounds.Section4.OracleMachineBerkowitzLoop

/-!
# Lemma 17: a real uniform determinant machine from a space-bounded entry machine

The dimension and finite-field presentation remain binary input data. The input
validity condition is the domain of the paper's matrix-computation lemma; the
machine never branches on an unimplemented validity test. Every controller,
field operation, oracle dispatch and full-value output routine is implemented
and verified here. Only the original entry-machine premise remains.
-/

noncomputable section
namespace SparseIrred.UpperBounds.Section4

open Complexity Matrix

set_option backward.isDefEq.respectTransparency false

variable {k : ℕ} {M : TM k} {A : OracleMatrixFamily} {space : Polynomial ℕ}

theorem MatrixEntryMachine.compiler_laws (E : MatrixEntryMachine M A space) :
    OracleDomainCompilerLaws (binaryBerkowitzLoopOps (matrixOracleWindow M space))
      OracleMatrixInputValid E.programInput := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    exact E.controller_laws x hx
  · intro x hx
    letI : Fact (oracleMatrixField x).Valid := ⟨hx.1⟩
    have h := binaryBerkowitzLoop_setup (matrixOracleWindow M space)
      (oracleMatrixDimension x) (oracleMatrixField x) (oracleMatrixDescription x)
    rw [hx.2] at h
    exact h
  · intro x hx c
    letI : Fact (oracleMatrixField x).Valid := ⟨hx.1⟩
    exact binaryBerkowitzLoop_completed (matrixOracleWindow M space)
      (oracleMatrixField x) (oracleMatrixDescription x)
      ((matrixOracleWindow M space).eval x.length) c
  · intro x hx v
    letI : Fact (oracleMatrixField x).Valid := ⟨hx.1⟩
    exact binaryBerkowitzLoop_verdict (matrixOracleWindow M space)
      (oracleMatrixField x) (oracleMatrixDescription x)
      ((matrixOracleWindow M space).eval x.length) v

/-- One deterministic machine computes the complete determinant code for every valid
binary matrix input. The sole implementation premise concerns the original entry TM,
which may take arbitrary time within its stated polynomial space bound. -/
theorem lemma17_uniform_scalar_machine (E : MatrixEntryMachine M A space) :
    ∃ (tapes : ℕ) (tm : TM tapes) (p : Polynomial ℕ),
      (∀ x (hx : OracleMatrixInputValid x) c,
        tm.reaches (tm.initCfg x) c → c.WithinDecisionSpace x.length (p.eval x.length)) ∧
      (∀ x (hx : OracleMatrixInputValid x), ∃ c,
        tm.reaches (tm.initCfg x) c ∧ tm.halted c ∧
          c.output.HasOutput (oracleMatrixScalarCode x hx (A x).det)) := by
  obtain ⟨tapes, tm, p, hspace, houtput⟩ := E.compiler_laws.machine_exists_of_window
    (determinantControllerBound (matrixOracleWindow M space)) (matrixOracleWindow M space)
    determinantValueBound determinantDepthBound
    E.controller_space (fun x hx i ↦ le_rfl) E.value_space E.depth_bound
  refine ⟨tapes, tm, p, hspace, ?_⟩
  intro x hx
  obtain ⟨c, hr, hh, ho⟩ := houtput x hx
  exact ⟨c, hr, hh, by rw [E.output_eq_det x hx] at ho; exact ho⟩

end SparseIrred.UpperBounds.Section4
