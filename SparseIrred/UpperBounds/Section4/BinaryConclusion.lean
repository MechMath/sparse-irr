import SparseIrred.UpperBounds.Section4.BinaryFirstStageRealization
import SparseIrred.UpperBounds.Section4.BinaryPrimeStage
import SparseIrred.UpperBounds.Section4.BinaryExtensionStage

/-!
# Theorem 18 with no implementation premise

The binary program below includes all parsing, arithmetic, matrix-address
instructions, stack transitions, field validation and output. Its polynomial-time
step proof constructs the previously omitted realization. The full deterministic
machine and its space bound follow without an external theorem or implementation
certificate parameter.
-/

namespace SparseIrred.UpperBounds.Section4

open Complexity Complexity.TM

/-- The complete executable binary transition, uniformly over all input fields. -/
def section4BinaryStep : List Bool → List Bool :=
  uniformBinaryStep firstStageRoutines binaryModulusStage binaryExtensionStage

theorem section4BinaryStep_mem_FP : section4BinaryStep ∈ FP :=
  uniformBinaryStep_mem_FP _ _ _

/-- The implementation interface is now inhabited by the explicit binary program. -/
theorem section4BinaryStep_realization : UniformLocalStepRealization section4BinaryStep :=
  uniformBinaryStep_realization _ _ _ firstStageRoutines_realization
    binaryModulusStage_realization binaryExtensionStage_realization

/-- Original Theorem 18, unconditionally, for the uniform encoded language. -/
theorem section4_irreducibility_mem_PSPACE_unconditional : UniformIrredLang ∈ PSPACE :=
  section4_irreducibility_mem_PSPACE section4BinaryStep_realization

/-- Complete machine certification: one fixed deterministic multitape machine
handles every characteristic and extension degree, uses polynomial decision space
at every reachable configuration, halts, and writes the correct answer. -/
theorem section4_complete_machine :
    ∃ (k : ℕ) (M : TM k) (q : Polynomial ℕ),
      (∀ s c, M.reaches (M.initCfg s) c → c.WithinDecisionSpace s.length (q.eval s.length)) ∧
      (∀ s, ∃ c, M.reaches (M.initCfg s) c ∧ M.halted c ∧
        c.output.cells 1 = Γ.ofBool (uniformDecision s)) :=
  section4_machine_exists section4BinaryStep_realization

/-- The first binary update creates the exact first mathematical configuration. -/
theorem section4BinaryStep_initial (s : List Bool) :
    section4BinaryStep (pair [] s) = uniformCode s (uniformStages s).initial :=
  section4BinaryStep_realization.initialize_state s

/-- Every encoded local transition agrees with the mathematical staged program. -/
theorem section4BinaryStep_correct (s : List Bool) (c : (uniformStages s).State)
    (hc : ¬c.Halted) :
    section4BinaryStep (uniformCode s c) = uniformCode s ((uniformStages s).step c) :=
  section4BinaryStep_realization.step s c hc

theorem section4BinaryStep_publish (s : List Bool) (b : Bool) :
    section4BinaryStep (uniformCode s (.done b)) = [b] :=
  section4BinaryStep_realization.publish s b

end SparseIrred.UpperBounds.Section4
