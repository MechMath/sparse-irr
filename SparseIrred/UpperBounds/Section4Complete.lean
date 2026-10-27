import SparseIrred.UpperBounds.Section4.Conclusion
import SparseIrred.UpperBounds.Section4.FactorRank
import SparseIrred.UpperBounds.Section4.DecisionScan
import SparseIrred.UpperBounds.Section4.BerkowitzOracleSpace
import SparseIrred.UpperBounds.Section4.StackFaithful
import SparseIrred.UpperBounds.Section4.EntryMachineUniformFaithful
import SparseIrred.UpperBounds.Section4.BinaryConclusion
import SparseIrred.UpperBounds.Section4.OracleMachineScalarCompiler
import SparseIrred.UpperBounds.Section4.OracleMachineLemma17
import SparseIrred.UpperBounds.Section4.EntryMachineFaithful
import SparseIrred.UpperBounds.Section4.EntryMachinePower

/-!
# Original-paper Section 4

Equations (47)--(49), the oracle-space composition of Lemma 17, the uniform
finite-field input language and its complete mathematical decision program.

`Section4.section4_irreducibility_mem_PSPACE_unconditional` is Theorem 18 without
any mathematical or implementation premise. The executable `section4BinaryStep`
inhabits the older `UniformLocalStepRealization` interface, and
`section4_complete_machine` certifies the full deterministic machine. See
`docs/SECTION4_MACHINE_CERTIFICATION_2026-10-23.md` for the implementation and
`docs/SECTION4_FORMALIZATION_2026-10-22.md` for the mathematical term map.

`Section4.lemma17_uniform_scalar_machine` compiles the determinant coroutine
against any actual entry machine satisfying the explicitly stated spatial-window
and output contract; all controller and compilation implementations are proved.
-/
