import SparseIrred.UpperBounds.RealCutoffGeneralGap
import SparseIrred.UpperBounds.Machine.GeneralGapConclusion
import SparseIrred.UpperBounds.Machine.StreamingTrace
import SparseIrred.UpperBounds.Machine.StreamingLinearCore
import SparseIrred.UpperBounds.Machine.StreamingBinaryLoad

/-!
# The original paper's complete Section 3 scope

This entry point collects the actual deterministic enumeration and its
polynomial-space whole-input implementation, the linear-space trial-division
core, Remark 16 for every fixed positive gap, and Proposition 13 at arbitrary
real cutoffs. The external analytic and AKS theorems remain named parameters;
no internal mathematical or machine-implementation certificate is assumed.
-/
