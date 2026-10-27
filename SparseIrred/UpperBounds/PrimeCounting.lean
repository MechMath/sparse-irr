import SparseIrred.UpperBounds.PrimeCountingDecision
import SparseIrred.UpperBounds.PrimeAverage
import SparseIrred.UpperBounds.WeightedDiscriminantBounds
import SparseIrred.UpperBounds.IntegerMahlerBounds
import SparseIrred.UpperBounds.ExceptionalPrimeCount
import SparseIrred.UpperBounds.RawInputBounds
import SparseIrred.UpperBounds.SparseModularEval
import SparseIrred.UpperBounds.RawPrimeCountingDecision
import SparseIrred.UpperBounds.Section3Arithmetic
import SparseIrred.UpperBounds.Section3Conclusion
import SparseIrred.UpperBounds.Machine
import SparseIrred.UpperBounds.RealCutoff
import SparseIrred.UpperBounds.Machine.GeneralGapConclusion
import SparseIrred.UpperBounds.Machine.StreamingTrace
import SparseIrred.UpperBounds.Section3Complete

/-!
# The standalone prime-counting proof: verified ingredients and conditional composition

This import collects the continuation based on `sparse_irreducibility_complete_qrh.pdf`.
The cutoff error, concrete witness counts, streaming invariants, sparse evaluations,
and input-length bounds are proved. The prime-counting and global root-average
estimates remain explicit hypotheses of the conditional decision theorem; no
unconditional `PP` or `PSPACE` membership theorem is provided by this import.

See `docs/PRIME_COUNTING_QRH.md` for exact statements and remaining work.
-/
