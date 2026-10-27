import SparseIrred.UpperBounds.IntegerBoundary
import SparseIrred.UpperBounds.IntegerRootCriterion
import SparseIrred.UpperBounds.GoodReductionRoots
import SparseIrred.UpperBounds.FiniteFieldTest
import SparseIrred.UpperBounds.PrimeCounting
import SparseIrred.UpperBounds.PowerBasisDiscriminant
import SparseIrred.UpperBounds.PrimeAverageInstantiation
import SparseIrred.UpperBounds.Section4Complete

/-!
# Ingredients of sparse irreducibility upper bounds

Formalized upper bounds for Sections 3--4 of `1021-AI4Math_Irreducibility.pdf`.
The Section 3 conclusions retain the named external analytic and primality
theorems. Section 4's uniform PSPACE conclusion and complete deterministic
machine certification have no mathematical or implementation premise. See the
section-specific completion and machine-certification reports for precise statements.
-/
