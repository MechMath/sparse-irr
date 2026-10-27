import SparseIrred.Reduction.Defs
import Complexitylib.Classes.P
import SparseIrred.Machine.Assemble

/-!
# The reduction is computable in polynomial time (`reduce ∈ FP`)

The proof exhibits a Cobham-algebra implementation working on the sparse representation only
(no array indexed by `N`, `M` or a numerical degree is ever built), proves it equal to `reduce`
pointwise, and uses complexitylib's `CobhamFP_eq_FP`, which connects Cobham's function algebra to
the library's Turing-machine time semantics (`FP`).
-/

open Complexity

namespace SparseIrred

theorem reduce_mem_FP : reduce ∈ FP := Machine.reduce_mem_FP_machine

end SparseIrred
