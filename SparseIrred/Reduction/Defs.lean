import SparseIrred.Construction.Defs
import SparseIrred.Sparse.Canonical

/-!
# The reduction as a total bit-string function

Source language: complexitylib's `Complexity.SAT.ThreeSAT.language`
(`{z | ∃ φ, z = φ.encode ∧ φ.Is3CNF ∧ φ.Satisfiable}`), decoded by `CNF.decode3?`.

* `decode3? x = none` (malformed code, or a formula with a clause of length `≠ 3`): output the
  fixed irreducible polynomial `X` (such `x` lie in `ThreeSAT.languageᶜ`);
* `Φ = []` or no variables (`n = 0` or `s = 0` in the notes): decide `Φ` directly and output the
  fixed reducible `X² - 1` when it is satisfiable, the fixed irreducible `X` otherwise;
* otherwise output `H_M` with `M = 2^{20(w+1)} (m+1)^6`.

The output is always the canonical binary-sparse code `encPoly` of a polynomial of positive degree.
-/

open Polynomial Complexity

namespace SparseIrred

open Complexity.SAT

open Classical in
/-- The polynomial produced by the reduction. -/
noncomputable def reducePoly (x : List Bool) : ℤ[X] :=
  match CNF.decode3? x with
  | none => X
  | some Φ => if Φ = [] ∨ numVars Φ = 0 then (if Φ.Satisfiable then X ^ 2 - 1 else X) else Hfinal Φ

/-- The reduction map on bit strings. -/
noncomputable def reduce (x : List Bool) : List Bool := encPoly (reducePoly x)

end SparseIrred
