import SparseIrred.Construction.Irreducible
import SparseIrred.FFK.Ljunggren

/-!
# Closing the large-gap dependency for the polynomials of Theorem 8

The only external input of the notes' proof is the large-gap theorem of Sawin–Shusterman–Stoll
(`SSSLargeGap`), whose proof relies on Schinzel / Filaseta–Ford–Konyagin for the non-reciprocal
part and on Lehmer-type lower bounds (Voutier, Mossinghoff–Rhin–Wu) for reciprocal factors.

For the specific polynomials `H_M` of Theorem 8, `SparseIrred/FFK/Ljunggren.lean` proves
irreducibility in `ℤ[X]` without that hypothesis (this file only states the result):

* reciprocal factors are excluded by the identity
  `X^{M+N-2D} H_M - mirror(H_M) = B (X^{2M+N-2D} + 1)` (valid since `A` is palindromic) together
  with the root-of-unity argument ②, so `IsRelPrime H_M (mirror H_M)` and no Lehmer-type bound is
  needed;
* the Ljunggren condition `H_M · mirror H_M = k · mirror k → k ∈ {±H_M, ±mirror H_M}` is proved by
  the Filaseta–Ford–Konyagin argument (Illinois J. Math. 44 (2000), Lemma 3 and the proof of
  Theorem 2 / Corollary), with Capelli's theorem replaced by Eisenstein's criterion at the prime
  `(X - 1)` of `ℤ[X]`;
* `Polynomial.irreducible_of_mirror` (Ljunggren's method, in mathlib) concludes.
-/

open Polynomial

namespace SparseIrred

open Complexity.SAT

/-- Unsatisfiable branch, unconditionally. -/
theorem Hfinal_irreducible_of_unsat (Φ : CNF) (hΦ : Φ ≠ [])
    (hunsat : ¬Φ.Satisfiable) : Irreducible (Hfinal Φ) :=
  FFK.irreducible_Hfinal Φ hΦ hunsat

/-- The core semantics of the reduction: `Irreducible (H Φ) ↔ ¬ Satisfiable Φ`. -/
theorem Hfinal_irreducible_iff (Φ : CNF) (hΦ : Φ ≠ []) :
    Irreducible (Hfinal Φ) ↔ ¬Φ.Satisfiable :=
  ⟨fun h hsat => Hfinal_not_irreducible_of_satisfiable Φ hsat h,
    fun h => Hfinal_irreducible_of_unsat Φ hΦ h⟩

end SparseIrred
