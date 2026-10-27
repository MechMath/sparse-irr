import SparseIrred.Machine.StrPipeline
import SparseIrred.Machine.DataCorrect

/-!
# Assembly: `reduce ∈ FP`

The reduction `reduce` is computed by a function `reduceStr` on bit strings, built in Cobham's
function algebra, in three layers:

1. `Machine/Primes.lean`, `Machine/Data.lean`: a computable data-level algorithm `reduceTerms` on
   sparse term lists `List (ℤ × ℕ)`;
2. `Machine/DataCorrect.lean`: `canonTerms (reducePoly x) = reduceTerms x`, hence
   `reduce x = encITerms (reduceTerms x)` (`reduce_eq_encITerms`);
3. `Machine/StrArith.lean`, `StrCnf.lean`, `StrPrimes.lean`, `StrClause.lean`,
   `StrPipeline.lean`: string functions computing the codes of the data-level results, each with
   a Cobham membership proof.

The algorithm works only with sparse term lists whose coefficients and exponents are binary
numerals; no list or array indexed by `N`, `M` or a numerical degree is ever built.  Only
quantities bounded by a polynomial in the input length are handled in unary: variable indices, the
primes `q_i` (all below `primeBound |x|`, `oddPrime_le`, `firstOddPrimes_primeBound`) and the
exponent `20 (w + 1)` of `2^{20(w+1)}` (at most `wBound |x|`, `twenty_mul_wD_succ_le`).  The size
bounds behind this are in `Machine/Bounds.lean`: `length_clauseTermsD_le_cube` (each `C_j` has at
most `Q³` raw terms), `length_sRawD_le` (`S` has at most `s Q⁶` raw terms),
`Qmax_oddPrimeList_le` (`Q ≤ 64 (n + 1)²`), `wD_hmA_le` and `twenty_mul_wD_succ_le`; the remaining
size statements of the notes are `natAbs_coeff_Spoly_le` and `Dexp_lt_three_mul_bigN`.

`reduceStr` implements the branch structure of `reducePoly`:

* if `x` is not the code of an exact-3 CNF (`validStr x = [false]`, i.e. `decode3? x = none`),
  the output is the constant code `encITerms [(1, 1)]` of `X`;
* if `x = []`, the only code of the empty CNF (`decode3?_eq_some_nil_iff`), the output is the
  constant code `encITerms [(-1, 0), (1, 2)]` of `X² - 1` (the empty CNF is satisfiable; for an
  exact-3 CNF, `numVars Φ = 0` already forces `Φ = []`);
* otherwise the output is `hmStr x`, the code of `H_M`.

`reduceStr_eq_encITerms` identifies `reduceStr` with the data-level algorithm, and Cobham
membership (`cobham_reduceStr`) together with complexitylib's `CobhamFP_eq_FP` gives
`reduce_mem_FP_machine : reduce ∈ FP`.
-/

open Complexity SparseDiv SparseDiv.StringArith SparseDiv.Appendix SparseGcd Complexity.SAT

namespace SparseIrred.Machine

open SparseIrred

/-- The whole reduction on bit strings. -/
def reduceStr (x : List Bool) : List Bool :=
  caseBit₀ (validStr x)
    (caseBit₀ (nonemptyFlag x) (hmStr x) (encITerms [(-1, 0), (1, 2)]))
    (encITerms [(1, 1)])

/-- A decodable string is the code of the empty CNF iff it is empty. -/
theorem decode3?_eq_some_nil_iff {x : List Bool} {Φ : CNF} (hx : CNF.decode3? x = some Φ) :
    Φ = [] ↔ x = [] := by
  obtain ⟨rfl, -⟩ := CNF.decode3?_eq_some_iff.1 hx
  constructor
  · rintro rfl
    rfl
  · intro h
    exact CNF.encode_injective (h.trans rfl)

/-- The string function computes the code of the data-level reduction. -/
theorem reduceStr_eq_encITerms (x : List Bool) : reduceStr x = encITerms (reduceTerms x) := by
  rw [reduceStr, validStr_eq, reduceTerms]
  rcases h : CNF.decode3? x with _ | Φ
  · simp
  · by_cases hΦ : Φ = []
    · have hx : x = [] := (decode3?_eq_some_nil_iff h).1 hΦ
      subst hx
      simp [hΦ, nonemptyFlag_nil]
    · have hx : x ≠ [] := fun hx => hΦ ((decode3?_eq_some_nil_iff h).2 hx)
      simp [hΦ, nonemptyFlag_of_ne_nil hx, hmStr_eq h]

theorem reduceStr_eq_reduce (x : List Bool) : reduceStr x = reduce x := by
  rw [reduceStr_eq_encITerms, reduce_eq_encITerms]

theorem cobham_reduceStr : Cobham fun v : Fin 1 → List Bool => reduceStr (v 0) := by
  unfold reduceStr
  exact Cobham.iteFn cobham_validStr
    (Cobham.iteFn (Cobham.nonemptyFn (.proj 0)) cobham_hmStr (Cobham.const _)) (Cobham.const _)

theorem reduceStr_mem_FP : reduceStr ∈ FP := by
  rw [← CobhamFP_eq_FP]
  exact cobham_reduceStr

/-- **The reduction is computable in polynomial time**: `reduce ∈ FP`. -/
theorem reduce_mem_FP_machine : reduce ∈ FP := by
  have h : reduceStr = reduce := funext reduceStr_eq_reduce
  rw [← h]
  exact reduceStr_mem_FP

end SparseIrred.Machine
