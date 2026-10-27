# Blueprint: `reduce ∈ FP` (Theorem 8, "polynomial sparse-bit cost", notes p. 7)

**Status: proved.** `SparseIrred.reduce_mem_FP` (`Machine/ReduceFP.lean`) is
`Machine.reduce_mem_FP_machine`; `#print axioms` gives only `propext`, `Classical.choice`,
`Quot.sound` (see `docs/AXIOMS.txt`).

---

## 1. Design constraints (from the task) and how they are met

| Constraint | Realisation |
|---|---|
| Keep the sparse representation; never build arrays indexed by `N`, `M` or numerical degrees | Every polynomial is a framed list of `(coefficient, exponent)` blocks. Exponents (`r·m_i`, `N`, `D`, `M`, `M+N`) are **binary** numerals. The only unary quantities are listed in the next row. |
| Unary quantities used | Variable indices (≤ input length); prime candidates `c < primeBound |x| = 64(|x|+2)²+1`; the primes `q_i` themselves (the `r < q_i` loop of `P⁻_i`); the count `20(w+1)` (≤ `wBound |x|`, §5). |
| Prime generation | First `n` odd primes, by trial division by every `d < c` over unary candidates below `primeBound |x|`. Correct because `q_i = nth Prime (i+1) ≤ 64 (i+2)²` (`Primes.nth_prime_le`, via Chebyshev). |
| Integer arithmetic | Sign–magnitude codes `encInt` (from SparseDivComplexity). The new functions (`mulIntStr`, `scale3Str`, `canonIntStr`) always emit a canonical sign and magnitude. |
| Sparse multiplication | `mulITermsStr`: all pairwise products, no merging. |
| Sparse addition, sort, merge, drop zeros | The sibling's `normalizeZStr` (insertion sort, FP), followed by the new `canonITermsStr` so that the output is **literally** `encITerms (normalizeZ l)`. |
| Laurent `S` | The offset trick. `K` is the largest raw exponent of all `C_j`, and `S_raw = Σ_j C_j · reflect_K(C_j)` denotes `X^K S(X)` with natural exponents. `A` is obtained by subtracting the smallest exponent `K − D`, so `D` is never needed as a separate numeral. |
| `w` numerically polynomial | `20(w+1) ≤ wBound |x|`, an explicit degree-26 polynomial (`Bounds.twenty_mul_wD_succ_le`). The unary ruler `wRuler x` has exactly this length, and binary→unary conversion of `20(w+1)` is clamped by it. |
| `(m+1)^6`, `M` | `pow6Str`, and `M = 0^{20(w+1)} ++ encNat((m+1)^6)` (`shiftStr`, i.e. `2^k·y` for `y > 0`). |
| Output `encPoly = encITerms (canonTerms)` | `outStr = A ++ ⟦(-1, M)⟧ ++ ⟦(1, M+N)⟧`. It is canonical because `deg A < M` (`Data.degreeZ_lt_MD`). |
| Proof in complexitylib's `FP` | Cobham membership, then `CobhamFP_eq_FP`. |

---

## 2. Three layers

1. **Data level** (`Primes`, `Data`) — computable functions on `ITerms = List (ℤ × ℕ)`, CNFs and naturals, exercised with `#eval`.
2. **Math bridge** (`DataCorrect`, `Bounds`)
   - `DataCorrect`: `canonTerms (reducePoly x) = reduceTerms x`, hence `reduce x = encITerms (reduceTerms x)`.
   - `Bounds`: the notes' size facts.
3. **String level** (`StrArith`, `StrCnf`, `StrPrimes`, `StrClause`, `StrPipeline`, `Assemble`)
   - Each string function is proved **literally equal** to the encoding of its data-level result (canonical numerals everywhere).
   - Each has a Cobham lemma in `_comp` form: `Cobham g₀ → … → Cobham fun v ↦ F (g₀ v) …`.

### Dependency order (imports)

```
Primes ─→ Data ─→ DataCorrect ─→ Bounds ─────────────┐
            └─→ StrArith ─→ StrCnf ─────────────────┤
                   └─→ StrPrimes ─→ StrClause ──────→ StrPipeline ─→ Assemble
```

`Assemble` imports `StrPipeline` and `DataCorrect`. `StrPipeline` imports `StrClause`, `StrCnf` and `Bounds`.

---

## 3. The pipeline, stage by stage

The input is `x : List Bool`. The notation is: `t = encCNFU Φ` (the internal CNF code, variables unary), `qs` (prime list), `N = qs.prod`.

| # | Stage | Data level (`Data`/`Primes`) | String level | Literal-correctness lemma | Cobham lemma |
|---|---|---|---|---|---|
| 0 | Parse and exact-3 check | `CNF.decode3?` | `SparseGcd.parseCnfStr`, `is3Str`, `validStr` | `pairSnd_parseCnfStr`, `is3Str_encCNFU`, `validStr_eq : validStr x = [(decode3? x).isSome]` | `parseCnfStr_mem_FP` (sibling), `cobham_is3Str_comp`, `cobham_validStr` |
| 1 | Occurrence and rank | `Occurs`, `varIdx`, `numVars` (frozen) | `clauseHasStr`, `occursStr`, `rankStr`, `numVarsU` | `occursStr_eq`, `rankStr_eq : rankStr (unaryN v) t = unaryN (varIdx Φ v)`, `numVarsU_eq` | `cobham_occursStr_comp`, `cobham_rankStr_comp`, `cobham_numVarsU_comp` |
| 2 | Renumbering | `renumLit`, `renumber` | `renumStr` | `renumStr_eq : renumStr (encCNFU Φ) = encCNFU (renumber Φ)` | `cobham_renumStr_comp` |
| 3 | Primes | `oddPrimesBelow T`, `firstOddPrimes T n`, `primeBound L` | `isOddPrimeU` (trial division), `oddPrimesStr`, `primesStr`, `primeRuler` | `isOddPrimeU_eq`, `oddPrimesStr_eq`, `primesStr_eq` | `cobham_isOddPrimeU_comp`, `cobham_oddPrimesStr_comp`, `cobham_primesStr_comp`, `cobham_primeRuler` |
| 4 | `N` and `m_i` | `qs.prod`, `N / qs.getD i 0` | `bigNStr` (`prodStr`), `TermsStr.divBits₀` | `prodStr_frame_encNat`, `bigNStr_eq` | `cobham_bigNStr_comp` |
| 5 | Literal lists | `posLitTerms m = [(-1,0),(1,m)]`, `negLitTerms q m = [(1,rm) ∣ r<q]`, `litTermsD` | `posLitStr`, `negLitStr`, `litStr` (`nthBlockStr` for `q_i`) | `nthBlockStr_primes`, `posLitStr_eq`, `negLitStr_eq`, `litStr_eq` | `cobham_litStr_comp` |
| 6 | Clause products `C_j` (raw, ≤ `Q³` terms) | `mulITerms`, `clauseTermsD` (`foldr`) | `prodBlockZ`, `mulITermsStr`, `clauseStepStr`, `clauseStr` (unrolled **3** times) | `mulIntStr_encInt`, `prodBlockZ_encITerm`, `mulITermsStr_eq`, `clauseStepStr_iterate`, `clauseStr_eq` (needs `c.length ≤ 3`) | `cobham_mulITermsStr_comp`, `cobham_clauseStr_comp` |
| 7 | Offset `K` and `S_raw = X^K S` (≤ `sQ⁶` terms) | `clauseListD`, `offsetD = degreeZ (flatten)`, `reflectITerms`, `sRawD` | `csStr`, `offsetStr` (`degreeStr`), `reflectStr`, `sRawStr` | `csStr_eq`, `degreeStr_encITerms`, `offsetStr_eq`, `reflectStr_eq`, `sRawStr_eq` | `cobham_csStr_comp`, `cobham_degreeStr_comp`, `cobham_reflectStr_comp`, `cobham_sRawStr_comp` |
| 8 | Collect like terms | `normalizeZ` (sibling), `sNormD` | `canonITermsStr ∘ normalizeZStr`, `sNormStr` | `canonITermsStr_of_decITerms`, `canonITermsStr_normalizeZStr`, `sNormStr_eq` | `cobham_normalizeZStr_comp`, `cobham_canonITermsStr_comp`, `cobham_sNormStr_comp` |
| 9 | `A = 3X^D S` | `headExpD` (= `K − D`), `aTermsD`, `hmA` | `headExpStr`, `scale3Str`, `aTermsStr` | `headExpStr_encITerms`, `scale3Str_encInt`, `aTermsStr_eq` | `cobham_aTermsStr_comp` |
| 10 | `w = 4 + Σ(3c)² + #A` | `sqSumD`, `wD` | `sqStep`, `sqSumStr`, `wStr` | `sqSumStr_eq`, `wStr_eq` | `length_sqStep_le` (growth, `c = 2`), `cobham_sqSumStr_comp`, `cobham_wStr_comp` |
| 11 | `m = max(N, deg A)`, `(m+1)⁶` | `mD` | `maxBinStr`, `mStr`, `pow6Str` | `maxBinStr_encNat`, `mStr_eq`, `pow6Str_encNat` | `cobham_maxBinStr_comp`, `cobham_pow6Str_comp` |
| 12 | `20(w+1)` in unary | `wBound` (Bounds) | `binToUnaryStep`, `binToUnaryStr k T` (clamped by `T`), `wRuler` | `binToUnaryStep_iterate`, `binToUnaryStr_eq` (needs `k ≤ |T|`) | `cobham_binToUnaryStr_comp` (`Cobham.iterFn`, ruler `T`), `cobham_wRuler` |
| 13 | `M = 2^{20(w+1)}(m+1)⁶` | `MD` | `shiftStr`, `MStr` | `shiftStr_eq` (`y > 0`), `MStr_eq` (needs `20(w+1) ≤ |T|`) | `cobham_shiftStr_comp`, `cobham_MStr_comp` |
| 14 | Output | `outTermsD N A = A ++ [(-1,M),(1,M+N)]`, `hmCore`, `hmTerms` | `outStr`, `hmCoreStr`, `hmStr` | `outStr_eq`, `hmCoreStr_eq`, `hmStr_eq : decode3? x = some Φ → hmStr x = encITerms (hmTerms (primeBound |x|) Φ)` | `cobham_outStr_comp`, `cobham_hmCoreStr_comp`, `cobham_hmStr` |
| 15 | Branches | `reduceTerms` | `reduceStr` | `decode3?_eq_some_nil_iff`, `reduceStr_eq_encITerms`, `reduceStr_eq_reduce` | `cobham_reduceStr`, `reduceStr_mem_FP` |

**Branch structure.** `reduceStr x = caseBit₀ (validStr x) (caseBit₀ (nonemptyFlag x) (hmStr x) ⟦X²−1⟧) ⟦X⟧`.

- `decode3? x = none` gives the code `encITerms [(1,1)]` of `X`.
- For exact-3 codes, `Φ = []` iff `x = []`. That case gives `encITerms [(-1,0),(1,2)]`, since `[]` is satisfiable.
- `numVars Φ = 0` with `Φ ≠ []` is impossible for exact-3 formulas (`numVars_ne_zero_of_is3CNF`). So the frozen branch `Φ = [] ∨ numVars Φ = 0` agrees with the machine's branch.

---

## 4. The math bridge (`DataCorrect.lean`)

**Main theorems:**
- `canonTerms_Apoly (Φ ≠ [])`: `canonTerms (Apoly Φ) = hmA (oddPrimeList (numVars Φ)) (renumber Φ)`.
- `canonTerms_Hfinal (Φ ≠ [])`: `canonTerms (Hfinal Φ) = hmCore (oddPrimeList (numVars Φ)) (renumber Φ)`.
- `canonTerms_reducePoly x = reduceTerms x`, and `reduce_eq_encITerms`.

**Chain of lemmas:**
1. `prod_oddPrimeList`, `getD_oddPrimeList`.
2. `toPolyZ_litTermsD` (the literal equals `litPoly`, using `varIdx_lt_numVars`).
3. `toPolyZ_clauseTermsD`, `clauseListD_renumber`.
4. Laurent bookkeeping:
   - `coeff_toLaurent_natCast`, `coeff_toLaurent_of_neg`, `coeff_T_mul`;
   - `toLaurent_toPolyZ_reflectITerms` (needs every exponent `≤ K`);
   - `toLaurent_toPolyZ_sRawD`;
   - **`toLaurent_toPolyZ_sNormD`**: `toLaurent (toPolyZ S) = T K * Spoly Φ`.
5. `coeff_eq_of_toLaurent_eq`, `headExpD_le`, `headExpD_eq_natTrailingDegree`.
6. **`headExpD_sNormD_add_Dexp`**: the head exponent plus `Dexp Φ` equals `K`, which shows `D ≤ K`. It uses `Spoly_coeff_Dexp_ne_zero` and `Spoly_coeff_eq_zero_of_lt`.
7. `coeff_toPolyZ_aTermsD`: `(A).coeff k = 3 · S.coeff (k + head)`.
8. `toPolyZ_hmA` via `Apoly_coeff`, then `normalizedZ_hmA`.
9. Canonical-list reading:
   - `weight_eq_sqSumD`, `termCount_eq_length`, `natDegree_eq_degreeZ`;
   - `canonTerms_cPoly = [(1,0),(-1,N)]`;
   - `wParam_eq`, `mParam_eq`, `Mval_eq`.
10. `canonTerms_Hfinal`, using `toPolyZ_outTermsD` and `normalizedZ_outTermsD`.
11. Branch lemmas:
    - `numVars_ne_zero_of_is3CNF`, `numVars_le_encode_length`;
    - `canonTerms_X`, `canonTerms_X_sq_sub_one`;
    - `firstOddPrimes_encode` (the machine's primes on `Φ.encode` equal `oddPrimeList`), `hmTerms_encode`;
    - `canonTerms_reducePoly`.

---

## 5. Size facts (`Bounds.lean`, `Primes.lean`)

**Primes.** `nth_prime_le : nth Prime k ≤ 64 (k+1)²` goes through Chebyshev's `2^x ≤ (x+1)·lcm(1..x)` (`mathlib.md` §8.8). Consequences:
- `oddPrime_le : q_i ≤ 64 (i+2)²`.
- `oddPrime_lt_primeBound`.
- `firstOddPrimes_eq`: the filtered candidate list is `oddPrimeList n` once every `q_i < T`. The proof goes via `Nat.count` and `Nat.nth_count`.
- `firstOddPrimes_primeBound`, which applies because `n ≤ |x|+1`.

**Notes p. 7, in the notes' notation** (`Q = Qmax qs = max(2, max q_i)`):
- `length_litTermsD_le`: every literal list has at most `Q` terms.
- `length_clauseTermsD_le_cube`: **each `C_j` has at most `Q³` raw terms.**
- `length_sRawD_le`: **`S` has at most `s·Q⁶` raw terms.**
- `natAbs_coeff_Spoly_le`: **`|[X^e]S| ≤ s·Q⁶`.**
- `offsetD_lt_three_mul_bigN` and `Dexp_lt_three_mul_bigN`: **raw exponents of the `C_j`, and `D`, are `< 3N`.**
- `Qmax_oddPrimeList_le : Q ≤ 64(n+1)²`, and `Qnotes_le`.

**`w` (load-bearing).** Write `R = #S_raw`.
1. `unitCoeffs_*`: raw coefficients are `±1`, so `absSum S_raw = R`.
2. `absSum_normalizeZ_le`: collecting like terms does not increase `Σ|c|` (triangle inequality through `insertTermZ`).
3. `sqSumD_le : Σc² ≤ (Σ|c|)²`, `sqSumD_aTermsD : Σ(3c)² = 9Σc²`.
4. Together these give `wD_hmA_le : w ≤ 4 + 9R² + R` with `R ≤ s·Q⁶`.
5. `length_le_encode_length : s ≤ |x|`.
6. **`twenty_mul_wD_succ_le : 20(w+1) ≤ wBound |x|`**, where `wBound L = 20(5 + 9·rawBound L² + rawBound L)` and `rawBound L = L·(64(L+2)²)⁶`.
7. The notes-level form is `wParam_le_wBound : 20 (wParam Φ + 1) ≤ wBound |Φ.encode|`.

---

## 6. Cobham/FP techniques used (for maintenance)

- **Maps.** `TermsStr.cobham_mapBlocks_comp` needs no length hypothesis and allows parameters. It is used for `reflectStr`, `aTermsStr`, `canonITermsStr`, `negLitStr`, `renumStr` (nested), `csStr` and `sRawStr`.
- **Folds.** `StringArith.cobham_foldBlocks` requires parameter-independent growth `|acc'| ≤ |acc| + c(|b|+1)`.
  - Flags (`length_andBit`, `length_orBit`): `is3Str`, `clauseHasStr`, `occursStr`, trial division.
  - Unary counter (+1): `rankStr`.
  - `acc ++ delimit c`: `oddPrimesStr`.
  - `sqStep`, which grows by at most `2(|b|+1)` (`length_sqStep_le`).
- **Fixed iteration.** `TermsStr.cobham_iterate` with `k = 3` for the clause product. No length analysis is needed; correctness assumes `c.length ≤ 3`.
- **Clocked iteration.** `Cobham.iterFn` in `binToUnaryStr`, with the ruler `T` as clock and width. The state grows by at most 1 per step.
- **Sibling FP functions inside the algebra.** `cobham_comp₁ (FP_subset_CobhamFP h)` for `parseCnfStr`, `normalizeZStr`, `degreeStr` and `numVarsStr`.
- **Rulers.** `primeRuler` and `wRuler` are computable `List.replicate`s. Their Cobham proofs rewrite them to `SparseGcd.polyUnary q` for an explicit `q : Polynomial ℕ`.
- **Final step.** `reduceStr_mem_FP` is `CobhamFP_eq_FP` applied to `cobham_reduceStr`.

**Pitfalls that were handled:**
- `addBits`, `mulBits` and `addInt` produce padded numerals, so every emitted numeral is passed through `canonBits`.
- The output of `normalizeZStr` is not canonical; `canonITermsStr` fixes it. That needs nonzero coefficients, which is `normalizedZ_normalizeZ`.2.
- The sign of a zero product is forced to `false` in `mulIntStr`.
- `divBits₀` is used so that `N/0 = 0`.
- `nthBlockStr`'s default `[]` is `unaryN 0`, which matches `qs.getD i 0`.
- The argument order of `lenLeFlag` is reversed; see `lenLeFlag_eq_decide`.

---

## 7. Upstream frozen statements used (black boxes)

- From `Construction/Laurent.lean`: `bigN_pos`, `three_le_oddPrime`, `mExp_mul_oddPrime`, `varIdx_lt_numVars`, `Spoly_coeff_eq_zero_of_lt`, `Spoly_coeff_Dexp_ne_zero`, `Apoly_coeff`.
- Everything else is complexitylib, mathlib, or the sibling project (`SparseGcd.*`, `SparseDiv.*`), and all of it is sorry-free (checked with `#print axioms`).

---

## 8. Integration (orchestrator)

1. Edit the frozen `Machine/ReduceFP.lean`. **Only the import and the proof body change; the statement does not.**
   ```lean
   import SparseIrred.Reduction.Defs
   import Complexitylib.Classes.P
   import SparseIrred.Machine.Assemble
   ...
   theorem reduce_mem_FP : reduce ∈ FP := Machine.reduce_mem_FP_machine
   ```
   I checked this in `scratch/fpbp_ax5.lean` (namespace `SparseIrred`): it compiles, with standard axioms only.
2. Optionally, add the ten new modules to `SparseIrred.lean`. They are reached anyway through `ReduceFP → Assemble`.
3. `lake build` will compile them in the order of §2, in about 1 minute in total.
   - During development they were compiled with `scratch/fpbp_mk.sh <file>`. It writes oleans to `scratch/fpbp_oleans/` (symlinked to the existing `.lake/build` oleans) and never touches `.lake`.
   - `lake env lean` alone works only for `Primes.lean`, because the others import new modules.

---

## 9. Validation beyond the proofs

The following were checked with `#eval` (`scratch/fpbp_eval1..5.lean`):
- The data algorithm on a 2-clause, 3-variable formula: `A` is palindromic of degree `2D = 406`, and `w = 2,068,231`.
- Every string stage against its data level on sample inputs.
- The whole `hmCoreStr_eq` for `[[x₀, ¬x₀, x₀]]`: `true` with a ruler of length exactly `20(w+1) = 6760`, and `false` with 6759. This confirms that the ruler hypothesis is sharp and necessary.

**Practical remark.** The notes' `M = 2^{20(w+1)}(m+1)⁶` is polynomial but enormous. The 2-clause example already has about 41 million output bits. This is a property of the construction, not of the machine.
