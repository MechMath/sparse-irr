# Status of the Theorem 8 formalization

For the public release of the integer Sections 2 and 3 formalization, start with
[the README](../README.md) and [the integer-results map](PAPER_1021_MAP.md).
The older theorem numbering and development history below are retained for context.
The latest build/audit run is recorded in [the release record](RELEASE_2026-10-27.md).

**Current scope, agreed on 2026-10-22:** cited external theorems may remain explicit hypotheses;
the paper's internal mathematical results and deductions must be proved in Lean. Algorithm steps
and machine implementations may be omitted, but the final conclusion must be a Lean theorem.
This policy applies to subsequent work in this project. In particular, the integer `PP` and
`PSPACE` conclusions are required targets, rather than being excluded with the machine construction.

The publication covers the integer hardness and upper-bound results. The detailed
[paper map](PAPER_1021_MAP.md) records the precise statements and external inputs.

The continuation from `sparse_irreducibility_complete_qrh.pdf` added 112 public theorems covering
conditional global-error aggregation, the explicit cutoff, witness counts, streaming, sparse
evaluations, and encoded-length bounds. The follow-up has now instantiated the discriminant,
exceptional-prime, and good-prime arguments for the actual irreducible factors and proved the
Proposition 4.1 average bound for the input polynomial, conditional only on a uniform external
prime-ideal estimate. Under the current agreement this cited analytic estimate is an allowed
explicit premise; importing or reproving it from the paper's QRH input is not required.
The continuation also connects the conditional
prime-counting threshold and its majority-witness form to arbitrary raw `ITerms` inputs, including
constant boundaries and a linear choice-bit bound in the input encoding.

`section3_uniform_arithmetic_conclusion` in `UpperBounds/Section3Arithmetic.lean` chooses one
integer constant before all inputs and proves the uniform counting/majority criteria and bit bound.
`section3_irreducibility_mem_PP_and_PSPACE` in `UpperBounds/Section3Conclusion.lean` gives the final
`IrredLang` membership conclusions for `Complexity.PP` and `Complexity.PSPACE`.
Following the user's request to formalize the actual Section 3.7 machine,
`primeCountingAlgorithmCertificate_of_binaryPrimalityInFP` now constructs the implementation
certificate. The concrete NTM, deterministic preprocessing, verifier, polynomial clock, and exact
acceptance probability are proved in `UpperBounds/Machine/`. The new final entry point is
`section3_irreducibility_mem_PP_and_PSPACE_of_external_theorems`: its only external premises are
the effective prime-ideal estimate and AKS binary primality in `FP`. It has no algorithm certificate
parameter. The subsequent Section 3 completion also proves the deterministic enumeration
implementation, including a direct whole-input PSPACE theorem and the post-preprocessing
trial-division core's linear decision-space bound. Remark 16 now supports every fixed positive
gap, and Proposition 13 supports real cutoffs. See
[the current detailed scope](PRIME_COUNTING_QRH.md).

A Chinese [Section 3 completion report](SECTION3_COMPLETION_2026-10-22.md) and
[paper-to-Lean correspondence](SECTION3_LEAN_MAP.md) record the completed results, remaining
premises, and the exact declarations for the paper's theorems and formulas.

The later `AI4Math_Irreducibility.pdf` has also been checked against the code (2026-10-19).
Its Theorem 2 has the same four conclusions. `SparseIrred/Irreducibility.lean` exposes its numbered
statements, including the literal rational-coprimality/reciprocal form of Theorem 4, the strict
positive-residue and uniqueness assertions of Lemma 5, and an explicit polynomial output-length
bound for Lemma 7. See [the detailed correspondence](IRREDUCIBILITY_AUDIT.md).

## Result

Theorem 8 of the notes (28 Sep 2026, §2.2, pp. 7–8) is formalized **unconditionally**, in
`SparseIrred/Theorem8.lean`:

```lean
theorem irreducibility_coNPHard : coNPHard IrredLang
theorem reducibility_NPHard : NPHard RedLang
theorem irreducibility_NPHard_oneQuery : ∀ L ∈ NP, OneQueryReducesPoly L IrredLang
theorem P_eq_NP_of_irreducibility_mem_P (h : IrredLang ∈ P) : P = NP
```

plus the robust forms `P_eq_NP_of_irreducibility_test` (any polynomial-time test that is correct on
canonical codes, arbitrary on non-codes) and `irreducibility_NPHard_oneQuery_of_codes` (the oracle
only has to be correct on canonical codes; the machine makes exactly one query). The four statements
are also proved along the notes' literal route with the Sawin–Shusterman–Stoll theorem as an
explicit hypothesis (`*_of_SSS`).

* `coNPHard`, `NPHard`, `P`, `NP`, `FP`, `≤ₚ` are complexitylib's (pinned `edd0e9ec`); the reduction
  is from complexitylib's `SAT.ThreeSAT.language` (exact-3 CNF), whose NP-hardness (Cook–Levin +
  Tseitin) is proved in complexitylib.
* `IrredLang`/`RedLang` are canonical binary-sparse codes of irreducible/reducible elements of
  `ℤ[X]` (mathlib `Irreducible`); non-codes are in neither language.
* `OneQueryReducesPoly` is defined on complexitylib's `OracleTM` with query counting over the whole
  run (`reachesInQ`), polynomial time bound, correctness for every oracle deciding the target.
* Core semantics: `Hfinal_irreducible_iff (Φ) (hΦ : Φ ≠ []) : Irreducible (Hfinal Φ) ↔ ¬Φ.Satisfiable`.

The build and audit results for the current integer-only publication are recorded in
[the release record](RELEASE_2026-10-27.md). `scripts/audit.sh` checks every retained
entry point and rejects unexpected axioms. Vendor hashes match the source snapshot.

Historical review: a 9-reviewer adversarial review with two skeptics per finding
found no mathematical or faithfulness defect. Confirmed findings (all minor after verification; two had
been filed as major) were documentation/hygiene items, the unpinned path dependency on the sibling
project (fixed by vendoring, 274947a) and the "promise" strengthening of (3)/(4) (added, 1a100e9).
A second development review found no regression; its minor
documentation findings were fixed.
Local review transcripts and session metadata are not required for proof checking and are not
included in the publication snapshot. The reproducible checks are the Lean build and audit scripts.

## Unfinished items

The original hardness theorem has no open proof obligation. The integer upper-bound continuation
retains the allowed analytic premise and, in the probabilistic and FP-step routes, the cited AKS
binary-primality theorem. The actual Section 3.7 machine and its implementation certificate are
proved from the AKS input. The actual Section 3.6 linear-space core uses verified trial division.
The previously listed Section 3.6 implementation, Remark 16 general-gap, and real-cutoff tasks
are now covered by `UpperBounds/Section3Complete.lean`.
Its current scope is described in
[PRIME_COUNTING_QRH.md](PRIME_COUNTING_QRH.md), while
[UPPER_BOUNDS_1021.md](UPPER_BOUNDS_1021.md) preserves the initial coverage audit.
Other items outside the original hardness proof:

1. The Sawin–Shusterman–Stoll large-gap theorem itself (`SSSLargeGap`). It is used only as the
   explicit hypothesis of the `*_of_SSS` variants that follow the notes literally. The unconditional
   theorems do not use it: for the polynomials `H_M` of Theorem 8 the needed irreducibility is proved
   directly (Filaseta–Ford–Konyagin argument specialized, `SparseIrred/FFK`).
2. Proposition 9 of the older notes is not Lemma 9 of the target 18-page manuscript. The later
   `UpperBounds/IntegerBoundary.lean` and input preprocessing cover the integer boundary cases
   used by the target manuscript; the old numbering is not an outstanding target-paper obligation.

Local-machine note: `.lake/packages` is a symlink to the sibling project's package cache (shared
mathlib oleans). The manifest is fully git-pinned.

## Deviations from the notes (all documented, none weakens a conclusion)

| Notes | Formalization | Why |
|---|---|---|
| 3-CNF with clauses of width at most three | source language is complexitylib's exact-3 `ThreeSAT.language` (`decode3?`); other strings (malformed, or a clause of length ≠ 3) go to the invalid-code branch (output `X`); the construction and the semantic theorems themselves hold for arbitrary CNFs | exact-3 SAT is NP-hard in complexitylib; no conclusion weakened |
| "Φ with n variables" | only occurring variables are numbered (`varIdx` = number of occurring variables below `v`), so `n ≤` input length | complexitylib variables are arbitrary naturals |
| Rosser–Schoenfeld for the size of `q_i` | `nth Prime k ≤ 64 (k+1)^2` (Chebyshev-type, proved) | enough for polynomial time |
| CRT for realizing assignments | mathlib `Nat.chineseRemainderOfFinset` (`exists_root_realizing`) | as in the notes |
| norm argument | `Algebra.norm` of `S(ζ)` in `ℚ(ζ) ⊂ ℂ`, integrality, product over embeddings `< 1` | as in the notes |
| satisfiable branch: nonconstant common divisor of `A, B` | explicit cyclotomic factor `Φ_k ∣ H_M` in `ℤ[X]`, `k ∣ N`, `0 < φ(k) ≤ N < M + N` | gives the factorization in `ℤ[X]` directly |
| unsatisfiable branch via SSS Thm 1.2 + 1.5 + Cor 1.3 | (a) literal route: `SSSLargeGap` hypothesis, all its hypotheses verified; (b) unconditional route: `IsRelPrime H (mirror H)` from the palindromic identity `X^{M+N-2D} H − mirror H = B (X^{2M+N-2D}+1)` + root-of-unity exclusion, Ljunggren condition via FFK Lemma 3 (Dirichlet, constants 8 boxes / `64^|S|`), no-carry `κ`-lift to `ℤ[X][Y]`, Eisenstein at `(X − 1)` instead of Capelli, mathlib `irreducible_of_mirror` | avoids Lehmer-type bounds (Voutier, MRW08) that cannot be formalized here |
| θ (Lehmer's constant) | quantified as any real root `> 1` of Lehmer's polynomial; uniqueness proved (`lehmerPoly_root_unique`); the bracket `117/100 < θ < 118/100` proved by IVT | no decimal approximation is assumed |
| input encoding | sign–magnitude binary coefficients, binary exponents (`Nat.bits`, LSB first), `delimit` framing, exponents increasing; `decodePoly` accepts exactly canonical codes | "canonical list", binary |

No mathematical error was found in the notes. Remarks on the sources: SSS quote Voutier's bound
without its hypothesis `d ≥ 2` (irrelevant for SSS and for this project); SSS's Theorem 1.5 agrees
with the Filaseta–Ford–Konyagin Corollary after substituting `f = c̃`, `g = d`, `n = N − deg c`
(`docs/history/survey/external.md`).

## Statement revisions after the freeze (commit ca9fc21)

All are strengthenings (hypotheses removed that were never used) or additions; recorded here as
required by the workflow:

| Commit | Declaration | Change |
|---|---|---|
| 1a100e9 | `Hfinal_irreducible_of_unsat`, `Hfinal_irreducible_iff` | dropped unused `numVars Φ ≠ 0` |
| 1a100e9 | `not_capellian` | dropped unused `Φ ≠ []` |
| 1a100e9 | `aeval_posLitPoly_eq_zero_iff` | dropped unused `ζ ^ N = 1`, `i < n` (ζ, i now explicit) |
| 1a100e9 | `P_eq_NP_of_irreducibility_test`, `irreducibility_NPHard_oneQuery_of_codes` | new (robust forms) |
| 18a0b2b | `exists_root_realizing` | new public lemma (CRT step, previously a local `have`) |
| 18a0b2b | `Occurs.le_maxVar`, `eval₂_invert` | private helpers made public (statements unchanged) |
| 18a0b2b | `eval₂_toLaurent_int` | new public lemma (Laurent evaluation of `toLaurent p` in any commutative ring) |
| 18a0b2b | `Machine.length_mul_Qmax_pow_six_le_rawBound` | new public lemma (size bound, previously duplicated inline) |

## Layout

See `docs/PAPER_MAP.md` (notes ↔ Lean), `docs/DEPENDENCIES.md` (dependency audit),
`docs/ENVIRONMENT.md` (versions, builds), `docs/FFK_BLUEPRINT.md` and `docs/FP_BLUEPRINT.md`
(proof designs), `docs/history/` (survey and design reports written during development).
