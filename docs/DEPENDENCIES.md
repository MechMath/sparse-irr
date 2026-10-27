# Dependency audit (hardness and upper-bound ingredients)

Machine-checked results including the original Section 3 and complete Section 4 machines,
2026-10-23 (reproduce with
`scripts/audit.sh` and `lake env lean scripts/DepAudit.lean`):

* `lake build` succeeds (9468 jobs); no `sorry`, `admit`, `axiom` declaration, `native_decide`,
  `implemented_by`, `extern` or `unsafe` anywhere in `SparseIrred/`.
* `#print axioms` of all 479 audited declarations, including the Theorem 8 entry points,
  their `_of_SSS` variants, the statements in `Irreducibility.lean`, and 448 theorem entry points
  in `UpperBounds/`, reaches only subsets of `[propext, Classical.choice, Quot.sound]`
  (`docs/AXIOMS.txt`).
* **Transitive closure** (`docs/DEP_AUDIT.txt`): 463 roots (the previous 15 entry points and
  448 upper-bound entry points) reach 84,756 constants (Mathlib 61,433;
  Init 7,921; complexitylib 8,534; this project 5,880; vendored SparseDivComplexity 545 and SparseGcd
  230; Batteries 211; Std 1; Aesop 1). The only axioms reached are `propext`, `Quot.sound` and
  `Classical.choice`. The closure contains complexitylib's own proofs of Cook–Levin, Tseitin,
  3SAT NP-hardness (`ThreeSAT.NPHard_language`), the Cobham characterization of FP and the TM model, so none of these is
  assumed.

## 1. Existing Lean results actually used (not re-proved here)

| Source | Results |
|---|---|
| complexitylib `edd0e9ec` | `SAT.ThreeSAT.language`, `CNF.decode3?`/`decode3?_eq_some_iff`/`mem_language_iff_decode3`, `ThreeSAT.NPHard_language` (Cook–Levin + Tseitin inside), `MapReducesPoly`, `NPHard.of_reduction`, `NPHard.compl`, `coNPHard.of_reduction`, `NPHard.P_eq_NP_of_mem_P`, `P_compl`, `mem_FP_comp`, `CobhamFP_eq_FP` and the Cobham toolkit (`Cobham.iterFn`, block/flag string operations), TM model (`TM`, `ComputesInTime`, `Tape.HasOutput`, run lemmas, `retargetOutput`-style lemmas, `Tape.HasBinarySuffix`), oracle model `OracleTM`, `OracleTM.step`, `step_query_true/false`, `BooleanOracle.Decides` |
| complexitylib `edd0e9ec`, integer upper-bound conclusion | Actual NTM semantics, deterministic-to-nondeterministic machine composition, `PPTIME`/`PP` definitions and the proved containment `PP_subset_PSPACE`. This project constructs the Section 3 machine and proves its polynomial running time and exact finite-witness acceptance fraction. |
| SparseDivComplexity `c76c0d4` (sibling project; 38 modules vendored verbatim in `Vendor/`) | sparse integer term lists `ITerms`, `toPolyZ`, `NormalizedZ`, `normalizeZ`; bit-string encodings `encNat`, `encInt`, `encITerm`, `encITerms`, `decITerms`, `decITerms_encITerms`; Cobham string arithmetic (`addBits`, `subBits`, `mulBits`, `divBits`, `ltBits`, `canonBits`, `normalizeZStr`, `mapBlocks`/`foldBlocks`) with FP/Cobham lemmas; SparseGcd `parseCnfStr` (CNF parsing in FP), `TermsStr`/`ArithStr` helpers |
| mathlib `e06eff5f` | `Irreducible`, `Polynomial`, `LaurentPolynomial` (`trunc`, `invert`, `eval₂`), cyclotomic polynomials and `cyclotomic_eq_minpoly_rat`, `IsPrimitiveRoot`, `Algebra.norm`, `Algebra.norm_eq_prod_embeddings`, `Algebra.isIntegral_norm`, `IsIntegrallyClosed`, number fields/`IntermediateField.adjoin`, Gauss's lemma `IsPrimitive.Int.irreducible_iff_irreducible_map_cast`, `isCoprime_iff_aeval_ne_zero_of_isAlgClosed`, `Nat.chineseRemainderOfFinset`, `Nat.nth` primes, `Chebyshev.two_pow_le_mul_lcmUpto`, Ljunggren's `Polynomial.irreducible_of_mirror`, `Polynomial.mirror`, Eisenstein criterion, `RatFunc`, real `log`/`exp` bounds, intermediate value theorem |
| mathlib `e06eff5f`, upper-bound ingredients | normalized irreducible factors with multiplicities; finite-field Frobenius algebra homomorphisms; `AdjoinRoot` power bases; separability and resultants; rank-nullity and rank normal form; adjugates; Bird's division-free determinant correctness (`Matrix/Determinant/Bird/Correctness.lean`) |

## 2. Proved in this project

The original modules in `SparseIrred/` prove the construction and steps ①–④ (`Construction/*`), the
verification of every hypothesis of the large-gap theorem and of the bound on `M`
(`LargeGap/Verify.lean`), the unconditional irreducibility of `H_M` in the unsatisfiable case
(`FFK/*`: Filaseta–Ford–Konyagin Lemma 3 (Dirichlet), the no-carry lifting to `ℤ[X][Y]`,
Eisenstein at `(X − 1)`, the palindromic identity), the sparse encoding (`Sparse/Canonical.lean`),
the reduction and its correctness (`Reduction/*`), `reduce ∈ FP` with an explicit Cobham
implementation and all size bounds (`Machine/*`, including the explicit bound
`nth Prime k ≤ 64 (k+1)^2` used instead of Rosser–Schoenfeld), query counting and the one-query
oracle machine (`Oracle/OneQuery.lean`), the Theorem 8 entry points (`Theorem8.lean`), and the
standalone irreducibility paper's statements (`Irreducibility.lean`, see `docs/IRREDUCIBILITY_AUDIT.md`).

`UpperBounds/` adds the local root-count identities, factor statistic, numerical cutoff bounds,
majority count, finite-field Frobenius/minor criterion, and a determinant entry oracle using a
linearized Bird transition. See [the coverage history](UPPER_BOUNDS_1021.md).
The independent prime-counting continuation adds global-error and cutoff inequalities, concrete
witness counts, streaming/sparse-evaluation correctness, Mahler bounds, and bit bounds for original
unnormalized input lists. `section3_uniform_arithmetic_conclusion` in `Section3Arithmetic.lean`
collects the uniform arithmetic conclusion. `UpperBounds/Machine/` implements canonical input
validation, arithmetic preprocessing, modular evaluation and derivative evaluation, the eight-mode
verifier, concrete random-bit parsing, padding, fixed-length guessing, and deterministic machine
composition. It proves the verifier is in `FP`, the NTM runs in polynomial time on all paths,
and its acceptance probability is exactly `primeCountingAcceptance`.
`section3_irreducibility_mem_PP_and_PSPACE_of_external_theorems` in `Machine/Conclusion.lean`
derives the final integer `PP` and `PSPACE` language conclusions from the analytic estimate and
binary primality in `FP`. The older certificate-parameter theorem in `Section3Conclusion.lean`
remains a compatibility interface. The exact scope is recorded in
[PRIME_COUNTING_QRH.md](PRIME_COUNTING_QRH.md).

## 3. External results not formalized

| Result | Where it appears | Status |
|---|---|---|
| Sawin–Shusterman–Stoll, Theorems 1.2 + 1.5 and Corollary 1.3 (large-gap irreducibility, with its inputs Schinzel / Filaseta–Ford–Konyagin in general, Voutier, Mossinghoff–Rhin–Wu) | `SSSLargeGap` in `LargeGap/Statement.lean` | **Not formalized.** It is an explicit hypothesis of the `_of_SSS` theorems only (the notes' literal route). The unconditional Theorem 8 does **not** depend on it: for the polynomials `H_M` the needed irreducibility is proved directly (FFK specialization + Ljunggren), and the reciprocal-factor part of Corollary 1.3 (Lehmer-type bounds) is unnecessary because `IsRelPrime H_M (mirror H_M)` follows from the palindromic identity. |
| Rosser–Schoenfeld `p_k < k(log k + log log k)` | notes p. 7 (prime size) | Not used; replaced by the formalized bound `nth Prime k ≤ 64(k+1)^2` (`Machine/Primes.lean`), which suffices for polynomial time. |
| Capelli's theorem | FFK Corollary | Not used; replaced by Eisenstein at `(X − 1)` for the relevant bivariate polynomial. |
| Dedekind zeta zero-free region and the uniform effective prime-ideal estimate | 2026-10-21 PDF §3.1; `ExternalPrimeIdealEstimate.lean` | Allowed explicit literature premise under the user's 2026-10-22 agreement. The effective estimate is assumed with an existential positive real constant; the project proves the choice of one integer constant uniform over all inputs. The actual-factor discriminant bound, good-prime correspondence, Proposition 4.1 average bound and final arithmetic criterion are derived, not assumed. Reproving or importing the cited analytic theorems is not required. |
| Agrawal–Kayal–Saxena, *PRIMES is in P* (2004) | Original PDF §3.7 reference [1]; independent PDF §7 reference [5]; `BinaryPrimalityInFP` in `UpperBounds/Machine/WitnessFP.lean` | Explicit literature premise: the binary primality flag `fun s => [decide (decNat s).Prime]` belongs to `FP`. The surrounding verifier, random-bit encoding, NTM construction, running-time bound and acceptance-probability proof are implemented and proved in this project. |

## 4. Explicit premises and the implemented Section 3 machine

The agreed policy is project-wide: cited external theorems may be explicit hypotheses; the target
paper's internal mathematical deductions must be proved; algorithm implementation may be omitted;
final conclusions must still be Lean theorems. An external premise is a theorem parameter, not a
new global Lean axiom. Following the user's request to formalize the actual machine, the §3.7
implementation has now also been constructed and verified.

None of the unconditional hardness conclusions assumes a gap theorem or a polynomial-time
implementation. Only the `_of_SSS` variants assume the external large-gap theorem (kept deliberately,
to record that the notes' literal route is also checked apart from that theorem itself).
The standalone algebraic criteria retain their stated mathematical hypotheses. The new
`integer_irreducible_iff_root_threshold_of_approximation` explicitly requires the quarter-unit
analytic approximation; it proves the arithmetic consequence of that estimate. It is not an
unconditional upper-bound theorem. The later `integer_irreducible_iff_primeCounting_threshold`
derives that approximation from explicit prime-counting and global-average estimates, which
remain explicit inputs to that intermediate theorem. The combined
`integer_irreducible_iff_primeCounting_threshold_of_uniform_estimate` derives both from one uniform
external prime-ideal estimate. The global-average estimate is Proposition 4.1 of the target paper
and is now derived for the actual input polynomial from that estimate and the formalized
number-field argument. Its external analytic input is allowed to remain a literature premise.

`PrimeCountingAlgorithmCertificate C₀` records a polynomial-time NTM realizing
`primeCountingAcceptance C₀ x`, the rational acceptance fraction of the actual finite majority
witnesses on the canonical sparse input encoding, including signed-prime constants and the
primitive-input filter. It does not assert `Irreducible`, `IrredLang` correctness or membership
in `PP`/`PSPACE`; those follow from the mathematical criterion and the verified machine.
`primeCountingAlgorithmCertificate_of_binaryPrimalityInFP` now constructs this certificate from
the AKS premise. The certificate remains an explicit parameter of older compatibility theorems,
but is no longer an additional assumption of the final entry point
`section3_irreducibility_mem_PP_and_PSPACE_of_external_theorems`. That theorem has only the two
literature inputs: the effective prime-ideal estimate with a positive real constant, and
`BinaryPrimalityInFP`.

The constructed probabilistic machine implements original §3.7. The new §3.6 implementation
has a direct deterministic whole-input PSPACE proof via bounded-state iteration; that FP-step
route uses the AKS premise. A separate actual trial-division core has a linear all-prefix
decision-space contract from its specified preprocessed register configuration, without AKS.
Its parsers, sparse ordinary/derivative evaluation, two counting loops and threshold output
are internally proved. Remark 16's arbitrary fixed positive gap and real-cutoff Proposition 13
are also proved. See [the exact interfaces](SECTION3_COMPLETION_2026-10-22.md).
The audits certify these conditional theorems and constructed implementations, not the explicitly
parameterized external analytic and AKS literature inputs.

## Original Section 4

`Section4.section4_irreducibility_mem_PSPACE` has no additional external mathematical theorem
parameters. The Berkowitz, Frobenius, CRT factor-count and rank/minor deductions are proved
internally. A field header is verified by trial division and the same polynomial irreducibility
test over the prime field; neither primality nor header irreducibility is an oracle premise.

The older conditional theorem retains `Section4.UniformLocalStepRealization G` for compatibility.
The 2026-10-23 implementation proves `section4BinaryStep_realization`, supplying that interface
from the concrete binary program. The final `section4_irreducibility_mem_PSPACE_unconditional`
and `section4_complete_machine` therefore have no mathematical or implementation parameters.
Finite-field arithmetic, input validation, coefficient queries, address dispatch and stack
operations all have internal uniform Cobham/FP and simulation proofs. See
[the complete machine certification](SECTION4_MACHINE_CERTIFICATION_2026-10-23.md).

The generic `lemma17_uniform_scalar_machine` retains only `MatrixEntryMachine M A space`,
the actual entry machine's output/termination and `WithinDecisionSpace` contract. Its controller,
field operations, dispatch, simulation and complete scalar-output epilogue are instantiated
internally. The contract includes an output-head window; no equivalence with every weaker
auxiliary-space-only transducer contract is asserted.
