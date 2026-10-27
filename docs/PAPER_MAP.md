# Notes ↔ Lean correspondence (Theorem 8, notes of 28 Sep 2026, pp. 7–8)

For the later standalone `AI4Math_Irreducibility.pdf` (Theorem 2 and Lemmas/Theorem 3–7),
see [IRREDUCIBILITY_AUDIT.md](IRREDUCIBILITY_AUDIT.md) and `SparseIrred/Irreducibility.lean`.
For the 2026-10-21 Section 3 upper bound, including the verified Section 3.7 machine and the
final theorem with external analytic and AKS premises, see
[the Section 3 completion report](SECTION3_COMPLETION_2026-10-22.md).
[UPPER_BOUNDS_1021.md](UPPER_BOUNDS_1021.md) preserves the earlier coverage history.
The current publication covers integer irreducibility in Sections 2 and 3;
see [the manuscript correspondence](PAPER_1021_MAP.md).
The subsequent standalone prime-counting note and its new formalizations are mapped in
[PRIME_COUNTING_QRH.md](PRIME_COUNTING_QRH.md).

Status as of the final audit (`scripts/audit.sh` → `docs/AXIOMS.txt`, `docs/DEP_AUDIT.txt`):
every theorem row is **proved**, i.e. the declaration and its transitive dependencies use only
`propext`, `Classical.choice`, `Quot.sound` (no `sorryAx`, no project axioms). "definition" rows
are definitions (checked for faithfulness by review, see `docs/STATUS.md`).

| Notes | Lean declaration | File | Status |
|---|---|---|---|
| Input model: canonical binary-sparse list (coefficients and nonnegative exponents in binary) | `canonTerms`, `encPoly`, `decodePoly`, `decodePoly_eq_some_iff`, `encPoly_injective` | `Sparse/Canonical.lean` | proved |
| "irreducible as an element of ℤ[X]" | mathlib `Irreducible (f : ℤ[X])`, language `IrredLang` | `Sparse/Canonical.lean` | definition |
| "reducibility" | `Reducible f := f ≠ 0 ∧ ∃ g h, ¬IsUnit g ∧ ¬IsUnit h ∧ f = g*h`, `RedLang`, `reducible_iff`, `reducible_iff_not_irreducible` (positive degree only) | `Sparse/Canonical.lean` | proved |
| 3-CNF Φ, 3-SAT/3-UNSAT | complexitylib `SAT.CNF`, `ThreeSAT.language` (exact-3 clauses), `CNF.decode3?` | complexitylib | library |
| n variables, first n odd primes q_i, N, m_i | `numVars`, `varIdx` (renumbering of occurring variables), `oddPrime`, `bigN`, `mExp` | `Construction/Defs.lean` | definition |
| P⁺_i = X^{m_i} − 1, P⁻_i = Σ_{r<q_i} X^{r m_i}, C_j | `posLitPoly`, `negLitPoly`, `litPoly`, `clausePoly` | `Construction/Defs.lean` | definition |
| S = Σ_j C_j(X) C_j(X⁻¹) in the Laurent ring, D = max{\|e\| : [X^e]S ≠ 0} | `Spoly : ℤ[T;T⁻¹]`, `Dexp` (sup over the true support) | `Construction/Defs.lean` | definition |
| A = 3X^D S, B = X^N − 1, H_M = A + X^M B | `Apoly` (= `trunc (3 T^D S)`), `Bpoly`, `Hpoly` | `Construction/Defs.lean` | definition |
| S ≠ 0 because S(−1) = Σ C_j(−1)² > 0 | `evalS_neg_one`, `clausePoly_eval_neg_one_ne_zero`, `evalS_neg_one_pos`, `Spoly_ne_zero` | `Construction/Laurent.lean` | proved |
| S(X⁻¹) = S(X); coefficients at ±D agree and are nonzero | `invert_Spoly`, `Spoly_coeff_neg`, `Spoly_coeff_Dexp_ne_zero`, `Spoly_coeff_eq_zero_of_lt` | `Construction/Laurent.lean` | proved |
| A ∈ ℤ[X], A(0) ≠ 0 | `toLaurent_Apoly` (negative exponent elimination), `Apoly_coeff`, `Apoly_coeff_zero_ne_zero`, `natDegree_Apoly`, `reverse_Apoly`, `three_dvd_Apoly_coeff`, `aeval_Apoly` | `Construction/Laurent.lean` | proved |
| ① literal polynomials vanish iff z_i = 1 / z_i ≠ 1 | `aeval_posLitPoly_eq_zero_iff`, `aeval_negLitPoly_eq_zero_iff` | `Construction/RootsOfUnity.lean` | proved |
| S(ζ) = Σ_j \|C_j(ζ)\|² | `evalS_eq_sum_normSq` | `Construction/RootsOfUnity.lean` | proved |
| every assignment arises (CRT) | `exists_root_realizing` (CRT), `exists_root_of_satisfiable` | `Construction/RootsOfUnity.lean` | proved |
| (2) Φ sat ⟺ ∃ζ^N=1, S(ζ)=0 ⟺ gcd_{ℚ[X]}(A,B) ≠ 1 | `satisfiable_iff_exists_root`, `satisfiable_iff_exists_common_root`, `satisfiable_iff_not_isCoprime` | `Construction/RootsOfUnity.lean` | proved |
| ② norm argument: nonzero algebraic integer, all conjugates in [0,2/3], norm < 1 | `eq_zero_of_isIntegral_of_forall_norm_embedding_lt_one`, `evalS_eq_zero_of_rootOfUnity` | `Construction/Norm.lean` | proved |
| H_M has a root of unity (any order) iff Φ sat, for every M | `exists_rootOfUnity_root_iff`, `satisfiable_of_rootOfUnity_root` | `Construction/Norm.lean` | proved |
| unsat ⇒ no cyclotomic factor | `not_cyclotomic_dvd_Hpoly` | `Construction/Norm.lean` | proved |
| Sawin–Shusterman–Stoll Thm 1.2 + 1.5 + Cor 1.3 | `SSSLargeGap` (explicit hypothesis, never an axiom), `ffkBound`, `sssN1`, `Capellian`, `NoncyclotomicPartIrreducible`, `lehmerPoly` | `LargeGap/Statement.lean` | statement |
| ③ c = 1 − X^N, d = A, L = M + N, c̃ = B, X^L c(X⁻¹) + d = H_M | `reverse_cPoly`, `fL_eq_Hfinal` | `LargeGap/Verify.lean` | proved |
| c(0)d(0) ≠ 0, coprimality, c ≠ ±d, non-Capellian | `cPoly_coeff_zero`, `Apoly_coeff_zero_ne_zero`, `isRelPrime_reverse_cPoly_Apoly`, `cPoly_ne_Apoly`, `cPoly_ne_neg_Apoly`, `not_capellian` | `LargeGap/Verify.lean`, `Construction/Laurent.lean` (`Apoly_coeff_zero_ne_zero`) | proved |
| m, w, M = 2^{20(w+1)}(m+1)^6 exceeds L₀, L₁, deg A | `mParam`, `wParam`, `Mval`; `bound_lt_Mval_add`, `natDegree_Apoly_lt_Mval`; θ: `exists_lehmerPoly_root`, `lehmerPoly_root_unique` | `Construction/Defs.lean`, `LargeGap/Verify.lean` | proved |
| source theorem ⇒ noncyclotomic part of H_M irreducible | `noncyclotomicPartIrreducible_Hfinal` (uses `SSSLargeGap`) | `LargeGap/Verify.lean` | proved |
| (replacement of the source theorem, unconditional) FFK Lemma 3, κ-lift/no-carry, Eisenstein at (X−1), palindromic identity, Ljunggren | `FFK.exists_lift_modulus`, `FFK.kLift_mul_eq_of_mul_eq`, `FFK.irreducible_gapLift`, `FFK.palindromic_identity`, `FFK.isRelPrime_gapPoly_mirror`, `FFK.ljunggren_gapPoly`, `FFK.irreducible_gapPoly`, `FFK.irreducible_Hfinal` | `FFK/*.lean` | proved |
| ④ coefficient of X^M is −1, H_M primitive, deg H_M = M + N | `Hpoly_coeff_M`, `isPrimitive_Hpoly`, `natDegree_Hpoly`, `natDegree_Hfinal` | `Construction/Irreducible.lean` | proved |
| unsat ⇒ irreducible in ℤ[X] (Gauss) | `Hfinal_irreducible_of_SSS`; unconditionally `Hfinal_irreducible_of_unsat` | `Construction/Irreducible.lean`, `FFK/Main.lean` | proved |
| sat ⇒ nonconstant common divisor, proper factorization in ℤ[X] | `exists_cyclotomic_dvd_of_satisfiable`, `Hfinal_factorization_of_satisfiable`, `Hfinal_reducible_of_satisfiable` | `Construction/Irreducible.lean` | proved |
| Irreducible(H Φ) ⟺ ¬ Satisfiable Φ | `Hfinal_irreducible_iff_of_SSS`, `Hfinal_irreducible_iff` | `Construction/Irreducible.lean`, `FFK/Main.lean` | proved |
| n = 0 or s = 0: output X² − 1 / X; invalid codes | `reducePoly`, `reduce`; `irreducible_X_int`, `reducible_X_sq_sub_one`, `reduce_correct(_of_SSS)` | `Reduction/Defs.lean`, `Reduction/Correct.lean` | proved |
| polynomial sparse-bit cost | `reduce_mem_FP` (= `Machine.reduce_mem_FP_machine`: Cobham implementation `reduceStr`, `reduceStr_eq_reduce` on all bit strings, `CobhamFP_eq_FP`) | `Machine/ReduceFP.lean`, `Machine/Assemble.lean` | proved |
| q_i below a polynomial in n (the notes cite Rosser–Schoenfeld) | `Machine.nth_prime_le : nth Prime k ≤ 64 (k+1)^2`, `Machine.oddPrime_le`, trial-division primes `Machine.firstOddPrimes_eq` | `Machine/Primes.lean` | proved |
| each C_j has at most Q³ raw terms; S at most sQ⁶ raw terms | `Machine.length_clauseTermsD_le_cube`, `Machine.length_sRawD_le` | `Machine/Bounds.lean` | proved |
| exponents of S have absolute value < 3N; coefficients at most sQ⁶ | `Machine.offsetD_lt_three_mul_bigN`, `Machine.Dexp_lt_three_mul_bigN`, `Machine.natAbs_coeff_Spoly_le` | `Machine/Bounds.lean` | proved |
| w (numerical value) polynomial in the formula length | `Machine.twenty_mul_wD_succ_le`, `Machine.wParam_le_wBound : 20 (w+1) ≤ wBound \|x\|` | `Machine/Bounds.lean` | proved |
| the algorithm computes the notes' H_M | `Machine.canonTerms_Hfinal`, `Machine.canonTerms_reducePoly`, `Machine.reduce_eq_encITerms`, `Machine.wParam_eq`, `Machine.mParam_eq`, `Machine.Mval_eq` | `Machine/DataCorrect.lean` | proved |
| "A machine deciding 3-SAT may compute the same H_M, ask an irreducibility oracle once, and negate its answer" | `reachesInQ` (query counting), `OneQueryReducesPoly`, `exists_negQuery_machine`, `oneQueryReducesPoly_of_neg` | `Oracle/OneQuery.lean` | proved |
| robust forms: test / oracle correct only on canonical codes | `P_eq_NP_of_irreducibility_test`, `irreducibility_NPHard_oneQuery_of_codes` | `Theorem8.lean` | proved |
| Theorem 8 (four conclusions) | `irreducibility_coNPHard`, `reducibility_NPHard`, `irreducibility_NPHard_oneQuery`, `P_eq_NP_of_irreducibility_mem_P` (+ `_of_SSS` forms) | `Theorem8.lean` | proved |
