# Sparse polynomial irreducibility in Lean 4

[中文说明](README.zh-CN.md) · [Whole-paper map](docs/PAPER_1021_MAP.md) ·
[Dependencies and assumptions](docs/DEPENDENCIES.md)

This repository contains the Lean formalization associated with the **18-page,
non-standalone manuscript `1021-AI4Math_Irreducibility.pdf`**. It includes the
integer hardness proof, the integer upper bounds, and the uniform finite-field
upper bound, together with the implemented machines described below.

The numbered theorems, lemmas, proposition, corollary and Remark 16 have formal
counterparts. This is not a claim that every sentence or illustrative example
has a Lean declaration: Example 1's factorization-output-size discussion is not
separately formalized. Earlier notes and the seven-page manuscript use different
numbering; use the [18-page correspondence](docs/PAPER_1021_MAP.md).

## Main results

| Manuscript | Lean entry point | Assumptions |
|---|---|---|
| Theorems 2 and 4: integer irreducibility is many-one coNP-hard; reducibility is many-one NP-hard; one-query Turing NP-hardness | `SparseIrred.Irreducibility.irreducibility_hardness` | None beyond the formal definitions. |
| Theorems 2 and 10: integer irreducibility is in `PP` and `PSPACE` | `SparseIrred.UpperBounds.section3_irreducibility_mem_PP_and_PSPACE_of_external_theorems` | The explicitly stated effective prime-ideal counting estimate and binary AKS primality in `FP`. |
| Remark 16: any fixed positive zero-free gap | `SparseIrred.UpperBounds.GeneralGap.section3_irreducibility_mem_PP_and_PSPACE_of_positive_gap` | The corresponding counting estimate and AKS. |
| Theorems 3 and 18: uniform finite-field irreducibility is in `PSPACE` | `SparseIrred.UpperBounds.Section4.section4_irreducibility_mem_PSPACE_unconditional` | **No mathematical or implementation parameters.** |
| Complete finite-field decision machine | `SparseIrred.UpperBounds.Section4.section4_complete_machine` | **No mathematical or implementation parameters.** |
| Lemma 17: a space-bounded entry machine yields a determinant machine | `SparseIrred.UpperBounds.Section4.lemma17_uniform_scalar_machine` | The given entry machine's correctness, termination and stated configuration-space contract. |

The unconditional hardness proof uses the specialized Filaseta–Ford–Konyagin
route in the target manuscript. The general `SSSLargeGap` proposition is only
an assumption of older, explicitly suffixed `_of_SSS` compatibility theorems.

Import all formalization modules with:

```lean
import SparseIrred

#check SparseIrred.Irreducibility.irreducibility_hardness
#check SparseIrred.UpperBounds.section3_irreducibility_mem_PP_and_PSPACE_of_external_theorems
#check SparseIrred.UpperBounds.Section4.section4_irreducibility_mem_PSPACE_unconditional
#check SparseIrred.UpperBounds.Section4.section4_complete_machine
#check SparseIrred.UpperBounds.Section4.lemma17_uniform_scalar_machine
```

## Build and verify

Install [elan](https://github.com/leanprover/elan) and Git. Bash, Python 3 and
ripgrep (`rg`) are also needed for the audit scripts. The toolchain and every
dependency revision are pinned; do not run `lake update` for this snapshot.

```sh
git clone https://github.com/MechMath/sparse-irr.git
cd sparse-irr
lake exe cache get
lake build
scripts/audit.sh
```

The toolchain is **Lean `v4.34.0-rc2`**. `complexitylib` is pinned at
`edd0e9ec3d7d2eb00afa978338e8585a4eab8152`; transitive revisions are recorded in
[`lake-manifest.json`](lake-manifest.json). A fresh build downloads these
dependencies. No sibling checkout, local cache symlink, or paper PDF is required.

Additional checks:

```sh
lake env lean scripts/Section4Smoke.lean
scripts/check_vendor.sh
git diff --check
```

The smoke program prints seven results, expected in order:
`true, false, true, false, true, false, false` (each wrapped as `some [bit]`).
These are executable examples, not a replacement for the proved machine theorems.
`scripts/audit.sh` fails on a failed build, forbidden source tokens, missing
dependency-audit declarations, unexpected axioms, or vendor checksum mismatches.

The checked proof dependency closure uses only `propext`, `Classical.choice`
and `Quot.sound`. There are no project axioms or `sorry` declarations. This
axiom check does **not** discharge the explicit literature hypotheses of the
integer upper-bound theorem. See the [release verification record](docs/RELEASE_2026-10-27.md).

## Scope and trust boundary

- **Section 3 literature inputs.** `EffectivePrimeIdealEstimate` records the
  effective counting conclusion after the zero-free input. In the target
  manuscript this is §3.1, references **[6] Cureton–Thorner** and **[9]
  Frei–Sofos–Widmer, Theorem 1.1**. **[2]** is the referenced public zero-free
  formalization; it is not imported here. `BinaryPrimalityInFP` is **[1]
  Agrawal–Kayal–Saxena, “PRIMES is in P”**, used in §3.7. All subsequent
  input-polynomial estimates and conclusions are proved internally.
- **Section 3 machines.** The probabilistic machine and the direct whole-input
  deterministic `PSPACE` route are proved using the stated inputs. The separate
  trial-division core has an affine space bound from its specified preprocessed
  configuration, without AKS. It is not advertised as an end-to-end linear-space
  machine starting from arbitrary raw input. `PP` means strict-majority
  acceptance, not `BPP` or a fixed bounded-error guarantee.
- **Section 4.** Binary field arithmetic, sparse queries, Berkowitz/Frobenius
  instructions, stacks, validation and machine compilation are implemented and
  proved. The finite field is represented by a prime and a dense monic
  irreducible modulus; characteristic and extension degree are input data.
  The final language rejects invalid strings and validates the field header.
- **Lemma 17.** The given entry TM satisfies `WithinDecisionSpace`, including
  the output-head bound. The determinant compiler returns the full field-element
  code and proves the bound at every reachable configuration. No conversion
  from arbitrary auxiliary-space-only transducer witnesses is asserted. The
  lemma's valid-input domain is separate from Theorem 18's total input validation.

## Navigate the code

| Path | Contents |
|---|---|
| [`SparseIrred/Irreducibility.lean`](SparseIrred/Irreducibility.lean) | Hardness and numbered algebraic interfaces; older docstrings use seven-page numbering. |
| `SparseIrred/Construction/`, `FFK/`, `Reduction/`, `Machine/`, `Oracle/` | SAT encoding, gap argument, reduction and one-query machinery. |
| [`SparseIrred/UpperBounds/Section3Complete.lean`](SparseIrred/UpperBounds/Section3Complete.lean) | Section 3 completion entry point. |
| [`SparseIrred/UpperBounds/Section4Complete.lean`](SparseIrred/UpperBounds/Section4Complete.lean) | Section 4 mathematics, binary implementations and compiled machines. |
| [`Vendor/`](Vendor/README.md) | 38 source-verified arithmetic/encoding modules; hashes in `Vendor/SHA256SUMS`. |
| [`scripts/`](scripts/) | Build, axiom/dependency, vendor and executable-example checks. |
| [`docs/PAPER_1021_MAP.md`](docs/PAPER_1021_MAP.md) | Full numbering map and detailed section reports. |

Historical progress reports are retained as snapshots, with their scope and
dates stated. Current claims are summarized above and in the whole-paper map.
Local paper drafts, session state, caches and build products are not needed for
the published source package.

## Licensing

No project-wide license has been specified in this source snapshot. This README
does not add a license grant. Vendored-source provenance is documented in
[`Vendor/README.md`](Vendor/README.md); fetched dependencies retain their own licenses.
