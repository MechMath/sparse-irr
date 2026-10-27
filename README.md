# Sparse integer polynomial irreducibility in Lean 4

[中文说明](README.zh-CN.md) · [Paper correspondence](docs/PAPER_1021_MAP.md) ·
[Dependencies and assumptions](docs/DEPENDENCIES.md)

This repository publishes the **integer irreducibility results in Sections 2
and 3** of the non-standalone manuscript `1021-AI4Math_Irreducibility.pdf`:
unconditional complexity hardness, and the integer `PP`/`PSPACE` upper bounds
under explicitly stated literature inputs. The supporting algebra, sparse
binary programs and integer machine proofs are included.

## Main results

| Manuscript | Lean entry point | Assumptions |
|---|---|---|
| Integer hardness (Theorems 2 and 4) | `SparseIrred.Irreducibility.irreducibility_hardness` | No additional mathematical hypotheses. |
| Integer `PP` and `PSPACE` (Theorems 2 and 10) | `SparseIrred.UpperBounds.section3_irreducibility_mem_PP_and_PSPACE_of_external_theorems` | Effective prime-ideal counting and binary AKS primality in `FP`. |
| Every fixed positive gap (Remark 16) | `SparseIrred.UpperBounds.GeneralGap.section3_irreducibility_mem_PP_and_PSPACE_of_positive_gap` | Corresponding counting estimate and AKS. |
| Deterministic streaming | `SparseIrred.UpperBounds.Machine.section3_deterministic_streaming_mem_PSPACE` | The stated analytic and AKS inputs. |
| Linear-space trial-division core | `SparseIrred.UpperBounds.Machine.section3_linear_streaming_core` | The analytic input and specified preprocessed configuration; no AKS. |

The hardness theorem distinguishes many-one coNP-hardness of irreducibility,
many-one NP-hardness of reducibility, and one-query Turing NP-hardness of
irreducibility. The specialized Filaseta–Ford–Konyagin proof is internal;
`SSSLargeGap` appears only in older `_of_SSS` compatibility theorems.

```lean
import SparseIrred

#check SparseIrred.Irreducibility.irreducibility_hardness
#check SparseIrred.UpperBounds.section3_irreducibility_mem_PP_and_PSPACE_of_external_theorems
#check SparseIrred.UpperBounds.GeneralGap.section3_irreducibility_mem_PP_and_PSPACE_of_positive_gap
```

## Build and verify

Install [elan](https://github.com/leanprover/elan), Git, Bash, Python 3 and
ripgrep (`rg`). The Lean toolchain and dependency revisions are pinned.
Do not run `lake update` when reproducing this snapshot.

```sh
git clone https://github.com/MechMath/sparse-irr.git
cd sparse-irr
lake exe cache get
lake build
scripts/audit.sh
scripts/check_vendor.sh
```

The toolchain is **Lean `v4.34.0-rc2`**; `complexitylib` is pinned at
`edd0e9ec3d7d2eb00afa978338e8585a4eab8152`. All transitive versions are in
[`lake-manifest.json`](lake-manifest.json). No sibling repository, local cache
symlink or paper PDF is required. The 38 vendored modules have a source-verified
SHA-256 manifest and can be checked without their original checkout.

The audit fails on build errors, forbidden proof placeholders, missing audit
roots, nonstandard axioms and vendor corruption. Results for this source scope
are in [the release record](docs/RELEASE_2026-10-27.md),
[AXIOMS.txt](docs/AXIOMS.txt) and [DEP_AUDIT.txt](docs/DEP_AUDIT.txt).

## External inputs and exact scope

The integer upper bound receives the effective counting conclusion as
`EffectivePrimeIdealEstimate` (with a real-cutoff counterpart). In the target
manuscript, §3.1 cites **[6] Cureton–Thorner** for the uniform zero-free input
and **[9] Frei–Sofos–Widmer, Theorem 1.1** for the counting estimate. The
external zero-free repository **[2]** is not imported. **[1]
Agrawal–Kayal–Saxena, “PRIMES is in P”** supplies `BinaryPrimalityInFP` in §3.7.
The discriminant bounds, good-prime correspondence, input-polynomial average,
cutoff, threshold and final complexity conclusions are then proved internally.

The probabilistic construction is connected to an actual machine, its exact
acceptance probability, and a polynomial bound on all paths. `PP` means strict
majority; it is not `BPP` or a bounded-error guarantee. The deterministic
whole-input PSPACE route uses AKS. The separate no-AKS linear-space core begins
at the specified preprocessed configuration; an end-to-end raw-input
linear-space preprocessing theorem is not claimed.

The checked dependency closure uses only Lean's `propext`, `Classical.choice`
and `Quot.sound`; there are no project axioms or `sorry` proofs. This audit does
not prove the explicit literature parameters. Example 1 and background prose
are not separately claimed as formalized declarations.

## Code and documentation

- [`SparseIrred/Irreducibility.lean`](SparseIrred/Irreducibility.lean): hardness interfaces.
- `Construction/`, `FFK/`, `Reduction/`, `Machine/`, `Oracle/` under `SparseIrred/`: algebra and actual reduction machinery.
- [`SparseIrred/UpperBounds/Section3Complete.lean`](SparseIrred/UpperBounds/Section3Complete.lean): integer upper-bound completion.
- [Paper map](docs/PAPER_1021_MAP.md), [Section 3 report](docs/SECTION3_COMPLETION_2026-10-22.md), and [detailed term map](docs/SECTION3_LEAN_MAP.md).
- [`Vendor/README.md`](Vendor/README.md): source provenance; [`scripts/`](scripts/): reproducible checks.

Older reports retain their dates and original theorem numbering. Use the paper
map for the numbering in the non-standalone manuscript.

## Licensing

No project-wide license has been specified in this snapshot. This README adds
no license grant. Vendored provenance is documented separately, and fetched
dependencies retain their own licenses.
