# Environment, pinned versions and baseline build

Recorded 2026-09-29.

This page preserves the earlier environment history. The current whole-paper release
and new audit run are described in [RELEASE_2026-10-27.md](RELEASE_2026-10-27.md).
Use the commands in the root README for a new clone; local paths below are historical only.

| Component | Version |
| --- | --- |
| Lean toolchain | `leanprover/lean4:v4.34.0-rc2` (commit 6a10ac8c22be), Lake 5.0.0-src+6a10ac8 |
| complexitylib | `edd0e9ec3d7d2eb00afa978338e8585a4eab8152` (2026-09-05) — pinned in `lakefile.toml` |
| mathlib | `e06eff5f95374108acfaf19f1ff7473aa7771df2` (inherited from complexitylib) |
| cslib | `d9be64196bf145edd019f1ccfeaee0c11166ba6b` (inherited) |
| batteries / aesop / Qq / plausible / importGraph / proofwidgets / LeanSearchClient / Cli | revs as in `lake-manifest.json` (inherited) |
| vendored modules | 38 modules of the local project SparseDivComplexity (libraries `SparseDivComplexity`, `SparseGcd`) copied verbatim from commit `c76c0d4575171bf8131f7487649e565d40530f6e` into `Vendor/` (`Vendor/README.md`, `scripts/check_vendor.sh`) |

Why this complexitylib commit: it is the commit already pinned by the sibling projects on this
machine (so mathlib oleans and the Cobham toolkit built on it can be shared). It contains every
reference entry point named in the task (`SAT.ThreeSAT.language`, `NPHard_language`,
`NPComplete_language`, `MapReducesPoly`, `NPHard.of_reduction`, `MapReducesPoly.mem_P`,
`NPHard.P_eq_NP_of_mem_P`, `coNPHard`, `MapReducesPoly.compl`, `NPComplete.compl`,
`coNPHard.of_reduction`, `CobhamFP_eq_FP`, `OracleTM.DecidesInTime`). The newest upstream `dev`
(`4673106a`, Lean v4.35.0-rc3) was checked: its oracle layer adds no query counting or Turing
reductions either, so moving to it would bring no benefit for this task.

On this machine `.lake/packages` is a local symlink to `../SparseDivComplexity/.lake/packages`
(identical revisions, shared mathlib oleans); it is git-ignored and not part of the project. A fresh
clone resolves the packages from `lake-manifest.json` (all git-pinned) with
`lake exe cache get && lake build`. Never run `lake update`; dependency checkouts are never edited.

History: the first version used a path dependency on `../SparseDivComplexity`; it was replaced by the
vendored copy (commit 274947a) so that the build depends only on pinned git revisions.

## Baseline build

A smoke-test module (`SparseIrred/Wiring.lean`, removed after the statement layer existed; it only
contained `#check`s of the reference entry points) importing ThreeSAT completeness, NP/coNP
reductions, Cobham, the oracle TM model, SparseDivComplexity string arithmetic and the needed mathlib
files: **success, 9017 jobs, 71 s wall clock** (complexitylib SAT/Tseitin modules built for the first
time; mathlib from the shared cache).

Final build: `lake build` **success, 9097 jobs** (vendored modules included, about 1.5 min from a
warm mathlib cache).

Fresh-clone check (2026-09-29, commit 18a0b2b; later commits change only docstrings/docs):
`git clone` into an empty directory with its own `.lake/packages`, then `lake exe cache get`
(all packages fetched from GitHub at the manifest revisions, 8789 mathlib cache files) and
`LEAN_NUM_THREADS=6 lake build`: **success, 9097 jobs, 8 min 32 s wall clock**;
`lake env lean scripts/Axioms.lean` there printed `[propext, Classical.choice, Quot.sound]` for all
22 audited declarations.

## Commands

```
export PATH=$HOME/.elan/bin:$PATH
cd /home/njw/lean4/complexity/SparseIrredHardness
lake build                       # full build
lake env lean SparseIrred/X.lean # single-file check
```
