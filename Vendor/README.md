# Vendored modules

Verbatim copies (no edits) of the 38 modules listed in `MODULES.txt`, taken with
`git show c76c0d4575171bf8131f7487649e565d40530f6e:<path>` from the local project
`/home/njw/lean4/complexity/SparseDivComplexity` (libraries `SparseDivComplexity` and `SparseGcd`,
same author/owner as this project). They provide the Cobham-algebra string arithmetic, sparse
integer term lists (`ITerms`, `encITerms`, `decITerms`, `normalizeZStr`) and CNF parsing
(`parseCnfStr`) reused by `SparseIrred/Sparse` and `SparseIrred/Machine`. Module names are kept so
that proofs are unchanged; they depend only on complexitylib `edd0e9ec` and its mathlib.
`Vendor/SHA256SUMS` records hashes checked against that original Git commit.
Run `scripts/check_vendor.sh` to verify this snapshot without a sibling checkout.
For an additional comparison against the original repository, run
`scripts/check_vendor.sh /path/to/SparseDivComplexity`.

No license grant is added by vendoring these files; no license file was present in
the source snapshot. The separately fetched dependencies retain their own licenses.
