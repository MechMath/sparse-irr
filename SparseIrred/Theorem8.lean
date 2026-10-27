import SparseIrred.Reduction.Correct
import SparseIrred.Machine.ReduceFP
import SparseIrred.Oracle.OneQuery
import Complexitylib.SAT.ThreeSAT.Completeness
import Complexitylib.Classes.NP.CoNP
import Complexitylib.Classes.Containments

/-!
# Theorem 8 (notes of 28 Sep 2026, §2.2 "Integer irreducibility (7.1)", pp. 7–8)

"For binary-sparse input, irreducibility in `ℤ[X]` is coNP-hard under polynomial-time many-one
reductions, and reducibility is NP-hard under such reductions.  Irreducibility is also NP-hard
under polynomial-time one-query Turing reductions.  Hence a polynomial-time irreducibility test
implies `P = NP`."

Languages (`SparseIrred/Sparse/Canonical.lean`): `IrredLang` / `RedLang` are the canonical
binary-sparse codes (binary coefficients and exponents) of irreducible / reducible elements of
`ℤ[X]`; non-codes belong to neither.  Complexity notions are complexitylib's (`FP`, `P`, `NP`,
`MapReducesPoly` = `≤ₚ`, `NPHard`, `coNPHard`, `OracleTM`); the one-query Turing reduction
`OneQueryReducesPoly` is defined in `SparseIrred/Oracle/OneQuery.lean` on top of `OracleTM`.

Nothing here claims that `IrredLang` is NP-hard under many-one reductions, nor any membership of
the languages in NP or coNP.

Each statement is given twice: the `_of_SSS` form follows the notes literally and takes the
Sawin–Shusterman–Stoll large-gap theorem as an explicit hypothesis; the plain form is
unconditional (the large-gap input is replaced, for these polynomials, by the formalized argument
in `SparseIrred/FFK`).
-/

open Complexity

namespace SparseIrred

/-! ### Generic glue from a correct polynomial-time reduction -/

private theorem coNPHard_Irred_of {f : List Bool → List Bool} (hf : f ∈ FP)
    (hcorr : ∀ x, x ∉ SAT.ThreeSAT.language ↔ f x ∈ IrredLang) : coNPHard IrredLang :=
  SAT.ThreeSAT.NPHard_language.compl.of_reduction ⟨f, hf, hcorr⟩

private theorem NPHard_Red_of {f : List Bool → List Bool} (hf : f ∈ FP)
    (hcorr : ∀ x, x ∈ SAT.ThreeSAT.language ↔ f x ∈ RedLang) : NPHard RedLang :=
  SAT.ThreeSAT.NPHard_language.of_reduction ⟨f, hf, hcorr⟩

private theorem oneQuery_Irred_of {f : List Bool → List Bool} (hf : f ∈ FP)
    (hcorr : ∀ x, x ∉ SAT.ThreeSAT.language ↔ f x ∈ IrredLang) :
    ∀ L ∈ NP, OneQueryReducesPoly L IrredLang := by
  intro L hL
  obtain ⟨g, hg, hgx⟩ := SAT.ThreeSAT.NPHard_language L hL
  refine oneQueryReducesPoly_of_neg (f := f ∘ g) (mem_FP_comp hg hf) fun x => ?_
  rw [hgx x, Function.comp_apply, ← hcorr (g x), not_not]

private theorem P_eq_NP_of_coNPHard {L : Language} (h : coNPHard L) (hP : L ∈ P) : P = NP :=
  h.compl.P_eq_NP_of_mem_P (P_compl hP)

/-! ### The notes' route: conditional on the large-gap theorem -/

theorem irreducibility_coNPHard_of_SSS (hSSS : SSSLargeGap) : coNPHard IrredLang :=
  coNPHard_Irred_of reduce_mem_FP fun x => (reduce_correct_of_SSS hSSS x).2

theorem reducibility_NPHard_of_SSS (hSSS : SSSLargeGap) : NPHard RedLang :=
  NPHard_Red_of reduce_mem_FP fun x => (reduce_correct_of_SSS hSSS x).1

theorem irreducibility_NPHard_oneQuery_of_SSS (hSSS : SSSLargeGap) :
    ∀ L ∈ NP, OneQueryReducesPoly L IrredLang :=
  oneQuery_Irred_of reduce_mem_FP fun x => (reduce_correct_of_SSS hSSS x).2

theorem P_eq_NP_of_irreducibility_mem_P_of_SSS (hSSS : SSSLargeGap) (h : IrredLang ∈ P) :
    P = NP :=
  P_eq_NP_of_coNPHard (irreducibility_coNPHard_of_SSS hSSS) h

/-! ### Theorem 8, unconditional -/

/-- (1) Irreducibility in `ℤ[X]` is coNP-hard under polynomial-time many-one reductions. -/
theorem irreducibility_coNPHard : coNPHard IrredLang :=
  coNPHard_Irred_of reduce_mem_FP fun x => (reduce_correct x).2

/-- (2) Reducibility in `ℤ[X]` is NP-hard under polynomial-time many-one reductions. -/
theorem reducibility_NPHard : NPHard RedLang :=
  NPHard_Red_of reduce_mem_FP fun x => (reduce_correct x).1

/-- (3) Irreducibility is NP-hard under polynomial-time one-query Turing reductions. -/
theorem irreducibility_NPHard_oneQuery : ∀ L ∈ NP, OneQueryReducesPoly L IrredLang :=
  oneQuery_Irred_of reduce_mem_FP fun x => (reduce_correct x).2

/-- (4) A polynomial-time irreducibility test implies `P = NP`. -/
theorem P_eq_NP_of_irreducibility_mem_P (h : IrredLang ∈ P) : P = NP :=
  P_eq_NP_of_coNPHard irreducibility_coNPHard h

/-! ### Robust forms: the test or oracle only has to be correct on canonical codes

`IrredLang ∈ P` asks for a decider that also rejects every non-code.  The reduction only ever
produces canonical codes (`reduce x = encPoly (reducePoly x)`), so a polynomial-time test, or an
oracle, that is correct on the canonical codes `encPoly f` and arbitrary elsewhere suffices. -/

/-- (4, robust) A polynomial-time test that is correct on every canonical binary-sparse code
implies `P = NP`. -/
theorem P_eq_NP_of_irreducibility_test {L : Language} (hL : L ∈ P)
    (hcorr : ∀ f : Polynomial ℤ, encPoly f ∈ L ↔ Irreducible f) : P = NP := by
  have hred : SAT.ThreeSAT.languageᶜ ≤ₚ L := by
    refine ⟨reduce, reduce_mem_FP, fun x => ?_⟩
    rw [Set.mem_compl_iff, (reduce_correct x).2, reduce, encPoly_mem_IrredLang_iff, hcorr]
  exact P_eq_NP_of_coNPHard (SAT.ThreeSAT.NPHard_language.compl.of_reduction hred) hL

/-- (3, robust) One-query NP-hardness where the oracle only has to answer correctly on canonical
codes: for every `L ∈ NP` there is a polynomial-time oracle machine that decides `L` with exactly
one query whenever its oracle agrees with irreducibility on all codes `encPoly f`. -/
theorem irreducibility_NPHard_oneQuery_of_codes (L : Language) (hL : L ∈ NP) :
    ∃ (k d : ℕ) (machine : OracleTM k) (T : ℕ → ℕ), T =O (· ^ d) ∧
      ∀ oracle : BooleanOracle, (∀ f : Polynomial ℤ, oracle (encPoly f) = true ↔ Irreducible f) →
        ∀ x, ∃ cfg time, time ≤ T x.length ∧
          reachesInQ machine oracle time 1 (machine.initCfg x) cfg ∧ machine.halted cfg ∧
          (x ∈ L → cfg.output.cells 1 = Γ.one) ∧ (x ∉ L → cfg.output.cells 1 = Γ.zero) := by
  obtain ⟨g, hg, hgx⟩ := SAT.ThreeSAT.NPHard_language L hL
  obtain ⟨k, d, machine, T, hT, hrun⟩ := exists_negQuery_machine (mem_FP_comp hg reduce_mem_FP)
  refine ⟨k, d, machine, T, hT, fun oracle horacle x => ?_⟩
  obtain ⟨cfg, time, ht, hr, hh, hcell⟩ := hrun oracle x
  have key : x ∈ L ↔ oracle (reduce (g x)) = false := by
    have h1 := (reduce_correct (g x)).2
    rw [reduce, encPoly_mem_IrredLang_iff, ← horacle] at h1
    rw [hgx x, ← not_not (a := g x ∈ SAT.ThreeSAT.language), h1, reduce]
    simp
  refine ⟨cfg, time, ht, hr, hh, fun hx => ?_, fun hx => ?_⟩
  · rw [hcell, Function.comp_apply, key.1 hx]; rfl
  · have : oracle (reduce (g x)) = true := by
      cases h : oracle (reduce (g x))
      · exact absurd (key.2 h) hx
      · rfl
    rw [hcell, Function.comp_apply, this]; rfl

end SparseIrred
