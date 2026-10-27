import SparseIrred.Reduction.Defs
import SparseIrred.FFK.Main

/-!
# Correctness of the reduction on every bit string
-/

open Polynomial Complexity

namespace SparseIrred

open Complexity.SAT

theorem irreducible_X_int : Irreducible (X : ℤ[X]) :=
  Polynomial.irreducible_X

theorem reducible_X_sq_sub_one : Reducible (X ^ 2 - 1 : ℤ[X]) := by
  have hfac : (X ^ 2 - 1 : ℤ[X]) = (X - C 1) * (X + C 1) := by
    simp only [map_one]; ring
  have h1 : (X - C 1 : ℤ[X]).natDegree = 1 := natDegree_X_sub_C 1
  have h2 : (X + C 1 : ℤ[X]).natDegree = 1 := natDegree_X_add_C 1
  refine ⟨?_, X - C 1, X + C 1, ?_, ?_, hfac⟩
  · rw [hfac]
    exact mul_ne_zero (ne_zero_of_natDegree_gt (n := 0) (by omega))
      (ne_zero_of_natDegree_gt (n := 0) (by omega))
  · exact Polynomial.not_isUnit_of_natDegree_pos _ (by omega)
  · exact Polynomial.not_isUnit_of_natDegree_pos _ (by omega)

private theorem natDegree_X_sq_sub_one : (X ^ 2 - 1 : ℤ[X]).natDegree = 2 := by
  rw [← C_1, natDegree_X_pow_sub_C]

theorem natDegree_reducePoly_pos (x : List Bool) : 0 < (reducePoly x).natDegree := by
  unfold reducePoly
  split
  · simp
  · rename_i Φ _
    split_ifs
    · rw [natDegree_X_sq_sub_one]; omega
    · simp
    · exact natDegree_Hfinal_pos Φ

/-- Generic correctness from the core semantics on the main branch. -/
private theorem reduce_correct_aux
    (hcore : ∀ Φ : CNF, Φ.Is3CNF → Φ ≠ [] → numVars Φ ≠ 0 →
      (Irreducible (Hfinal Φ) ↔ ¬Φ.Satisfiable)) (x : List Bool) :
    (x ∈ ThreeSAT.language ↔ reduce x ∈ RedLang) ∧
      (x ∉ ThreeSAT.language ↔ reduce x ∈ IrredLang) := by
  have hirr : x ∉ ThreeSAT.language ↔ Irreducible (reducePoly x) := by
    rw [ThreeSAT.mem_language_iff_decode3]
    unfold reducePoly
    rcases hd : CNF.decode3? x with _ | Φ
    · simp [irreducible_X_int]
    · have h3 : Φ.Is3CNF := (CNF.decode3?_eq_some_iff.1 hd).2
      simp only [Option.some.injEq, exists_eq_left']
      split_ifs with hcase hsat
      · simp only [hsat, not_true_eq_false, false_iff]
        rw [← reducible_iff_not_irreducible (by rw [natDegree_X_sq_sub_one]; omega)]
        exact reducible_X_sq_sub_one
      · simp [hsat, irreducible_X_int]
      · push Not at hcase
        exact (hcore Φ h3 hcase.1 hcase.2).symm
  have hpos := natDegree_reducePoly_pos x
  refine ⟨?_, ?_⟩
  · rw [reduce, encPoly_mem_RedLang_iff, reducible_iff_not_irreducible hpos, ← hirr, not_not]
  · rw [reduce, encPoly_mem_IrredLang_iff, hirr]

/-- Correctness, conditional on the large-gap theorem (the notes' route). -/
theorem reduce_correct_of_SSS (hSSS : SSSLargeGap) (x : List Bool) :
    (x ∈ ThreeSAT.language ↔ reduce x ∈ RedLang) ∧
      (x ∉ ThreeSAT.language ↔ reduce x ∈ IrredLang) :=
  reduce_correct_aux (fun Φ _ hΦ _ => Hfinal_irreducible_iff_of_SSS hSSS Φ hΦ) x

/-- Correctness, unconditional. -/
theorem reduce_correct (x : List Bool) :
    (x ∈ ThreeSAT.language ↔ reduce x ∈ RedLang) ∧
      (x ∉ ThreeSAT.language ↔ reduce x ∈ IrredLang) :=
  reduce_correct_aux (fun Φ _ hΦ _ => Hfinal_irreducible_iff Φ hΦ) x

end SparseIrred
