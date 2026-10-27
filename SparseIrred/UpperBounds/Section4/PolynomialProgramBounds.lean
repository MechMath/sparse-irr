import SparseIrred.UpperBounds.Section4.PolynomialProgram
import Mathlib.Data.Nat.Size

/-! # Uniform input-length bounds for the complete polynomial decision program -/

namespace SparseIrred.UpperBounds.Section4

open Polynomial

set_option backward.isDefEq.respectTransparency false

def polynomialStackBound (d e q : ℕ) : ℕ :=
  max (berkowitzStackBound (d + e) + 2)
    (minorStackBound d q + splitDepth ((d - 1 + 1) * (d - 1 + 1)) + 4) + 2

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem polynomialProgram_rank_initial (f : K[X]) :
    (polynomialProgram f).rank (polynomialInitial _ _) ≤
      polynomialStackBound f.natDegree f.derivative.natDegree (Fintype.card K) := by
  unfold polynomialProgram polynomialInitial
  split_ifs with hf
  · change max ((sylvesterProgram f).rank .initial + 2)
      (minorStackBound f.natDegree (Fintype.card K) + 2 +
        splitDepth ((f.natDegree - 1 + 1) * (f.natDegree - 1 + 1)) + 2) + 2 ≤ _
    unfold polynomialStackBound
    apply Nat.add_le_add_right
    apply max_le_max
    · exact Nat.add_le_add_right (berkowitzProgram_rank_initial _) 2
    · omega
  · exact Nat.zero_le _

private theorem log2_le_size (n : ℕ) : n.log2 ≤ n.size := by
  by_cases hn : n = 0
  · subst n; decide
  · have h := (Nat.log2_lt hn).mpr (Nat.lt_size_self n)
    omega

/-- The arithmetic stack bound is polynomial in encoded degree and field size. -/
theorem polynomialStackBound_le_of_size (d e q L : ℕ) (he : e ≤ d)
    (hd : d.size ≤ L) (hq : q.size ≤ L ^ 2 + 1) :
    polynomialStackBound d e q ≤ 100 * (L + 3) ^ 4 := by
  have hdl : d.log2 ≤ L := (log2_le_size d).trans hd
  have hql : q.log2 ≤ L ^ 2 + 1 := (log2_le_size q).trans hq
  have htail : (d - 1 + 1).log2 ≤ L := by
    by_cases h0 : d = 0
    · subst d; exact Nat.zero_le _
    · have heq : d - 1 + 1 = d := by omega
      simpa [heq] using hdl
  have hsum : (d + e + 1).log2 ≤ L + 1 := by
    have hpow := Nat.size_le.mp hd
    have hp : 0 < 2 ^ L := pow_pos (by omega) _
    have hlt : d + e + 1 < 2 ^ ((L + 1) + 1) := by
      simp only [pow_succ]
      omega
    have := (Nat.log2_lt (show d + e + 1 ≠ 0 by omega)).mpr hlt
    omega
  have hsplit : splitDepth ((d - 1 + 1) * (d - 1 + 1)) ≤ 2 * L + 3 := by
    have h := splitDepth_mul_le (d - 1 + 1) (d - 1 + 1) (d - 1 + 1) le_rfl
    omega
  have hsyl : berkowitzStackBound (d + e) + 2 + 2 ≤ 100 * (L + 3) ^ 4 := by
    unfold berkowitzStackBound
    nlinarith [Nat.zero_le (L ^ 3), Nat.zero_le (L ^ 4)]
  have hminor : minorStackBound d q + splitDepth ((d - 1 + 1) * (d - 1 + 1)) + 4 + 2 ≤
      100 * (L + 3) ^ 4 := by
    unfold minorStackBound berkowitzStackBound frobeniusEntryBound
    have hprod : (q.log2 + d.log2 + 4) * (d.log2 + 4) ≤
        (L ^ 2 + 1 + L + 4) * (L + 4) := by
      exact Nat.mul_le_mul (by omega) (by omega)
    nlinarith [Nat.zero_le (L ^ 3), Nat.zero_le (L ^ 4)]
  unfold polynomialStackBound
  omega

/-- The complete polynomial program has a uniform polynomial bound in input length. -/
theorem polynomialProgram_rank_input (f : K[X]) (L : ℕ)
    (hd : f.natDegree.size ≤ L) (hq : (Fintype.card K).size ≤ L ^ 2 + 1) :
    (polynomialProgram f).rank (polynomialInitial _ _) ≤ 100 * (L + 3) ^ 4 :=
  (polynomialProgram_rank_initial f).trans (polynomialStackBound_le_of_size _ _ _ L
    ((natDegree_derivative_le f).trans (Nat.sub_le _ _)) hd hq)

theorem polynomialProgram_stack_input (f : K[X]) (L : ℕ)
    (hd : f.natDegree.size ≤ L) (hq : (Fintype.card K).size ≤ L ^ 2 + 1) (t : ℕ) :
    ((polynomialProgram f).step^[t] (.eval (polynomialInitial _ _) [])).stack.length ≤
      100 * (L + 3) ^ 4 :=
  ((polynomialProgram f).stack_length_iterate_le _ t).trans (polynomialProgram_rank_input f L hd hq)

end SparseIrred.UpperBounds.Section4
