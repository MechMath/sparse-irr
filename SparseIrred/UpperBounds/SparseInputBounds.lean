import SparseIrred.Sparse.Canonical
import SparseIrred.Machine.Bounds
import SparseIrred.UpperBounds.PrimeCutoff

/-!
# Input-length bounds for the prime-counting cutoff

The length is the actual framed sign-magnitude binary encoding `encITerms`, not
the degree or a dense polynomial size. These bounds allow arbitrary term lists;
in particular, coefficient cancellation and repeated exponents cause no problem.
-/

open Polynomial Complexity SparseDiv SparseDiv.Appendix SparseDiv.StringArith

namespace SparseIrred.UpperBounds

theorem encITerms_cons_length (t : ℤ × ℕ) (l : ITerms) :
    (encITerms (t :: l)).length =
      22 + 4 * t.1.natAbs.size + 2 * t.2.size + (encITerms l).length := by
  simp [encITerms, frame_cons, encITerm, pair_length, length_encInt]
  omega

/-- The sum of coefficient magnitudes stays below an exponential in the actual code length. -/
theorem absSum_add_one_le_pow_length (l : ITerms) :
    Machine.absSum l + 1 ≤ 2 ^ (encITerms l).length := by
  induction l with
  | nil => simp [Machine.absSum, encITerms, frame]
  | cons t l ih =>
    have ht : t.1.natAbs + 1 ≤ 2 ^ t.1.natAbs.size := Nat.lt_size_self _
    have hprod := Nat.mul_le_mul ht ih
    have hle : t.1.natAbs.size + (encITerms l).length ≤ (encITerms (t :: l)).length := by
      rw [encITerms_cons_length]
      omega
    calc
      Machine.absSum (t :: l) + 1 ≤ (t.1.natAbs + 1) * (Machine.absSum l + 1) := by
        rw [Machine.absSum_cons]
        nlinarith [Nat.zero_le (t.1.natAbs * Machine.absSum l)]
      _ ≤ 2 ^ t.1.natAbs.size * 2 ^ (encITerms l).length := hprod
      _ ≤ _ := by rw [← pow_add]; exact Nat.pow_le_pow_right (by decide) hle

/-- The degree is controlled by the binary exponent fields even before normalization. -/
theorem degreeZ_lt_pow_length (l : ITerms) : degreeZ l < 2 ^ (encITerms l).length := by
  induction l with
  | nil => simp [degreeZ, encITerms]
  | cons t l ih =>
    have hlen := encITerms_cons_length t l
    have he := Nat.lt_size_self t.2
    have he' : 2 ^ t.2.size ≤ 2 ^ (encITerms (t :: l)).length :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hl' : 2 ^ (encITerms l).length ≤ 2 ^ (encITerms (t :: l)).length :=
      Nat.pow_le_pow_right (by decide) (by omega)
    change max t.2 (degreeZ l) < _
    exact max_lt (he.trans_le he') (ih.trans_le hl')

/-- The coefficient `ℓ¹` norm as a natural number. -/
noncomputable def integerL1 (f : ℤ[X]) : ℕ := Machine.absSum (canonTerms f)

theorem integerL1_eq_sum (f : ℤ[X]) : integerL1 f = ∑ e ∈ f.support, (f.coeff e).natAbs := by
  rw [Finset.sum_eq_multiset_sum, ← Finset.sort_eq f.support (· ≤ ·), Multiset.map_coe,
    Multiset.sum_coe]
  simp [integerL1, Machine.absSum, canonTerms, List.map_map, Function.comp_def]

theorem integerL1_pos (f : ℤ[X]) (hf : f ≠ 0) : 0 < integerL1 f := by
  by_contra hn
  have hz : integerL1 f = 0 := by omega
  apply hf
  ext e
  have hc := Machine.natAbs_coeff_toPolyZ_le (canonTerms f) e
  rw [toPolyZ_canonTerms] at hc
  change (f.coeff e).natAbs ≤ integerL1 f at hc
  rw [hz] at hc
  simpa using hc

theorem degree_lt_pow_encPoly_length (f : ℤ[X]) : f.natDegree < 2 ^ (encPoly f).length := by
  have h := (natDegree_toPolyZ_le (canonTerms f)).trans_lt
    (degreeZ_lt_pow_length (canonTerms f))
  simpa [encPoly, toPolyZ_canonTerms] using h

theorem integerL1_add_one_le_pow_encPoly_length (f : ℤ[X]) :
    integerL1 f + 1 ≤ 2 ^ (encPoly f).length :=
  absSum_add_one_le_pow_length _

/-- The integer parameter `Δ` in equation (15) of the standalone prime-counting note. -/
noncomputable def inputDelta (f : ℤ[X]) : ℕ :=
  Nat.clog 2 (f.natDegree + 2) + Nat.clog 2 (integerL1 f + 2) + 2

/-- Both ceiling logarithms are bounded by the length of the original sparse code. -/
theorem input_log_bounds (f : ℤ[X]) :
    Nat.clog 2 (f.natDegree + 2) ≤ (encPoly f).length + 2 ∧
      Nat.clog 2 (integerL1 f + 2) ≤ (encPoly f).length + 2 := by
  have hn := degree_lt_pow_encPoly_length f
  have hS := integerL1_add_one_le_pow_encPoly_length f
  have hp : 0 < 2 ^ (encPoly f).length := by positivity
  constructor <;> apply Nat.clog_le_of_le_pow <;> rw [pow_add] <;> norm_num <;> omega

/-- `Δ = O(L)`, with an explicit bound on canonical sparse inputs. -/
theorem inputDelta_le_length (f : ℤ[X]) : inputDelta f ≤ 2 * (encPoly f).length + 6 := by
  have h := input_log_bounds f
  unfold inputDelta
  omega

theorem inputDelta_ge_six (f : ℤ[X]) (hf : 0 < f.natDegree) : 6 ≤ inputDelta f := by
  have hS := integerL1_pos f (Polynomial.ne_zero_of_natDegree_gt hf)
  have hn : 2 ≤ Nat.clog 2 (f.natDegree + 2) := by
    apply (Nat.lt_clog_iff_pow_lt (by decide : 1 < (2 : ℕ))).mpr
    norm_num
    omega
  have hv : 2 ≤ Nat.clog 2 (integerL1 f + 2) := by
    apply (Nat.lt_clog_iff_pow_lt (by decide : 1 < (2 : ℕ))).mpr
    norm_num
    omega
  unfold inputDelta
  omega

/-- The cutoff exponent is linear in the length of the actual sparse input code. -/
theorem cutoffLog_le_input_length (C₀ : ℕ) (f : ℤ[X]) :
    cutoffLog C₀ f.natDegree (inputDelta f) ≤
      38 + Nat.clog 2 C₀ + 6 * (encPoly f).length := by
  have h := cutoffLog_le C₀ f.natDegree (inputDelta f)
  have hn := (Nat.clog_mono_right 2 (Nat.le_add_right f.natDegree 2)).trans
    (input_log_bounds f).1
  have hd : Nat.clog 2 (inputDelta f + 1) ≤ inputDelta f + 1 :=
    Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have hΔ := inputDelta_le_length f
  omega

/-- The number of bits guessed for each prime/residue candidate, `m=32k=128 ell`. -/
noncomputable def inputCutoffExponent (C₀ : ℕ) (f : ℤ[X]) : ℕ :=
  128 * cutoffLog C₀ f.natDegree (inputDelta f)

theorem inputCutoffExponent_le (C₀ : ℕ) (f : ℤ[X]) :
    inputCutoffExponent C₀ f ≤
      128 * (38 + Nat.clog 2 C₀) + 768 * (encPoly f).length := by
  have := Nat.mul_le_mul_left 128 (cutoffLog_le_input_length C₀ f)
  unfold inputCutoffExponent
  omega

/-- The cutoff itself, despite its value, has only linearly many binary digits. -/
theorem inputCutoff_size_le (C₀ : ℕ) (f : ℤ[X]) :
    Nat.size (2 ^ inputCutoffExponent C₀ f) ≤
      128 * (38 + Nat.clog 2 C₀) + 768 * (encPoly f).length + 1 := by
  rw [Nat.size_pow]
  have := inputCutoffExponent_le C₀ f
  omega

/-- Formal derivatives have coefficient magnitudes bounded by degree times `ℓ¹` norm. -/
theorem derivative_coeff_natAbs_le (f : ℤ[X]) (e : ℕ) :
    (f.derivative.coeff e).natAbs ≤ f.natDegree * integerL1 f := by
  rw [Polynomial.coeff_derivative, Int.natAbs_mul]
  by_cases hc : f.coeff (e + 1) = 0
  · simp [hc]
  · have he := Polynomial.le_natDegree_of_ne_zero hc
    have hnorm := Machine.natAbs_coeff_toPolyZ_le (canonTerms f) (e + 1)
    rw [toPolyZ_canonTerms] at hnorm
    change (f.coeff (e + 1)).natAbs ≤ integerL1 f at hnorm
    have hcast : (↑e + 1 : ℤ).natAbs = e + 1 := by norm_cast
    rw [hcast]
    simpa only [Nat.mul_comm] using Nat.mul_le_mul he hnorm

/-- Binary coefficient magnitudes of the derivative are at most twice the input length. -/
theorem derivative_coeff_size_le (f : ℤ[X]) (e : ℕ) :
    (f.derivative.coeff e).natAbs.size ≤ 2 * (encPoly f).length := by
  apply Nat.size_le.mpr
  have hn := degree_lt_pow_encPoly_length f
  have hS := integerL1_add_one_le_pow_encPoly_length f
  have hS' : integerL1 f < 2 ^ (encPoly f).length := by omega
  have hp := Nat.mul_lt_mul'' hn hS'
  have hcoeff := derivative_coeff_natAbs_le f e
  have hpow : 2 ^ (encPoly f).length * 2 ^ (encPoly f).length =
      2 ^ (2 * (encPoly f).length) := by rw [← pow_add]; congr 1; omega
  rw [hpow] at hp
  exact hcoeff.trans_lt hp

end SparseIrred.UpperBounds
