import SparseIrred.UpperBounds.SparseInputBounds
import SparseIrred.UpperBounds.PrimeStreamingBits

/-!
# Prime-counting parameters for unnormalized sparse input lists

The input may contain repeated exponents, zero coefficients and cancellations.
The estimates below use the original list's encoded length, so normalization
does not silently replace the complexity parameter by a larger code length.
-/

open Polynomial SparseDiv SparseDiv.Appendix

namespace SparseIrred.UpperBounds

theorem integerL1_toPolyZ_le (l : ITerms) :
    integerL1 (toPolyZ l) ≤ Machine.absSum l := by
  calc
    integerL1 (toPolyZ l) = Machine.absSum (normalizeZ l) := by
      unfold integerL1
      rw [← toPolyZ_normalizeZ l, canonTerms_toPolyZ (normalizedZ_normalizeZ l)]
    _ ≤ _ := Machine.absSum_normalizeZ_le l

/-- Degree and coefficient size are bounded by the original input, before normalization. -/
theorem raw_input_log_bounds (l : ITerms) :
    Nat.clog 2 ((toPolyZ l).natDegree + 2) ≤ (encITerms l).length + 2 ∧
      Nat.clog 2 (integerL1 (toPolyZ l) + 2) ≤ (encITerms l).length + 2 := by
  have hn := (natDegree_toPolyZ_le l).trans_lt (degreeZ_lt_pow_length l)
  have hS := (Nat.add_le_add_right (integerL1_toPolyZ_le l) 1).trans
    (absSum_add_one_le_pow_length l)
  have hp : 0 < 2 ^ (encITerms l).length := by positivity
  constructor <;> apply Nat.clog_le_of_le_pow <;> rw [pow_add] <;> norm_num <;> omega

/-- The linear `Δ` bound holds for every original encoded sparse term list. -/
theorem inputDelta_le_raw_length (l : ITerms) :
    inputDelta (toPolyZ l) ≤ 2 * (encITerms l).length + 6 := by
  have h := raw_input_log_bounds l
  unfold inputDelta
  omega

theorem cutoffLog_le_raw_length (C₀ : ℕ) (l : ITerms) :
    cutoffLog C₀ (toPolyZ l).natDegree (inputDelta (toPolyZ l)) ≤
      38 + Nat.clog 2 C₀ + 6 * (encITerms l).length := by
  have h := cutoffLog_le C₀ (toPolyZ l).natDegree (inputDelta (toPolyZ l))
  have hn := (Nat.clog_mono_right 2 (Nat.le_add_right (toPolyZ l).natDegree 2)).trans
    (raw_input_log_bounds l).1
  have hd : Nat.clog 2 (inputDelta (toPolyZ l) + 1) ≤ inputDelta (toPolyZ l) + 1 :=
    Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have hΔ := inputDelta_le_raw_length l
  omega

/-- The cutoff's binary exponent is linear in the original sparse input length. -/
theorem inputCutoffExponent_le_raw_length (C₀ : ℕ) (l : ITerms) :
    inputCutoffExponent C₀ (toPolyZ l) ≤
      128 * (38 + Nat.clog 2 C₀) + 768 * (encITerms l).length := by
  have := Nat.mul_le_mul_left 128 (cutoffLog_le_raw_length C₀ l)
  unfold inputCutoffExponent
  omega

/-- The enormous cutoff has only linearly many binary digits even for unnormalized inputs. -/
theorem inputCutoff_size_le_raw_length (C₀ : ℕ) (l : ITerms) :
    Nat.size (2 ^ inputCutoffExponent C₀ (toPolyZ l)) ≤
      128 * (38 + Nat.clog 2 C₀) + 768 * (encITerms l).length + 1 := by
  rw [Nat.size_pow]
  have := inputCutoffExponent_le_raw_length C₀ l
  omega

/-- Actual streaming counter widths relative to an arbitrary original sparse list. -/
theorem raw_streaming_counter_bits (l : ITerms) (hl : (toPolyZ l).IsPrimitive)
    (k m : ℕ) (hk : k ≤ 2 ^ m) :
    (primeStreaming (toPolyZ l) k).1.size ≤ m + 1 ∧
      (primeStreaming (toPolyZ l) k).2.size ≤ (encITerms l).length + m + 1 := by
  have hb := primeStreaming_prefix_bounds (toPolyZ l) hl k (2 ^ m) hk
  refine ⟨(Nat.size_le_size hb.1).trans_eq Nat.size_pow, Nat.size_le.mpr ?_⟩
  have hn := (natDegree_toPolyZ_le l).trans_lt (degreeZ_lt_pow_length l)
  calc
    _ ≤ 2 * (toPolyZ l).natDegree * 2 ^ m := hb.2
    _ < 2 * 2 ^ (encITerms l).length * 2 ^ m :=
      Nat.mul_lt_mul_of_pos_right
        (Nat.mul_lt_mul_of_pos_left hn (by decide)) (by positivity)
    _ = _ := by rw [pow_add, pow_add]; norm_num; ring

/-- Both streaming counters have explicit linear bit bounds at the chosen cutoff. -/
theorem raw_inputCutoff_counter_bits (C₀ : ℕ) (l : ITerms) (hl : (toPolyZ l).IsPrimitive)
    (k : ℕ) (hk : k ≤ 2 ^ inputCutoffExponent C₀ (toPolyZ l)) :
    (primeStreaming (toPolyZ l) k).1.size ≤
        128 * (38 + Nat.clog 2 C₀) + 768 * (encITerms l).length + 1 ∧
      (primeStreaming (toPolyZ l) k).2.size ≤
        128 * (38 + Nat.clog 2 C₀) + 769 * (encITerms l).length + 1 := by
  have h := raw_streaming_counter_bits l hl k (inputCutoffExponent C₀ (toPolyZ l)) hk
  have hm := inputCutoffExponent_le_raw_length C₀ l
  omega

end SparseIrred.UpperBounds
