import SparseIrred.UpperBounds.Machine.StreamingStepFP
import SparseIrred.UpperBounds.Machine.StreamingSemantics
import SparseIrred.UpperBounds.Machine.StreamingMachine

/-!
# Complete trace of the deterministic prime/root enumeration

The proof identifies every stored state, bounds all counter encodings linearly,
and supplies the actual deterministic iteration machine with its termination
and final-answer specification. The compiled machine's polynomial-space theorem
also covers the work done between these stored states.
-/

open Complexity SparseDiv SparseDiv.Appendix SparseDiv.StringArith SparseGcd

namespace SparseIrred.UpperBounds.Machine

def streamStop (C₀ : ℕ) (s : List Bool) : ℕ :=
  streamCutoff C₀ s * streamCutoff C₀ s + 2

def streamAnswer (C₀ : ℕ) (s : List Bool) : Bool :=
  let X := streamCutoff C₀ s
  streamVerdict s (streamCounts s X (X * X)).1 (streamCounts s X (X * X)).2

/-- Every finite enumeration prefix has exactly the expected position and counters. -/
theorem stream_iterate_run (C₀ : ℕ) (s : List Bool) (t : ℕ)
    (ht : t ≤ streamCutoff C₀ s * streamCutoff C₀ s) :
    (streamStepStr C₀)^[t + 1] (pair [] s) =
      streamRunCode s (streamCutoff C₀ s) t
        (streamCounts s (streamCutoff C₀ s) t).1
        (streamCounts s (streamCutoff C₀ s) t).2 := by
  induction t with
  | zero => simp [streamStepStr_start]
  | succ t ih =>
      rw [Function.iterate_succ_apply', ih (by omega), streamStepStr_run]
      · rw [ite_eq_left (by omega), streamCounts_succ]
      · exact pow_ne_zero _ (by decide)

theorem stream_iterate_done (C₀ : ℕ) (s : List Bool) :
    (streamStepStr C₀)^[streamStop C₀ s] (pair [] s) =
      streamDoneCode (streamAnswer C₀ s) := by
  unfold streamStop
  rw [show streamCutoff C₀ s * streamCutoff C₀ s + 2 =
    (streamCutoff C₀ s * streamCutoff C₀ s + 1) + 1 by omega]
  rw [Function.iterate_succ_apply', stream_iterate_run C₀ s _ le_rfl,
    streamStepStr_run C₀ s (streamCutoff C₀ s) _ _ _ (by exact pow_ne_zero _ (by decide)),
    ite_eq_right (lt_irrefl _)]
  rfl

theorem stream_iterate_answer (C₀ : ℕ) (s : List Bool) :
    (streamStepStr C₀)^[streamStop C₀ s + 1] (pair [] s) = [streamAnswer C₀ s] := by
  rw [Function.iterate_succ_apply', stream_iterate_done, streamStepStr_done]

/-- Even on malformed input, all stored counters have only linearly many bits. -/
theorem streamRunCode_length_le (s : List Bool) (m t : ℕ) (ht : t ≤ 2 ^ m * 2 ^ m) :
    (streamRunCode s (2 ^ m) t (streamCounts s (2 ^ m) t).1
      (streamCounts s (2 ^ m) t).2).length ≤ 2 * s.length + 12 * m + 20 := by
  have hsq : 2 ^ m * 2 ^ m = 2 ^ (2 * m) := by rw [← pow_add]; congr 1; omega
  have hc := streamCounts_bounds s (2 ^ m) t
  have ht' : t ≤ 2 ^ (2 * m) := ht.trans_eq hsq
  have htbits : t.size ≤ 2 * m + 1 :=
    (Nat.size_le_size ht').trans_eq (Nat.size_pow)
  have hPbits : (streamCounts s (2 ^ m) t).1.size ≤ 2 * m + 1 :=
    (Nat.size_le_size (hc.1.trans ht')).trans_eq (Nat.size_pow)
  have hA : (streamCounts s (2 ^ m) t).2 ≤ 2 ^ (2 * m + 1) := by
    rw [pow_succ]
    omega
  have hAbits : (streamCounts s (2 ^ m) t).2.size ≤ 2 * m + 2 :=
    (Nat.size_le_size hA).trans_eq (Nat.size_pow)
  simp only [streamRunCode, List.length_cons, pair_length, length_encNat, Nat.size_pow]
  omega

noncomputable def streamStateBound (C₀ : ℕ) : Polynomial ℕ :=
  Polynomial.C (12 * (128 * (38 + Nat.clog 2 C₀)) + 20) +
    Polynomial.C (2 + 12 * 768) * Polynomial.X

noncomputable def streamTimeExponent (C₀ : ℕ) : Polynomial ℕ :=
  Polynomial.C (2 * (128 * (38 + Nat.clog 2 C₀)) + 2) +
    Polynomial.C (2 * 768) * Polynomial.X

theorem stream_iterate_length_le (C₀ : ℕ) (s : List Bool) (i : ℕ)
    (hi : i ≤ streamStop C₀ s + 1) :
    ((streamStepStr C₀)^[i] (pair [] s)).length ≤ (streamStateBound C₀).eval s.length := by
  have hb := cutoffUnary_length_le C₀ s
  have hlarge : 2 * s.length + 12 * (cutoffUnary C₀ s).length + 20 ≤
      (streamStateBound C₀).eval s.length := by
    simp only [streamStateBound, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    omega
  by_cases hi0 : i = 0
  · subst i
    simp only [Function.iterate_zero, id_eq, pair_length, List.length_nil, mul_zero, zero_add]
    omega
  by_cases hirun : i ≤ streamCutoff C₀ s * streamCutoff C₀ s + 1
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
    rw [stream_iterate_run C₀ s t (by omega)]
    exact (streamRunCode_length_le s _ t (by exact Nat.le_of_succ_le_succ hirun)).trans hlarge
  · have hi' : i = streamStop C₀ s ∨ i = streamStop C₀ s + 1 := by
      dsimp [streamStop] at hi ⊢
      omega
    rcases hi' with rfl | rfl
    · rw [stream_iterate_done]
      change 2 ≤ _
      omega
    · rw [stream_iterate_answer]
      change 1 ≤ _
      omega

theorem streamStop_le (C₀ : ℕ) (s : List Bool) :
    streamStop C₀ s ≤ 2 ^ (streamTimeExponent C₀).eval s.length := by
  let m := (cutoffUnary C₀ s).length
  have hm := cutoffUnary_length_le C₀ s
  have hsmall : streamStop C₀ s ≤ 2 ^ (2 * m + 2) := by
    have hpos : 1 ≤ (2 : ℕ) ^ (2 * m) := Nat.one_le_two_pow
    have hsq : (2 : ℕ) ^ m * 2 ^ m = 2 ^ (2 * m) := by
      rw [← pow_add]; congr 1; omega
    change 2 ^ m * 2 ^ m + 2 ≤ _
    rw [hsq, pow_add]
    norm_num
    omega
  exact hsmall.trans (Nat.pow_le_pow_right (by decide) (by
    simp only [streamTimeExponent, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    dsimp [m]
    omega))

/-- The concrete program satisfies every condition of the verified iteration compiler. -/
def section3StreamingTrace (C₀ : ℕ) :
    StreamingTrace (streamStepStr C₀) (streamAnswer C₀)
      (streamStateBound C₀) (streamTimeExponent C₀) where
  state s i := (streamStepStr C₀)^[i] (pair [] s)
  stop := streamStop C₀
  start _ := rfl
  step s i := Function.iterate_succ_apply' _ _ _
  length_le := stream_iterate_length_le C₀
  stop_pos s := by unfold streamStop; omega
  stop_le := streamStop_le C₀
  running s i hi hirun := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
    rw [stream_iterate_run C₀ s t (by dsimp [streamStop] at hirun; omega)]
    rfl
  done s := by rw [stream_iterate_done]; rfl
  answer_nonempty s := by rw [stream_iterate_answer]; simp
  answer_eq s := by rw [stream_iterate_answer]; rfl

/-- Section 3.6 gives PSPACE directly through a deterministic counter-enumeration machine. -/
theorem section3_deterministic_streaming_mem_PSPACE (C₀ : ℕ) (hC : 1 ≤ C₀)
    (hExternal : UniformPrimeIdealEstimate C₀) (hAKS : BinaryPrimalityInFP) :
    IrredLang ∈ PSPACE := by
  apply streamingLanguage_mem_PSPACE (streamStepStr_mem_FP C₀ hAKS) (section3StreamingTrace C₀)
  intro s
  exact (streamVerdict_counts_iff_mem_IrredLang C₀ hC hExternal s).symm

end SparseIrred.UpperBounds.Machine
