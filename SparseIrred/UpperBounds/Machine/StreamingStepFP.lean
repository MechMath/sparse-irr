import SparseIrred.UpperBounds.Machine.StreamingProgram

/-! # Correctness and polynomial time of one deterministic enumeration step -/

open Complexity SparseDiv SparseDiv.Appendix SparseDiv.StringArith SparseGcd

namespace SparseIrred.UpperBounds.Machine

theorem cobham_streamPrimeIncrementStr (hAKS : BinaryPrimalityInFP) {n : ℕ}
    {gp ga : (Fin n → List Bool) → List Bool} (hp : Cobham gp) (ha : Cobham ga) :
    Cobham fun v ↦ streamPrimeIncrementStr (gp v) (ga v) :=
  Cobham.iteFn (Cobham.andFn (cobham_binaryPrimeFlag_comp hAKS hp)
    (cobham_isZeroBits_comp ha)) (Cobham.const _) (Cobham.const _)

theorem cobham_streamRootIncrementStr (hAKS : BinaryPrimalityInFP) {n : ℕ}
    {gs gp ga : (Fin n → List Bool) → List Bool}
    (hs : Cobham gs) (hp : Cobham gp) (ha : Cobham ga) :
    Cobham fun v ↦ streamRootIncrementStr (gs v) (gp v) (ga v) :=
  Cobham.iteFn
    (Cobham.andFn (Cobham.andFn (cobham_binaryPrimeFlag_comp hAKS hp)
      (cobham_ltBits_comp ha hp))
      (cobham_isZeroBits_comp (cobham_sparseEvalModStr_comp false hp ha hs)))
    (Cobham.iteFn (cobham_isZeroBits_comp (cobham_sparseEvalModStr_comp true hp ha hs))
      (Cobham.const _) (Cobham.const _)) (Cobham.const _)

theorem cobham_streamVerdictStr (hAKS : BinaryPrimalityInFP) {n : ℕ}
    {gs gP gA : (Fin n → List Bool) → List Bool}
    (hs : Cobham gs) (hP : Cobham gP) (hA : Cobham gA) :
    Cobham fun v ↦ streamVerdictStr (gs v) (gP v) (gA v) := by
  have hv := (Cobham.comp (FP_subset_CobhamFP validCode_mem_FP)
    fun _ : Fin 1 ↦ hs).of_eq (fun _ ↦ rfl)
  have hd := (Cobham.comp (FP_subset_CobhamFP degreeStr_mem_FP)
    fun _ : Fin 1 ↦ hs).of_eq (fun _ ↦ rfl)
  have hc := (Cobham.comp (FP_subset_CobhamFP contentStr_mem_FP)
    fun _ : Fin 1 ↦ hs).of_eq (fun _ ↦ rfl)
  exact Cobham.iteFn hv (Cobham.iteFn (cobham_isZeroBits_comp hd)
    (cobham_binaryPrimeFlag_comp hAKS hc)
    (Cobham.andFn (cobham_eqBits_comp hc (Cobham.const [true]))
      (cobham_ltBits_comp (cobham_mulBits_comp (Cobham.const _) hA)
        (cobham_mulBits_comp (Cobham.const _) hP)))) (Cobham.const [false])

theorem cobham_streamCutoffStr (C₀ : ℕ) {n : ℕ}
    {gs : (Fin n → List Bool) → List Bool} (hs : Cobham gs) :
    Cobham fun v ↦ streamCutoffStr C₀ (gs v) :=
  Cobham.appendFn (Cobham.zeroBlockFn (cobham_cutoffUnary C₀ hs)) (Cobham.const [true])

theorem cobham_streamInitStr (C₀ : ℕ) {n : ℕ}
    {gs : (Fin n → List Bool) → List Bool} (hs : Cobham gs) :
    Cobham fun v ↦ streamInitStr C₀ (gs v) :=
  cobham_cons false (cobham_cons false (cobham_pair_comp hs
    (cobham_pair_comp (cobham_streamCutoffStr C₀ hs) (Cobham.const _))))

theorem cobham_streamAdvanceStr (hAKS : BinaryPrimalityInFP) {n : ℕ}
    {gz : (Fin n → List Bool) → List Bool} (hz : Cobham gz) :
    Cobham fun v ↦ streamAdvanceStr (gz v) := by
  have hs := cobham_pairFst_comp hz
  have hX := cobham_pairFst_comp (cobham_pairSnd_comp hz)
  have ht := cobham_pairFst_comp (cobham_pairSnd_comp (cobham_pairSnd_comp hz))
  have hP := cobham_pairFst_comp
    (cobham_pairSnd_comp (cobham_pairSnd_comp (cobham_pairSnd_comp hz)))
  have hA := cobham_pairSnd_comp
    (cobham_pairSnd_comp (cobham_pairSnd_comp (cobham_pairSnd_comp hz)))
  have hp := cobham_canonBits_comp (cobham_divStr_comp ht hX)
  have ha := cobham_canonBits_comp (cobham_redStr_comp ht hX)
  exact Cobham.iteFn (cobham_ltBits_comp ht (cobham_mulBits_comp hX hX))
    (cobham_cons false (cobham_cons false (cobham_pair_comp hs
      (cobham_pair_comp hX (cobham_pair_comp (cobham_canonBits_comp (cobham_succBits_comp ht))
        (cobham_pair_comp
          (cobham_canonBits_comp (cobham_addBits_comp hP
            (cobham_streamPrimeIncrementStr hAKS hp ha)))
          (cobham_canonBits_comp (cobham_addBits_comp hA
            (cobham_streamRootIncrementStr hAKS hs hp ha)))))))))
    (cobham_cons true (cobham_streamVerdictStr hAKS hs hP hA))

/-- One deterministic step is polynomial-time; no enumeration is hidden in this bound. -/
theorem streamStepStr_mem_FP (C₀ : ℕ) (hAKS : BinaryPrimalityInFP) :
    streamStepStr C₀ ∈ FP := by
  apply CobhamFP_subset_FP
  have ht := Cobham.tailFn (Cobham.proj (n := 1) 0)
  have hd := Cobham.dropFn (Cobham.const [false, false]) (Cobham.proj (n := 1) 0)
  exact Cobham.iteFn (.proj 0) ht
    (Cobham.iteFn ht (cobham_streamInitStr C₀ hd) (cobham_streamAdvanceStr hAKS hd))

theorem streamPrimeIncrementStr_eq (p a : ℕ) :
    streamPrimeIncrementStr (encNat p) (encNat a) = encNat (streamPrimeIncrement p a) := by
  by_cases hp : p.Prime <;> by_cases ha : a = 0 <;>
    simp [streamPrimeIncrementStr, streamPrimeIncrement, binaryPrimeFlag,
      isZeroBits_eq_decide_decNat, hp, ha] <;> rfl

theorem streamRootIncrementStr_eq (s : List Bool) (p a : ℕ) :
    streamRootIncrementStr s (encNat p) (encNat a) =
      encNat (streamRootIncrement s p a) := by
  by_cases hp : p.Prime <;> by_cases ha : a < p <;>
    by_cases hv : decNat (sparseEvalModStr false (encNat p) (encNat a) s) = 0 <;>
    by_cases hd : decNat (sparseEvalModStr true (encNat p) (encNat a) s) = 0 <;>
    simp [streamRootIncrementStr, streamRootIncrement, binaryPrimeFlag,
      isZeroBits_eq_decide_decNat, ltBits_eq_decide_decNat, hp, ha, hv, hd] <;> rfl

/-- The output of the boundary/threshold test is always a single Boolean bit. -/
theorem streamVerdictStr_singleton (s P A : List Bool) :
    streamVerdictStr s P A = [(streamVerdictStr s P A).headD false] := by
  have hc (flag a b : List Bool) (ha : a.length = 1) (hb : b.length = 1) :
      (caseBit₀ flag a b).length = 1 := by
    rcases caseBit₀_cases flag a b with h | h <;> rw [h] <;> assumption
  have hlen : (streamVerdictStr s P A).length = 1 := by
    unfold streamVerdictStr
    apply hc
    · exact hc _ _ _ rfl (andBit_length _ _)
    · rfl
  cases h : streamVerdictStr s P A with
  | nil => simp [h] at hlen
  | cons b rest =>
      have hr : rest = [] := by simpa [h] using hlen
      simp [hr]

theorem streamVerdictStr_eq (s : List Bool) (P A : ℕ) :
    streamVerdictStr s (encNat P) (encNat A) = [streamVerdict s P A] :=
  streamVerdictStr_singleton _ _ _

theorem encNat_two_pow (m : ℕ) : encNat (2 ^ m) = List.replicate m false ++ [true] := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [pow_succ, Nat.mul_comm, encNat, Nat.bit0_bits _ (by positivity)]
      change false :: encNat (2 ^ m) = _
      simp [ih, List.replicate_succ]

theorem streamCutoffStr_eq (C₀ : ℕ) (s : List Bool) :
    streamCutoffStr C₀ s = encNat (streamCutoff C₀ s) :=
  (encNat_two_pow _).symm

theorem streamInitStr_eq (C₀ : ℕ) (s : List Bool) :
    streamInitStr C₀ s = streamRunCode s (streamCutoff C₀ s) 0 0 0 := by
  simp only [streamInitStr, streamRunCode, streamCutoffStr_eq]
  rfl

theorem streamStepStr_start (C₀ : ℕ) (s : List Bool) :
    streamStepStr C₀ (pair [] s) = streamRunCode s (streamCutoff C₀ s) 0 0 0 := by
  change streamInitStr C₀ s = _
  exact streamInitStr_eq C₀ s

theorem streamStepStr_done (C₀ : ℕ) (b : Bool) :
    streamStepStr C₀ (streamDoneCode b) = [b] := rfl

/-- The concrete binary transition is precisely one update of the two counters. -/
theorem streamStepStr_run (C₀ : ℕ) (s : List Bool) (X t P A : ℕ) (hX : X ≠ 0) :
    streamStepStr C₀ (streamRunCode s X t P A) =
      if t < X * X then
        streamRunCode s X (t + 1)
          (P + streamPrimeIncrement (t / X) (t % X))
          (A + streamRootIncrement s (t / X) (t % X))
      else streamDoneCode (streamVerdict s P A) := by
  have hp : canonBits (divStr (encNat t) (encNat X)) = encNat (t / X) := by
    simp only [canonBits, decNat_divStr, decNat_encNat]
  have ha : canonBits (redStr (encNat t) (encNat X)) = encNat (t % X) := by
    rw [canonBits, decNat_redStr _ _ (by simpa using hX)]
    simp only [decNat_encNat]
  change streamAdvanceStr (pair s (pair (encNat X)
    (pair (encNat t) (pair (encNat P) (encNat A))))) = _
  simp only [streamAdvanceStr, pairFst_pair, pairSnd_pair]
  rw [hp, ha]
  simp only [streamPrimeIncrementStr_eq, streamRootIncrementStr_eq, canonBits, decNat_succBits,
    decNat_addBits, decNat_encNat, ltBits_eq_decide_decNat, decNat_mulBits,
    caseBit₀_cons, streamVerdictStr_eq]
  by_cases ht : t < X * X <;> simp [ht, streamRunCode, streamDoneCode]

/-- The width clamp bounds the state even on malformed strings. -/
theorem cutoffUnary_length_le (C₀ : ℕ) (s : List Bool) :
    (cutoffUnary C₀ s).length ≤ 128 * (38 + Nat.clog 2 C₀) + 768 * s.length := by
  have hc : ∃ m, cutoffExponentStr C₀ s = encNat m := by
    unfold cutoffExponentStr canonBits
    exact ⟨_, rfl⟩
  obtain ⟨m, hm⟩ := hc
  rw [cutoffUnary, hm, SparseIrred.Machine.binToUnaryStr,
    SparseIrred.Machine.binToUnaryStep_iterate, SparseGcd.length_unaryN]
  exact (Nat.min_le_left _ _).trans_eq (cutoffRuler_length C₀ s)

end SparseIrred.UpperBounds.Machine
