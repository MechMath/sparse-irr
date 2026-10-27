import SparseIrred.UpperBounds.Machine.GeneralGapSeedAcceptance
import SparseIrred.UpperBounds.Machine.SeedPadding

/-!
# A polynomial-time padded input for the fixed-length guessing machine

Padding keeps the original input as its first framed component and makes the input
length large enough to supply every random bit used by Section 3.7. The verifier
unpacks that original input and ignores the unused random suffix. Its full-length
uniform acceptance probability is exactly the previously verified arithmetic one.
-/

open Complexity SparseDiv SparseDiv.Appendix SparseDiv.StringArith

open SparseIrred.UpperBounds.Machine
namespace SparseIrred.UpperBounds.GeneralGap

/-- Linear input padding that makes `|padded|+1` a sufficient random-seed length. -/
def padPrimeInput (r C₀ : ℕ) (x : List Bool) : List Bool :=
  pair x (cutoffRuler r C₀ x ++ cutoffRuler r C₀ x ++ [false, false, false, false, false])

@[simp] theorem pairFst_padPrimeInput (r C₀ : ℕ) (x : List Bool) :
    pairFst (padPrimeInput r C₀ x) = x := by simp only [padPrimeInput, pairFst_pair]

theorem padPrimeInput_injective (r C₀ : ℕ) : Function.Injective (padPrimeInput r C₀) := by
  intro x y h
  simpa only [pairFst_padPrimeInput] using congrArg pairFst h

theorem cobham_padPrimeInput (r C₀ : ℕ) {n : ℕ}
    {gx : (Fin n → List Bool) → List Bool} (hx : Cobham gx) :
    Cobham fun v ↦ padPrimeInput r C₀ (gx v) :=
  cobham_pair_comp hx (Cobham.appendFn
    (Cobham.appendFn (cobham_cutoffRuler r C₀ hx) (cobham_cutoffRuler r C₀ hx))
    (Cobham.const _))

theorem padPrimeInput_mem_FP (r C₀ : ℕ) : padPrimeInput r C₀ ∈ FP :=
  CobhamFP_subset_FP (cobham_padPrimeInput r C₀ (.proj 0))

theorem padPrimeInput_length (r C₀ : ℕ) (x : List Bool) :
    (padPrimeInput r C₀ x).length =
      256 * r * (38 + Nat.clog 2 C₀ + 2 * Nat.clog 2 r) + (1536 * r + 2) * x.length + 7 := by
  simp only [padPrimeInput, pair_length, List.length_append, cutoffRuler_length,
    List.length_cons, List.length_nil]
  nlinarith

/-- The fixed-length guessing budget on the padded input covers every needed choice bit. -/
theorem primeChoice_bits_le_padded_length (r C₀ : ℕ) (x : List Bool) :
    2 * encodedCutoffExponent r C₀ x + 5 ≤ (padPrimeInput r C₀ x).length + 1 := by
  have hb := encodedPrimeChoice_bits_le r C₀ x
  rw [padPrimeInput_length]
  nlinarith

/-- The flat verifier depends only on its input-dependent prefix of random bits. -/
theorem randomSeedVerifier_take_prefix (r C₀ : ℕ) (x seed : List Bool) :
    randomSeedVerifier r C₀ x (seed.take (2 * encodedCutoffExponent r C₀ x + 5)) =
      randomSeedVerifier r C₀ x seed := by
  cases hx : decodeTerms x with
  | none => rw [randomSeedVerifier_of_decode_none r C₀ x _ hx,
      randomSeedVerifier_of_decode_none r C₀ x _ hx]
  | some l =>
      have hm : encodedCutoffExponent r C₀ x = termCutoffExponent r C₀ l := by
        simp only [encodedCutoffExponent, hx]
      have h3 : min 3 (2 * termCutoffExponent r C₀ l + 5) = 3 := by omega
      have hp : min (termCutoffExponent r C₀ l) (2 * termCutoffExponent r C₀ l + 5 - 3) =
          termCutoffExponent r C₀ l := by omega
      have ha : min (termCutoffExponent r C₀ l)
          (2 * termCutoffExponent r C₀ l + 5 - (3 + termCutoffExponent r C₀ l)) =
          termCutoffExponent r C₀ l := by omega
      have hb : min 1 (2 * termCutoffExponent r C₀ l + 5 -
          (3 + 2 * termCutoffExponent r C₀ l)) = 1 := by omega
      have hc : min 1 (2 * termCutoffExponent r C₀ l + 5 -
          (4 + 2 * termCutoffExponent r C₀ l)) = 1 := by omega
      simp only [randomSeedVerifier, cutoffUnary_eq r C₀ x l hx, SparseGcd.length_unaryN,
        hm, List.drop_take, List.take_take, h3, hp, ha, hb, hc]

/-- The ordinary paired-input verifier for a padded input and a supplied random seed. -/
def paddedPrimeVerifier (r C₀ : ℕ) (z : List Bool) : List Bool :=
  randomSeedVerifier r C₀ (pairFst (pairFst z)) (pairSnd z)

theorem paddedPrimeVerifier_mem_FP (r C₀ : ℕ) (hAKS : BinaryPrimalityInFP) :
    paddedPrimeVerifier r C₀ ∈ FP :=
  CobhamFP_subset_FP (cobham_randomSeedVerifier r C₀ hAKS
    (cobham_pairFst_comp (cobham_pairFst_comp (.proj 0))) (cobham_pairSnd_comp (.proj 0)))

private theorem caseBit_length_one (flag x y : List Bool)
    (hx : x.length = 1) (hy : y.length = 1) : (caseBit₀ flag x y).length = 1 := by
  rcases SparseGcd.caseBit₀_cases flag x y with h | h <;> rw [h] <;> assumption

private theorem primeMajorityStr_length_one (s mode p a b coin : List Bool) :
    (primeMajorityStr s mode p a b coin).length = 1 := by
  unfold primeMajorityStr
  apply caseBit_length_one
  · exact Cobham.orBit_length _ _
  · apply caseBit_length_one
    · exact SparseGcd.andBit_length _ _
    · unfold notBit
      exact caseBit_length_one _ _ _ rfl rfl

private theorem encodedVerifierStr_length_one (s mode p a b coin : List Bool) :
    (encodedVerifierStr s mode p a b coin).length = 1 := by
  unfold encodedVerifierStr
  apply caseBit_length_one
  · apply caseBit_length_one
    · rfl
    · exact caseBit_length_one _ _ _ (primeMajorityStr_length_one _ _ _ _ _ _) rfl
  · rfl

/-- Every string, including malformed inputs and short seeds, produces exactly one Boolean bit. -/
theorem paddedPrimeVerifier_always_bool (r C₀ : ℕ) (z : List Bool) :
    ∃ b : Bool, paddedPrimeVerifier r C₀ z = [b] := by
  have hlen : (paddedPrimeVerifier r C₀ z).length = 1 := by
    unfold paddedPrimeVerifier randomSeedVerifier
    exact encodedVerifierStr_length_one _ _ _ _ _ _
  exact List.length_eq_one_iff.mp hlen

/-- A polynomial-time deterministic decider is extracted from the verified one-bit transducer. -/
theorem exists_paddedPrimeVerifier_decider (r C₀ : ℕ) (hAKS : BinaryPrimalityInFP) :
    ∃ (k : ℕ) (tm : TM k) (time : ℕ → ℕ) (d : ℕ),
      tm.DecidesInTime {z | paddedPrimeVerifier r C₀ z = [true]} time ∧ time =O (· ^ d) := by
  obtain ⟨d, k, tm, time, hcompute, hpoly⟩ := paddedPrimeVerifier_mem_FP r C₀ hAKS
  refine ⟨k, tm, time, d, ?_, hpoly⟩
  intro z
  obtain ⟨cfg, t, ht, hreach, hhalt, hout⟩ := hcompute z
  obtain ⟨b, hb⟩ := paddedPrimeVerifier_always_bool r C₀ z
  rw [hb] at hout
  have hcell := hout.1 0 (by simp)
  simp only [zero_add, List.getElem_cons_zero] at hcell
  refine ⟨cfg, t, ht, hreach, hhalt, ?_, ?_⟩
  · intro hz
    have hbt : b = true := by simpa only [Set.mem_ofPred_eq, hb, List.cons.injEq, and_true] using hz
    simpa only [hbt, Γ.ofBool] using hcell
  · intro hz
    have hbf : b = false := by
      cases b
      · rfl
      · exact False.elim (hz hb)
    simpa only [hbf, Γ.ofBool] using hcell

@[simp] theorem paddedPrimeVerifier_pair (r C₀ : ℕ) (x seed : List Bool) :
    paddedPrimeVerifier r C₀ (pair (padPrimeInput r C₀ x) seed) =
      randomSeedVerifier r C₀ x seed := by
  simp only [paddedPrimeVerifier, pairFst_pair, pairSnd_pair, pairFst_padPrimeInput]

/-- The complete padded random tape has exactly the Section 3 arithmetic acceptance probability. -/
theorem paddedPrimeVerifier_eventProb (r C₀ : ℕ) (x : List Bool) :
    eventProb (Finset.univ.filter
      fun seed : Fin ((padPrimeInput r C₀ x).length + 1) → Bool ↦
        paddedPrimeVerifier r C₀ (pair (padPrimeInput r C₀ x) (List.ofFn seed)) = [true]) =
      primeCountingAcceptance r C₀ x := by
  simp only [paddedPrimeVerifier_pair]
  have hpadded := eventProb_take_ofFn (primeChoice_bits_le_padded_length r C₀ x)
    (fun seed ↦ decide (randomSeedVerifier r C₀ x seed = [true]))
  simp only [decide_eq_true_eq, randomSeedVerifier_take_prefix] at hpadded
  exact hpadded.trans (randomSeedVerifier_eventProb r C₀ x)

end SparseIrred.UpperBounds.GeneralGap
