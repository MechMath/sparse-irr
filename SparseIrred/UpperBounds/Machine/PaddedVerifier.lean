import SparseIrred.UpperBounds.Machine.SeedAcceptance
import SparseIrred.UpperBounds.Machine.SeedPadding

/-!
# A polynomial-time padded input for the fixed-length guessing machine

Padding keeps the original input as its first framed component and makes the input
length large enough to supply every random bit used by Section 3.7. The verifier
unpacks that original input and ignores the unused random suffix. Its full-length
uniform acceptance probability is exactly the previously verified arithmetic one.
-/

open Complexity SparseDiv SparseDiv.Appendix SparseDiv.StringArith

namespace SparseIrred.UpperBounds.Machine

/-- Linear input padding that makes `|padded|+1` a sufficient random-seed length. -/
def padPrimeInput (C₀ : ℕ) (x : List Bool) : List Bool :=
  pair x (cutoffRuler C₀ x ++ cutoffRuler C₀ x ++ [false, false, false, false, false])

@[simp] theorem pairFst_padPrimeInput (C₀ : ℕ) (x : List Bool) :
    pairFst (padPrimeInput C₀ x) = x := by simp only [padPrimeInput, pairFst_pair]

theorem padPrimeInput_injective (C₀ : ℕ) : Function.Injective (padPrimeInput C₀) := by
  intro x y h
  simpa only [pairFst_padPrimeInput] using congrArg pairFst h

theorem cobham_padPrimeInput (C₀ : ℕ) {n : ℕ}
    {gx : (Fin n → List Bool) → List Bool} (hx : Cobham gx) :
    Cobham fun v ↦ padPrimeInput C₀ (gx v) :=
  cobham_pair_comp hx (Cobham.appendFn
    (Cobham.appendFn (cobham_cutoffRuler C₀ hx) (cobham_cutoffRuler C₀ hx))
    (Cobham.const _))

theorem padPrimeInput_mem_FP (C₀ : ℕ) : padPrimeInput C₀ ∈ FP :=
  CobhamFP_subset_FP (cobham_padPrimeInput C₀ (.proj 0))

theorem padPrimeInput_length (C₀ : ℕ) (x : List Bool) :
    (padPrimeInput C₀ x).length =
      256 * (38 + Nat.clog 2 C₀) + 1538 * x.length + 7 := by
  simp only [padPrimeInput, pair_length, List.length_append, cutoffRuler_length,
    List.length_cons, List.length_nil]
  omega

/-- The fixed-length guessing budget on the padded input covers every needed choice bit. -/
theorem primeChoice_bits_le_padded_length (C₀ : ℕ) (x : List Bool) :
    2 * encodedCutoffExponent C₀ x + 5 ≤ (padPrimeInput C₀ x).length + 1 := by
  have hb := encodedPrimeChoice_bits_le C₀ x
  rw [padPrimeInput_length]
  omega

/-- The flat verifier depends only on its input-dependent prefix of random bits. -/
theorem randomSeedVerifier_take_prefix (C₀ : ℕ) (x seed : List Bool) :
    randomSeedVerifier C₀ x (seed.take (2 * encodedCutoffExponent C₀ x + 5)) =
      randomSeedVerifier C₀ x seed := by
  cases hx : decodeTerms x with
  | none => rw [randomSeedVerifier_of_decode_none C₀ x _ hx,
      randomSeedVerifier_of_decode_none C₀ x _ hx]
  | some l =>
      have hm : encodedCutoffExponent C₀ x = termCutoffExponent C₀ l := by
        simp only [encodedCutoffExponent, hx]
      have h3 : min 3 (2 * termCutoffExponent C₀ l + 5) = 3 := by omega
      have hp : min (termCutoffExponent C₀ l) (2 * termCutoffExponent C₀ l + 5 - 3) =
          termCutoffExponent C₀ l := by omega
      have ha : min (termCutoffExponent C₀ l)
          (2 * termCutoffExponent C₀ l + 5 - (3 + termCutoffExponent C₀ l)) =
          termCutoffExponent C₀ l := by omega
      have hb : min 1 (2 * termCutoffExponent C₀ l + 5 -
          (3 + 2 * termCutoffExponent C₀ l)) = 1 := by omega
      have hc : min 1 (2 * termCutoffExponent C₀ l + 5 -
          (4 + 2 * termCutoffExponent C₀ l)) = 1 := by omega
      simp only [randomSeedVerifier, cutoffUnary_eq C₀ x l hx, SparseGcd.length_unaryN,
        hm, List.drop_take, List.take_take, h3, hp, ha, hb, hc]

/-- The ordinary paired-input verifier for a padded input and a supplied random seed. -/
def paddedPrimeVerifier (C₀ : ℕ) (z : List Bool) : List Bool :=
  randomSeedVerifier C₀ (pairFst (pairFst z)) (pairSnd z)

theorem paddedPrimeVerifier_mem_FP (C₀ : ℕ) (hAKS : BinaryPrimalityInFP) :
    paddedPrimeVerifier C₀ ∈ FP :=
  CobhamFP_subset_FP (cobham_randomSeedVerifier C₀ hAKS
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
theorem paddedPrimeVerifier_always_bool (C₀ : ℕ) (z : List Bool) :
    ∃ b : Bool, paddedPrimeVerifier C₀ z = [b] := by
  have hlen : (paddedPrimeVerifier C₀ z).length = 1 := by
    unfold paddedPrimeVerifier randomSeedVerifier
    exact encodedVerifierStr_length_one _ _ _ _ _ _
  exact List.length_eq_one_iff.mp hlen

/-- A polynomial-time deterministic decider is extracted from the verified one-bit transducer. -/
theorem exists_paddedPrimeVerifier_decider (C₀ : ℕ) (hAKS : BinaryPrimalityInFP) :
    ∃ (k : ℕ) (tm : TM k) (time : ℕ → ℕ) (d : ℕ),
      tm.DecidesInTime {z | paddedPrimeVerifier C₀ z = [true]} time ∧ time =O (· ^ d) := by
  obtain ⟨d, k, tm, time, hcompute, hpoly⟩ := paddedPrimeVerifier_mem_FP C₀ hAKS
  refine ⟨k, tm, time, d, ?_, hpoly⟩
  intro z
  obtain ⟨cfg, t, ht, hreach, hhalt, hout⟩ := hcompute z
  obtain ⟨b, hb⟩ := paddedPrimeVerifier_always_bool C₀ z
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

@[simp] theorem paddedPrimeVerifier_pair (C₀ : ℕ) (x seed : List Bool) :
    paddedPrimeVerifier C₀ (pair (padPrimeInput C₀ x) seed) =
      randomSeedVerifier C₀ x seed := by
  simp only [paddedPrimeVerifier, pairFst_pair, pairSnd_pair, pairFst_padPrimeInput]

/-- The complete padded random tape has exactly the Section 3 arithmetic acceptance probability. -/
theorem paddedPrimeVerifier_eventProb (C₀ : ℕ) (x : List Bool) :
    eventProb (Finset.univ.filter
      fun seed : Fin ((padPrimeInput C₀ x).length + 1) → Bool ↦
        paddedPrimeVerifier C₀ (pair (padPrimeInput C₀ x) (List.ofFn seed)) = [true]) =
      primeCountingAcceptance C₀ x := by
  simp only [paddedPrimeVerifier_pair]
  have hpadded := eventProb_take_ofFn (primeChoice_bits_le_padded_length C₀ x)
    (fun seed ↦ decide (randomSeedVerifier C₀ x seed = [true]))
  simp only [decide_eq_true_eq, randomSeedVerifier_take_prefix] at hpadded
  exact hpadded.trans (randomSeedVerifier_eventProb C₀ x)

end SparseIrred.UpperBounds.Machine
