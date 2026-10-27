import SparseIrred.UpperBounds.Machine.CutoffParameters
import SparseIrred.UpperBounds.Machine.EncodedVerifierFP

/-!
# A polynomial-time verifier on an input and a flat random seed

The seed layout is three mode bits, two equally wide candidate numerals, the root
tag bit, and one final fair bit. Any unused suffix is ignored. The width is computed
from the input in polynomial time and clamped on malformed inputs.
-/

open Polynomial Complexity SparseDiv SparseDiv.Appendix SparseDiv.StringArith SparseGcd

namespace SparseIrred.UpperBounds.Machine

/-- Execute one Section 3.7 branch from a flat string of random bits. -/
def randomSeedVerifier (C₀ : ℕ) (x seed : List Bool) : List Bool :=
  let m := (cutoffUnary C₀ x).length
  encodedVerifierStr x (seed.take 3) ((seed.drop 3).take m)
    ((seed.drop (3 + m)).take m) ((seed.drop (3 + 2 * m)).take 1)
    ((seed.drop (4 + 2 * m)).take 1)

theorem cobham_randomSeedVerifier (C₀ : ℕ) (hAKS : BinaryPrimalityInFP) {n : ℕ}
    {gx gs : (Fin n → List Bool) → List Bool} (hx : Cobham gx) (hs : Cobham gs) :
    Cobham fun v ↦ randomSeedVerifier C₀ (gx v) (gs v) := by
  have hm := cobham_cutoffUnary C₀ hx
  have h3 : Cobham (fun _ : Fin n → List Bool ↦ ([false, false, false] : List Bool)) :=
    Cobham.const _
  have h4 : Cobham (fun _ : Fin n → List Bool ↦ ([false, false, false, false] : List Bool)) :=
    Cobham.const _
  have h1 : Cobham (fun _ : Fin n → List Bool ↦ ([false] : List Bool)) := Cobham.const _
  have hp := Cobham.takeFn hm (Cobham.dropFn h3 hs)
  have ha := Cobham.takeFn hm (Cobham.dropFn (Cobham.appendFn h3 hm) hs)
  have hb := Cobham.takeFn h1
    (Cobham.dropFn (Cobham.appendFn h3 (Cobham.appendFn hm hm)) hs)
  have hc := Cobham.takeFn h1
    (Cobham.dropFn (Cobham.appendFn h4 (Cobham.appendFn hm hm)) hs)
  exact (cobham_encodedVerifierStr_comp hAKS hx (Cobham.takeFn h3 hs) hp ha hb hc).of_eq
    fun v ↦ by
      simp only [randomSeedVerifier, List.length_cons, List.length_nil, List.length_append]
      congr 3 <;> omega

/-- The ordinary paired-input verifier has a polynomial-time deterministic machine. -/
theorem randomSeedVerifier_mem_FP (C₀ : ℕ) (hAKS : BinaryPrimalityInFP) :
    (fun z ↦ randomSeedVerifier C₀ (pairFst z) (pairSnd z)) ∈ FP :=
  CobhamFP_subset_FP (cobham_randomSeedVerifier C₀ hAKS
    (cobham_pairFst_comp (.proj 0)) (cobham_pairSnd_comp (.proj 0)))

private theorem take_one_drop_eq (s : List Bool) (i : ℕ) (h : i < s.length) :
    (s.drop i).take 1 = [s.getD i false] := by
  rw [List.drop_eq_getElem_cons h, List.take_succ_cons, List.take_zero,
    List.getD_eq_getElem s false h]

/-- All malformed input strings reject independently of their supplied random seed. -/
theorem randomSeedVerifier_of_decode_none (C₀ : ℕ) (x seed : List Bool)
    (hx : decodeTerms x = none) : randomSeedVerifier C₀ x seed = [false] := by
  simp [randomSeedVerifier, encodedVerifierStr, validCode_eq_false_of_decode_none x hx]

/-- On legitimate inputs the flat parser has exactly the paper's field widths. -/
theorem randomSeedVerifier_eq (C₀ : ℕ) (x seed : List Bool) (l : ITerms)
    (hx : decodeTerms x = some l)
    (hlen : 2 * termCutoffExponent C₀ l + 5 ≤ seed.length) :
    randomSeedVerifier C₀ x seed =
      [executableEncodedDecision x (decNat (seed.take 3))
        (decNat ((seed.drop 3).take (termCutoffExponent C₀ l)))
        (decNat ((seed.drop (3 + termCutoffExponent C₀ l)).take (termCutoffExponent C₀ l)))
        (seed.getD (3 + 2 * termCutoffExponent C₀ l) false)
        (seed.getD (4 + 2 * termCutoffExponent C₀ l) false)] := by
  rw [randomSeedVerifier, cutoffUnary_eq C₀ x l hx, length_unaryN]
  rw [take_one_drop_eq _ _ (by omega), take_one_drop_eq _ _ (by omega), encodedVerifierStr_eq]

end SparseIrred.UpperBounds.Machine
