import SparseIrred.UpperBounds.Machine.RandomSeedVerifier
import SparseIrred.UpperBounds.Machine.SeedEncoding

/-!
# Exact acceptance probability of the polynomial-time random-seed verifier

This connects the actual string parser and verifier to the already proved arithmetic
acceptance probability. It does not assume correctness of the verifier as an interface.
-/

open Complexity SparseDiv SparseDiv.Appendix

namespace SparseIrred.UpperBounds.Machine

/-- On the exact random width, the string program computes the concrete finite branch. -/
theorem randomSeedVerifier_ofFn (C₀ : ℕ) (x : List Bool)
    (seed : Fin (2 * encodedCutoffExponent C₀ x + 5) → Bool) :
    randomSeedVerifier C₀ x (List.ofFn seed) =
      [let w := seedPrimeChoices (encodedCutoffExponent C₀ x) seed
       executableEncodedDecision x w.1.val w.2.1.1.val w.2.1.2.1.val w.2.1.2.2 w.2.2] := by
  cases hx : decodeTerms x with
  | none =>
      simp [randomSeedVerifier_of_decode_none C₀ x _ hx, executableEncodedDecision, hx]
  | some l =>
      have hm : encodedCutoffExponent C₀ x = termCutoffExponent C₀ l := by
        simp [encodedCutoffExponent, hx]
      have h := randomSeedVerifier_eq C₀ x (List.ofFn seed) l hx (by
        simp only [List.length_ofFn, hm]; exact le_rfl)
      simpa only [seedPrimeChoices, ← hm] using h

/-- Uniform random bits give exactly the probability used by the final Section 3 theorem. -/
theorem randomSeedVerifier_eventProb (C₀ : ℕ) (x : List Bool) :
    eventProb (Finset.univ.filter fun seed : Fin (2 * encodedCutoffExponent C₀ x + 5) → Bool ↦
      randomSeedVerifier C₀ x (List.ofFn seed) = [true]) = primeCountingAcceptance C₀ x := by
  have hevent :
      (Finset.univ.filter fun seed : Fin (2 * encodedCutoffExponent C₀ x + 5) → Bool ↦
        randomSeedVerifier C₀ x (List.ofFn seed) = [true]) =
      Finset.univ.filter (fun seed ↦ executableEncodedBranch C₀ x
        (seedPrimeChoices (encodedCutoffExponent C₀ x) seed)) := by
    ext seed
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [randomSeedVerifier_ofFn]
    change [_] = [true] ↔ _ = true
    simp only [List.cons.injEq, and_true]
  rw [hevent, eventProb_seedPrimeChoices, ← executableEncodedAcceptance_eq_ratio,
    executableEncodedAcceptance_eq]

end SparseIrred.UpperBounds.Machine
