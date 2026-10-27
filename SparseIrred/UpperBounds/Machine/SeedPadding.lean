import SparseIrred.UpperBounds.Machine.SeedEncoding
import SparseIrred.UpperBounds.Machine.GuessVerify
import Mathlib.Data.Fin.Tuple.Take

/-!
# Exact probability under unused random suffix padding

A common polynomial random-tape length may exceed the number of bits used for a
particular input. Restricting a uniform tape to the required prefix preserves its
distribution, including the concrete Section 3.7 witness parser.
-/

open Complexity

namespace SparseIrred.UpperBounds

/-- The actual first `q` positions of a `B`-bit tape. -/
def seedPrefixEmbedding {q B : ℕ} (h : q ≤ B) : Fin q ↪ Fin B :=
  ⟨Fin.castLE h, Fin.castLE_injective h⟩

theorem scheduledSeed_prefix {q B : ℕ} (h : q ≤ B) (seed : Fin B → Bool) :
    Machine.scheduledSeed (seedPrefixEmbedding h) seed = Fin.take q h seed := rfl

/-- Boolean events depending on a prefix have the compact uniform probability. -/
theorem eventProb_seedPrefix {q B : ℕ} (h : q ≤ B)
    (verifier : (Fin q → Bool) → Bool) :
    eventProb (Finset.univ.filter fun seed : Fin B → Bool ↦
      verifier (Fin.take q h seed) = true) =
    eventProb (Finset.univ.filter fun seed : Fin q → Bool ↦ verifier seed = true) := by
  exact Machine.eventProb_scheduledSeed (seedPrefixEmbedding h) verifier

/-- The same prefix identity for arbitrary decidable finite predicates. -/
theorem eventProb_seedPrefix_pred {q B : ℕ} (h : q ≤ B)
    (R : (Fin q → Bool) → Prop) [DecidablePred R] :
    eventProb (Finset.univ.filter fun seed : Fin B → Bool ↦ R (Fin.take q h seed)) =
    eventProb (Finset.univ.filter R) := by
  simpa only [decide_eq_true_eq] using eventProb_seedPrefix h (fun seed ↦ decide (R seed))

/-- Exact uniform probability of a bitstring verifier that reads only a fixed prefix. -/
theorem eventProb_take_ofFn {q B : ℕ} (h : q ≤ B) (verifier : List Bool → Bool) :
    eventProb (Finset.univ.filter fun seed : Fin B → Bool ↦
      verifier ((List.ofFn seed).take q) = true) =
    eventProb (Finset.univ.filter fun seed : Fin q → Bool ↦
      verifier (List.ofFn seed) = true) := by
  simpa only [Fin.ofFn_take_eq_take_ofFn] using
    eventProb_seedPrefix h (fun seed ↦ verifier (List.ofFn seed))

/-- Pointwise suffix-insensitivity suffices for the probability padding argument. -/
theorem eventProb_of_suffix_ignored {q B : ℕ} (h : q ≤ B)
    (padded compact : List Bool → Bool)
    (heq : ∀ seed : Fin B → Bool,
      padded (List.ofFn seed) = compact ((List.ofFn seed).take q)) :
    eventProb (Finset.univ.filter fun seed : Fin B → Bool ↦
      padded (List.ofFn seed) = true) =
    eventProb (Finset.univ.filter fun seed : Fin q → Bool ↦
      compact (List.ofFn seed) = true) := by
  simp_rw [heq]
  exact eventProb_take_ofFn h compact

/-- The concrete witness-count probability is unchanged by an unused suffix. -/
theorem eventProb_seedPrimeChoices_padded (m B : ℕ) (h : 2 * m + 5 ≤ B)
    (R : (Fin 8 × PrimeWitness (2 ^ m) × Bool) → Prop) [DecidablePred R] :
    eventProb (Finset.univ.filter fun seed : Fin B → Bool ↦
      R (seedPrimeChoices m (Fin.take (2 * m + 5) h seed))) =
        (witnessCount R : ℚ) / 2 ^ (2 * m + 5) := by
  rw [eventProb_seedPrefix_pred h (fun seed ↦ R (seedPrimeChoices m seed)),
    eventProb_seedPrimeChoices]

end SparseIrred.UpperBounds
