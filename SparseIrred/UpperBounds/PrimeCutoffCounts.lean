import SparseIrred.UpperBounds.IntegerRootCriterion
import SparseIrred.UpperBounds.SparseInputBounds
import Mathlib.NumberTheory.PrimeCounting

/-!
# Matching the inclusive analytic cutoff with the strict streaming cutoff

The analytic estimates count primes at most `X`; fixed-width witnesses and the
streaming loop use primes less than `X`. At the selected power-of-two cutoff the
endpoint is composite, so these conventions give exactly the same counts.
-/

namespace SparseIrred.UpperBounds

theorem primeCountBelow_eq_primeCounting' (X : ℕ) :
    primeCountBelow X = X.primeCounting' := by
  rw [Nat.primeCounting', Nat.count_eq_card_filter_range]
  rfl

theorem primeCountBelow_succ_of_not_prime (X : ℕ) (hX : ¬X.Prime) :
    primeCountBelow (X + 1) = primeCountBelow X := by
  simp [primeCountBelow, Finset.range_add_one, Finset.filter_insert, hX]

theorem primeRootSum_succ_of_not_prime (f : Polynomial ℤ) (X : ℕ) (hX : ¬X.Prime) :
    primeRootSum f (X + 1) = primeRootSum f X := by
  simp [primeRootSum, Finset.range_add_one, Finset.filter_insert, hX]

theorem primeCountBelow_eq_primeCounting_of_not_prime (X : ℕ) (hX : ¬X.Prime) :
    primeCountBelow X = X.primeCounting := by
  rw [Nat.primeCounting_eq_primeCounting'_succ,
    ← primeCountBelow_eq_primeCounting', primeCountBelow_succ_of_not_prime X hX]

theorem primeCountBelow_pos (X : ℕ) (hX : 2 < X) : 0 < primeCountBelow X := by
  apply Finset.card_pos.mpr
  exact ⟨2, by simp [hX, Nat.prime_two]⟩

/-- Powers of two used by the majority witnesses have a composite endpoint. -/
theorem binary_cutoff_counts (f : Polynomial ℤ) (m : ℕ) (hm : 2 ≤ m) :
    primeCountBelow (2 ^ m) = (2 ^ m).primeCounting ∧
      primeRootSum f (2 ^ m + 1) = primeRootSum f (2 ^ m) := by
  have hnp : ¬(2 ^ m).Prime := Nat.Prime.not_prime_pow hm
  exact ⟨primeCountBelow_eq_primeCounting_of_not_prime _ hnp,
    primeRootSum_succ_of_not_prime f _ hnp⟩

/-- The manuscript's actual input-dependent cutoff has at least two exponent bits. -/
theorem inputCutoffExponent_ge (C₀ : ℕ) (f : Polynomial ℤ) (hC : 1 ≤ C₀)
    (hf : 0 < f.natDegree) : 2560 ≤ inputCutoffExponent C₀ f := by
  have := cutoffLog_ge_twenty C₀ f.natDegree (inputDelta f) hC hf
  unfold inputCutoffExponent
  omega

theorem inputCutoff_counts (C₀ : ℕ) (f : Polynomial ℤ) (hC : 1 ≤ C₀)
    (hf : 0 < f.natDegree) :
    primeCountBelow (2 ^ inputCutoffExponent C₀ f) =
        (2 ^ inputCutoffExponent C₀ f).primeCounting ∧
      primeRootSum f (2 ^ inputCutoffExponent C₀ f + 1) =
        primeRootSum f (2 ^ inputCutoffExponent C₀ f) :=
  binary_cutoff_counts f _ (by have := inputCutoffExponent_ge C₀ f hC hf; omega)

end SparseIrred.UpperBounds
