import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Counting the exceptional rational primes

The last step in Lemma 3.1 of the prime-counting note converts an integer size
bound into a bound on the number of distinct prime divisors. The discriminant
size bound itself is a separate algebraic-number-theoretic obligation.
-/

namespace SparseIrred.UpperBounds

/-- Distinct prime divisors contribute at least one factor of two each. -/
theorem two_pow_primeFactors_card_le (N : ℕ) (hN : N ≠ 0) :
    2 ^ N.primeFactors.card ≤ N := by
  calc
    _ = ∏ _p ∈ N.primeFactors, (2 : ℕ) := by simp
    _ ≤ ∏ p ∈ N.primeFactors, p := by
      apply Finset.prod_le_prod
      · intro _ _
        omega
      · intro p hp
        exact (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) (Nat.prod_primeFactors_dvd N)

/-- A nonzero integer has at most `floor(log₂ |Z|)` distinct rational prime divisors. -/
theorem integer_primeFactors_card_le_log2 (Z : ℤ) (hZ : Z ≠ 0) :
    Z.natAbs.primeFactors.card ≤ Z.natAbs.log2 := by
  have hN : Z.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hZ
  exact (Nat.le_log2 hN).mpr (two_pow_primeFactors_card_le _ hN)

/-- The exceptional-prime cardinality conclusion follows from a binary size bound. -/
theorem exceptional_prime_card_bound (Z : ℤ) (hZ : Z ≠ 0) (n Δ : ℕ)
    (hsize : Z.natAbs ≤ 2 ^ (2 * n * Δ)) :
    Z.natAbs.primeFactors.card ≤ 2 * n * Δ := by
  have hpow := (two_pow_primeFactors_card_le Z.natAbs (Int.natAbs_ne_zero.mpr hZ)).trans hsize
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hpow

end SparseIrred.UpperBounds
