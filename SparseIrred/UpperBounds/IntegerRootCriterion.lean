import SparseIrred.UpperBounds.FactorStatistic
import SparseIrred.UpperBounds.ModularRoots
import SparseIrred.UpperBounds.MajorityCount
import SparseIrred.UpperBounds.PrimeCutoff

/-!
# Prime-root counts and the integer irreducibility threshold

The definitions count primes strictly below `X`, matching the streaming loop of
Section 3.6. The numerical implication from a quarter-unit approximation is proved;
the approximation itself, which requires the analytic number theory in Sections
3.1--3.5, is not assumed to have been established by the repository.
-/

open Polynomial
open scoped BigOperators

namespace SparseIrred.UpperBounds

/-- `ν_f(p)+μ_f(p)` at primes, and zero elsewhere. -/
noncomputable def primeRootWeight (f : ℤ[X]) (p : ℕ) : ℕ := by
  classical
  exact if hp : p.Prime then
    let _ : Fact p.Prime := ⟨hp⟩
    let g := f.map (Int.castRingHom (ZMod p))
    rootCount g + multipleRootCount g
  else 0

/-- `P(X)` with the strict cutoff used by the actual loop. -/
def primeCountBelow (X : ℕ) : ℕ := ((Finset.range X).filter Nat.Prime).card

/-- `A_f(X)` with the same strict cutoff. -/
noncomputable def primeRootSum (f : ℤ[X]) (X : ℕ) : ℕ :=
  ∑ p ∈ (Finset.range X).filter Nat.Prime, primeRootWeight f p

/-- Uniform local counter bound, also at primes dividing the leading coefficient. -/
theorem primeRootWeight_le (f : ℤ[X]) (hf : f.IsPrimitive) (p : ℕ) :
    primeRootWeight f p ≤ 2 * f.natDegree := by
  classical
  unfold primeRootWeight
  split_ifs with hp
  · have h := primitive_modular_root_bounds f hf p hp
    dsimp at h ⊢
    omega
  · omega

theorem primeCountBelow_le (X : ℕ) : primeCountBelow X ≤ X := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

/-- The two counters need at most the bits of `X` and `2 n X`, respectively. -/
theorem prime_counter_bounds (f : ℤ[X]) (hf : f.IsPrimitive) (X : ℕ) :
    primeCountBelow X ≤ X ∧ primeRootSum f X ≤ 2 * f.natDegree * X := by
  refine ⟨primeCountBelow_le X, ?_⟩
  calc
    primeRootSum f X ≤ ∑ _p ∈ (Finset.range X).filter Nat.Prime, 2 * f.natDegree := by
      exact Finset.sum_le_sum (fun p _ ↦ primeRootWeight_le f hf p)
    _ = 2 * f.natDegree * primeCountBelow X := by
      simp [primeCountBelow, Nat.mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left _ (primeCountBelow_le X)

/-- Corollary 15's arithmetic step. The analytic approximation is an explicit input,
not a custom axiom or a theorem asserted without proof. -/
theorem integer_irreducible_iff_root_threshold_of_approximation (f : ℤ[X])
    (hf : f.IsPrimitive) (hdeg : 0 < f.natDegree) (X : ℕ)
    (hP : 0 < primeCountBelow X)
    (happrox : |(primeRootSum f X : ℝ) / primeCountBelow X -
      factorStatistic (f.map (Int.castRingHom ℚ))| < 1 / 4) :
    Irreducible f ↔ 2 * primeRootSum f X < 3 * primeCountBelow X := by
  have hdegQ : 0 < (f.map (Int.castRingHom ℚ)).natDegree := by
    rwa [Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int _)]
  rw [← integer_factorStatistic_eq_one_iff f hf]
  exact (root_threshold_iff _ _ _ hP (factorStatistic_bounds _ hdegQ).1 happrox).symm

end SparseIrred.UpperBounds
