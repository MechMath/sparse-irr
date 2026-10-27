import SparseIrred.UpperBounds.RawPrimeCountingDecision

/-!
# A uniform arithmetic conclusion for Section 3

The cited effective prime-ideal estimate is the external analytic premise. One
integer constant is chosen before any sparse input. The threshold criterion, its
majority form, and the linear witness-length bound are internal consequences.
-/

open Polynomial SparseDiv SparseDiv.Appendix

namespace SparseIrred.UpperBounds

/-- The prime-counting test, including the integer-ring boundary cases. -/
def rawPrimeCountingTest (C₀ : ℕ) (l : ITerms) : Prop :=
  if (toPolyZ l).natDegree = 0 then
    ((toPolyZ l).coeff 0).natAbs.Prime
  else
    (toPolyZ l).IsPrimitive ∧
      2 * primeRootSum (toPolyZ l) (primeCountingCutoff C₀ (toPolyZ l)) <
        3 * primeCountBelow (primeCountingCutoff C₀ (toPolyZ l))

/-- The same test expressed by the number of actual accepting witnesses. -/
def rawPrimeCountingMajority (C₀ : ℕ) (l : ITerms) : Prop :=
  if (toPolyZ l).natDegree = 0 then
    ((toPolyZ l).coeff 0).natAbs.Prime
  else
    (toPolyZ l).IsPrimitive ∧
      2 ^ (2 * inputCutoffExponent C₀ (toPolyZ l) + 5) <
        2 * witnessCount (majorityGadget
          (positivePrimeWitness (primeCountingCutoff C₀ (toPolyZ l)))
          (negativePrimeWitness (toPolyZ l) (primeCountingCutoff C₀ (toPolyZ l))))

/-- The Section 3 arithmetic conclusion with one constant for all raw inputs.
Only the cited effective prime-ideal estimate is assumed. -/
theorem section3_uniform_arithmetic_conclusion
    (hExternal : ∃ C : ℝ, 0 < C ∧ EffectivePrimeIdealEstimate (1 / 32) C) :
    ∃ C₀ : ℕ, 1 ≤ C₀ ∧ UniformPrimeIdealEstimate C₀ ∧ ∀ l : ITerms,
      (Irreducible (toPolyZ l) ↔ rawPrimeCountingTest C₀ l) ∧
      (Irreducible (toPolyZ l) ↔ rawPrimeCountingMajority C₀ l) ∧
      2 * inputCutoffExponent C₀ (toPolyZ l) + 5 ≤
        256 * (38 + Nat.clog 2 C₀) + 1536 * (encITerms l).length + 5 := by
  obtain ⟨C₀, hC, hEstimate⟩ := exists_integer_uniform_primeIdeal_estimate hExternal
  refine ⟨C₀, hC, hEstimate, fun l ↦ ?_⟩
  exact ⟨rawList_irreducible_iff_primeCounting_test C₀ l hC hEstimate,
    rawList_irreducible_iff_primeCounting_majority C₀ l hC hEstimate,
    rawList_primeCounting_choice_bits_le C₀ l⟩

end SparseIrred.UpperBounds
