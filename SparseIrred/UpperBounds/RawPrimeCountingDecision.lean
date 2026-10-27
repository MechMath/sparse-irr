import SparseIrred.UpperBounds.PrimeAverageInstantiation
import SparseIrred.UpperBounds.IntegerBoundary
import SparseIrred.UpperBounds.RawInputBounds

/-!
# The conditional prime-counting test on raw sparse input

The arithmetic decision criterion is connected to the original sparse term-list
representation, including constants and nonprimitive inputs. The only analytic
premise is the already explicit uniform prime-ideal estimate.
-/

open Polynomial SparseDiv SparseDiv.Appendix

namespace SparseIrred.UpperBounds

/-- The Section 3 threshold, with integer boundary cases, for every raw sparse
term list. Cancellations and repeated exponents are interpreted by `toPolyZ`. -/
theorem rawList_irreducible_iff_primeCounting_test (C₀ : ℕ) (l : ITerms)
    (hC : 1 ≤ C₀) (hExternal : UniformPrimeIdealEstimate C₀) :
    Irreducible (toPolyZ l) ↔
      if (toPolyZ l).natDegree = 0 then
        ((toPolyZ l).coeff 0).natAbs.Prime
      else
        (toPolyZ l).IsPrimitive ∧
          2 * primeRootSum (toPolyZ l)
              (primeCountingCutoff C₀ (toPolyZ l)) <
            3 * primeCountBelow (primeCountingCutoff C₀ (toPolyZ l)) := by
  let f := toPolyZ l
  change Irreducible f ↔
    if f.natDegree = 0 then (f.coeff 0).natAbs.Prime else
      f.IsPrimitive ∧ 2 * primeRootSum f (primeCountingCutoff C₀ f) <
        3 * primeCountBelow (primeCountingCutoff C₀ f)
  by_cases hdegree : f.natDegree = 0
  · simpa [hdegree] using integer_irreducible_boundary f
  · have hpos : 0 < f.natDegree := Nat.pos_of_ne_zero hdegree
    have hboundary := integer_irreducible_iff_primitive_and_rational f hpos
    rw [hboundary]
    simp only [hdegree, ↓reduceIte]
    constructor
    · rintro ⟨hf, hq⟩
      refine ⟨hf, ?_⟩
      apply (integer_irreducible_iff_primeCounting_threshold_of_uniform_estimate
        C₀ f hC hf hpos hExternal).mp
      exact hboundary.mpr ⟨hf, hq⟩
    · rintro ⟨hf, hthreshold⟩
      exact hboundary.mp ((integer_irreducible_iff_primeCounting_threshold_of_uniform_estimate
        C₀ f hC hf hpos hExternal).mpr hthreshold)

/-- The majority-witness form of the raw-input decision test. -/
theorem rawList_irreducible_iff_primeCounting_majority (C₀ : ℕ) (l : ITerms)
    (hC : 1 ≤ C₀) (hExternal : UniformPrimeIdealEstimate C₀) :
    Irreducible (toPolyZ l) ↔
      if (toPolyZ l).natDegree = 0 then
        ((toPolyZ l).coeff 0).natAbs.Prime
      else
        (toPolyZ l).IsPrimitive ∧
          2 ^ (2 * inputCutoffExponent C₀ (toPolyZ l) + 5) <
            2 * witnessCount (majorityGadget
              (positivePrimeWitness (primeCountingCutoff C₀ (toPolyZ l)))
              (negativePrimeWitness (toPolyZ l) (primeCountingCutoff C₀ (toPolyZ l)))) := by
  apply Iff.trans (rawList_irreducible_iff_primeCounting_test C₀ l hC hExternal)
  by_cases hdegree : (toPolyZ l).natDegree = 0
  · simp [hdegree]
  · simp only [hdegree, ↓reduceIte]
    constructor
    · rintro ⟨hf, hthreshold⟩
      exact ⟨hf, (primeCounting_majority_iff_threshold C₀ (toPolyZ l)).mpr hthreshold⟩
    · rintro ⟨hf, hmajority⟩
      exact ⟨hf, (primeCounting_majority_iff_threshold C₀ (toPolyZ l)).mp hmajority⟩

/-- The number of majority-witness bits is linear in the original term-list code. -/
theorem rawList_primeCounting_choice_bits_le (C₀ : ℕ) (l : ITerms) :
    2 * inputCutoffExponent C₀ (toPolyZ l) + 5 ≤
      256 * (38 + Nat.clog 2 C₀) + 1536 * (encITerms l).length + 5 := by
  have h := inputCutoffExponent_le_raw_length C₀ l
  omega

end SparseIrred.UpperBounds
