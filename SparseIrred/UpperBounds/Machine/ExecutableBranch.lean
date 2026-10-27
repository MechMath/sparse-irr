import SparseIrred.UpperBounds.Machine.Preprocess
import SparseIrred.UpperBounds.Machine.ExecutableWitness
import SparseIrred.UpperBounds.Section3Conclusion

/-!
# Executable Section 3.7 branches on encoded sparse inputs

The decision function includes malformed-input rejection, signed-prime constants,
the content test, and the eight-mode majority procedure. All data definitions are
computable. The finite acceptance ratio is proved equal to the probability used in
the Section 3 conclusion. This establishes functional correctness, independently of
the remaining Turing-machine compilation and polynomial-time obligations.
-/

open Polynomial SparseDiv SparseDiv.Appendix

namespace SparseIrred.UpperBounds.Machine

/-- Compute the constant coefficient directly from the sparse term list. -/
def termConstantCoefficient (l : ITerms) : ℤ :=
  ((l.filter fun t ↦ t.2 = 0).map Prod.fst).sum

theorem termConstantCoefficient_eq (l : ITerms) :
    termConstantCoefficient l = (toPolyZ l).coeff 0 :=
  (coeff_toPolyZ l 0).symm

/-- The executable decision on decoded terms and one supplied random choice. -/
def executableTermDecision (l : ITerms) (mode p a : ℕ) (b coin : Bool) : Bool :=
  if degreeZ l = 0 then decide (termConstantCoefficient l).natAbs.Prime
  else if contentZ l = 1 then executablePrimeMajority l mode p a b coin
  else false

/-- The finite accepting-branch predicate for an arbitrary common candidate bound. -/
def executableTermBranch (l : ITerms) (X : ℕ)
    (w : Fin 8 × PrimeWitness X × Bool) : Prop :=
  executableTermDecision l w.1.val w.2.1.1.val w.2.1.2.1.val w.2.1.2.2 w.2.2 = true

instance (l : ITerms) (X : ℕ) : DecidablePred (executableTermBranch l X) :=
  fun _ ↦ inferInstanceAs (Decidable (_ = true))

/-- The exact ratio over all equally likely choices, including deterministic branches. -/
def executableTermAcceptance (C₀ : ℕ) (l : ITerms) : ℚ :=
  (witnessCount (executableTermBranch l (2 ^ termCutoffExponent C₀ l)) : ℚ) /
    (2 : ℚ) ^ (2 * termCutoffExponent C₀ l + 5)

/-- On nonconstant primitive inputs the term branch is the verified prime branch. -/
theorem executableTermBranch_eq_primeBranch (l : ITerms) (X : ℕ)
    (hd : degreeZ l ≠ 0) (hc : contentZ l = 1) :
    executableTermBranch l X = executablePrimeBranch l X := by
  funext w
  simp only [executableTermBranch, executableTermDecision, hd, hc, ↓reduceIte,
    executablePrimeBranch]

/-- Normalized raw terms give exactly the polynomial-level finite acceptance probability. -/
theorem executableTermAcceptance_eq (C₀ : ℕ) (l : ITerms) (hl : NormalizedZ l) :
    executableTermAcceptance C₀ l = polynomialPrimeCountingAcceptance C₀ (toPolyZ l) := by
  classical
  have hd := natDegree_toPolyZ_of_normalizedZ hl
  have hc := contentZ_eq_one_iff l hl
  have hm := termCutoffExponent_eq C₀ l hl
  have hcard :
      (Fintype.card (Fin 8 × PrimeWitness (2 ^ termCutoffExponent C₀ l) × Bool) : ℚ) =
        (2 : ℚ) ^ (2 * termCutoffExponent C₀ l + 5) := by
    exact_mod_cast primeWitness_choice_count (termCutoffExponent C₀ l)
  by_cases hdegree : degreeZ l = 0
  · by_cases hp : (termConstantCoefficient l).natAbs.Prime
    · have hcount : witnessCount (executableTermBranch l (2 ^ termCutoffExponent C₀ l)) =
          Fintype.card (Fin 8 × PrimeWitness (2 ^ termCutoffExponent C₀ l) × Bool) := by
        unfold witnessCount
        rw [Finset.filter_eq_self.mpr (by
          intro w _
          simp [executableTermBranch, executableTermDecision, hdegree, hp])]
        exact Finset.card_univ
      rw [executableTermAcceptance, hcount, hcard]
      simp [polynomialPrimeCountingAcceptance, hd, hdegree,
        ← termConstantCoefficient_eq, hp]
    · simp [executableTermAcceptance, witnessCount, executableTermBranch,
        executableTermDecision, hdegree, hp, polynomialPrimeCountingAcceptance, hd,
        ← termConstantCoefficient_eq]
  · by_cases hcontent : contentZ l = 1
    · have hprimitive := hc.mp hcontent
      simp only [executableTermAcceptance, executableTermBranch_eq_primeBranch l _ hdegree
          hcontent, executablePrimeBranch_eq, polynomialPrimeCountingAcceptance, hd,
        hdegree, hprimitive, ↓reduceIte, primeCountingCutoff]
      exact congrArg (fun m ↦
        (witnessCount (majorityGadget (positivePrimeWitness (2 ^ m))
          (negativePrimeWitness (toPolyZ l) (2 ^ m))) : ℚ) / (2 : ℚ) ^ (2 * m + 5)) hm
    · have hnot : ¬(toPolyZ l).IsPrimitive := mt hc.mpr hcontent
      simp [executableTermAcceptance, witnessCount, executableTermBranch,
        executableTermDecision, hdegree, hcontent, polynomialPrimeCountingAcceptance,
        hd, hnot]

/-- The executable branch on a binary input; decoding is part of this function. -/
def executableEncodedDecision (x : List Bool) (mode p a : ℕ) (b coin : Bool) : Bool :=
  match decodeTerms x with
  | none => false
  | some l => executableTermDecision l mode p a b coin

/-- Malformed strings may use a dummy choice width, since all their branches reject. -/
def encodedCutoffExponent (C₀ : ℕ) (x : List Bool) : ℕ :=
  match decodeTerms x with
  | none => 0
  | some l => termCutoffExponent C₀ l

/-- Exactly the paper's finite choice space at the width computed from the input. -/
abbrev EncodedPrimeChoice (C₀ : ℕ) (x : List Bool) :=
  Fin 8 × PrimeWitness (2 ^ encodedCutoffExponent C₀ x) × Bool

/-- Two fixed-width candidates, one root bit, three mode bits, and one padding bit. -/
theorem encodedPrimeChoice_card (C₀ : ℕ) (x : List Bool) :
    Fintype.card (EncodedPrimeChoice C₀ x) = 2 ^ (2 * encodedCutoffExponent C₀ x + 5) :=
  primeWitness_choice_count (encodedCutoffExponent C₀ x)

/-- Acceptance of a single finite branch on an encoded input. -/
def executableEncodedBranchAt (x : List Bool) (X : ℕ)
    (w : Fin 8 × PrimeWitness X × Bool) : Prop :=
  executableEncodedDecision x w.1.val w.2.1.1.val w.2.1.2.1.val w.2.1.2.2 w.2.2 = true

instance (x : List Bool) (X : ℕ) : DecidablePred (executableEncodedBranchAt x X) :=
  fun _ ↦ inferInstanceAs (Decidable (_ = true))

/-- Specialize the executable branch to the input's computed candidate range. -/
def executableEncodedBranch (C₀ : ℕ) (x : List Bool) : EncodedPrimeChoice C₀ x → Prop :=
  executableEncodedBranchAt x (2 ^ encodedCutoffExponent C₀ x)

instance (C₀ : ℕ) (x : List Bool) : DecidablePred (executableEncodedBranch C₀ x) :=
  fun _ ↦ inferInstanceAs (Decidable (_ = true))

/-- The exact acceptance ratio of the complete executable finite-branch procedure. -/
def executableEncodedAcceptance (C₀ : ℕ) (x : List Bool) : ℚ :=
  match decodeTerms x with
  | none => 0
  | some l => executableTermAcceptance C₀ l

/-- The acceptance definition is exactly accepting paths divided by all equiprobable paths. -/
theorem executableEncodedAcceptance_eq_ratio (C₀ : ℕ) (x : List Bool) :
    executableEncodedAcceptance C₀ x =
      (witnessCount (executableEncodedBranch C₀ x) : ℚ) /
        (2 : ℚ) ^ (2 * encodedCutoffExponent C₀ x + 5) := by
  classical
  cases hdecode : decodeTerms x with
  | none =>
      have hb (X : ℕ) : executableEncodedBranchAt x X = fun _ ↦ False := by
        funext w
        simp [executableEncodedBranchAt, executableEncodedDecision, hdecode]
      change executableEncodedAcceptance C₀ x =
        (witnessCount (executableEncodedBranchAt x (2 ^ encodedCutoffExponent C₀ x)) : ℚ) /
          (2 : ℚ) ^ (2 * encodedCutoffExponent C₀ x + 5)
      simp [hb, executableEncodedAcceptance, hdecode, witnessCount]
  | some l =>
      have hb (X : ℕ) : executableEncodedBranchAt x X = executableTermBranch l X := by
        funext w
        simp only [executableEncodedBranchAt, executableEncodedDecision, hdecode,
          executableTermBranch]
      change executableEncodedAcceptance C₀ x =
        (witnessCount (executableEncodedBranchAt x (2 ^ encodedCutoffExponent C₀ x)) : ℚ) /
          (2 : ℚ) ^ (2 * encodedCutoffExponent C₀ x + 5)
      simp only [hb, executableEncodedAcceptance, hdecode]
      have hm : termCutoffExponent C₀ l = encodedCutoffExponent C₀ x := by
        simp only [encodedCutoffExponent, hdecode]
      exact congrArg (fun m ↦ (witnessCount (executableTermBranch l (2 ^ m)) : ℚ) /
        (2 : ℚ) ^ (2 * m + 5)) hm

/-- The complete executable procedure realizes the precise probability in the final theorem. -/
theorem executableEncodedAcceptance_eq (C₀ : ℕ) (x : List Bool) :
    executableEncodedAcceptance C₀ x = primeCountingAcceptance C₀ x := by
  cases hdecode : decodeTerms x with
  | none =>
      simp [executableEncodedAcceptance, hdecode, primeCountingAcceptance,
        decodePoly_eq_map_decodeTerms]
  | some l =>
      have hl := ((decodeTerms_eq_some_iff x l).mp hdecode).1
      simpa only [executableEncodedAcceptance, primeCountingAcceptance,
        decodePoly_eq_map_decodeTerms, hdecode, Option.map_some] using
          executableTermAcceptance_eq C₀ l hl

/-- The verified executable branches decide the encoded irreducibility language by majority. -/
theorem executableEncodedAcceptance_gt_half_iff (C₀ : ℕ) (hC : 1 ≤ C₀)
    (hExternal : UniformPrimeIdealEstimate C₀) (x : List Bool) :
    executableEncodedAcceptance C₀ x > 1 / 2 ↔ x ∈ IrredLang := by
  rw [executableEncodedAcceptance_eq]
  exact primeCountingAcceptance_gt_half_iff_mem_IrredLang C₀ hC hExternal x

/-- The number of supplied random bits has a uniform linear bound in the input length. -/
theorem encodedCutoffExponent_le (C₀ : ℕ) (x : List Bool) :
    encodedCutoffExponent C₀ x ≤ 128 * (38 + Nat.clog 2 C₀) + 768 * x.length := by
  cases hdecode : decodeTerms x with
  | none => simp [encodedCutoffExponent, hdecode]
  | some l =>
      simpa only [encodedCutoffExponent, hdecode] using termCutoffExponent_le C₀ x l hdecode

/-- The total number of binary choices is linear in the actual encoded input length. -/
theorem encodedPrimeChoice_bits_le (C₀ : ℕ) (x : List Bool) :
    2 * encodedCutoffExponent C₀ x + 5 ≤
      256 * (38 + Nat.clog 2 C₀) + 1536 * x.length + 5 := by
  have h := encodedCutoffExponent_le C₀ x
  omega

end SparseIrred.UpperBounds.Machine
