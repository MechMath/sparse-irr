import SparseIrred.UpperBounds.GeneralGapAcceptance
import SparseIrred.UpperBounds.Machine.GeneralGapParameters
import SparseIrred.UpperBounds.Machine.ExecutableBranch

open Polynomial SparseDiv SparseDiv.Appendix
open SparseIrred.UpperBounds.Machine
namespace SparseIrred.UpperBounds.GeneralGap

/-- The exact ratio over all equally likely choices, including deterministic branches. -/
def executableTermAcceptance (r C₀ : ℕ) (l : ITerms) : ℚ :=
  (witnessCount (executableTermBranch l (2 ^ termCutoffExponent r C₀ l)) : ℚ) /
    (2 : ℚ) ^ (2 * termCutoffExponent r C₀ l + 5)

/-- Normalized raw terms give exactly the polynomial-level finite acceptance probability. -/
theorem executableTermAcceptance_eq (r C₀ : ℕ) (l : ITerms) (hl : NormalizedZ l) :
    executableTermAcceptance r C₀ l = polynomialPrimeCountingAcceptance r C₀ (toPolyZ l) := by
  classical
  have hd := natDegree_toPolyZ_of_normalizedZ hl
  have hc := contentZ_eq_one_iff l hl
  have hm := termCutoffExponent_eq r C₀ l hl
  have hcard :
      (Fintype.card (Fin 8 × PrimeWitness (2 ^ termCutoffExponent r C₀ l) × Bool) : ℚ) =
        (2 : ℚ) ^ (2 * termCutoffExponent r C₀ l + 5) := by
    exact_mod_cast primeWitness_choice_count (termCutoffExponent r C₀ l)
  by_cases hdegree : degreeZ l = 0
  · by_cases hp : (termConstantCoefficient l).natAbs.Prime
    · have hcount : witnessCount (executableTermBranch l (2 ^ termCutoffExponent r C₀ l)) =
          Fintype.card (Fin 8 × PrimeWitness (2 ^ termCutoffExponent r C₀ l) × Bool) := by
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
        hdegree, hprimitive, ↓reduceIte, scaledPrimeCountingCutoff]
      exact congrArg (fun m ↦
        (witnessCount (majorityGadget (positivePrimeWitness (2 ^ m))
          (negativePrimeWitness (toPolyZ l) (2 ^ m))) : ℚ) / (2 : ℚ) ^ (2 * m + 5)) hm
    · have hnot : ¬(toPolyZ l).IsPrimitive := mt hc.mpr hcontent
      simp [executableTermAcceptance, witnessCount, executableTermBranch,
        executableTermDecision, hdegree, hcontent, polynomialPrimeCountingAcceptance,
        hd, hnot]

/-- Malformed strings may use a dummy choice width, since all their branches reject. -/
def encodedCutoffExponent (r C₀ : ℕ) (x : List Bool) : ℕ :=
  match decodeTerms x with
  | none => 0
  | some l => termCutoffExponent r C₀ l

/-- Exactly the paper's finite choice space at the width computed from the input. -/
abbrev EncodedPrimeChoice (r C₀ : ℕ) (x : List Bool) :=
  Fin 8 × PrimeWitness (2 ^ encodedCutoffExponent r C₀ x) × Bool

/-- Two fixed-width candidates, one root bit, three mode bits, and one padding bit. -/
theorem encodedPrimeChoice_card (r C₀ : ℕ) (x : List Bool) :
    Fintype.card (EncodedPrimeChoice r C₀ x) = 2 ^ (2 * encodedCutoffExponent r C₀ x + 5) :=
  primeWitness_choice_count (encodedCutoffExponent r C₀ x)

/-- Specialize the executable branch to the input's computed candidate range. -/
def executableEncodedBranch (r C₀ : ℕ) (x : List Bool) : EncodedPrimeChoice r C₀ x → Prop :=
  executableEncodedBranchAt x (2 ^ encodedCutoffExponent r C₀ x)

instance (r C₀ : ℕ) (x : List Bool) : DecidablePred (executableEncodedBranch r C₀ x) :=
  fun _ ↦ inferInstanceAs (Decidable (_ = true))

/-- The exact acceptance ratio of the complete executable finite-branch procedure. -/
def executableEncodedAcceptance (r C₀ : ℕ) (x : List Bool) : ℚ :=
  match decodeTerms x with
  | none => 0
  | some l => executableTermAcceptance r C₀ l

/-- The acceptance definition is exactly accepting paths divided by all equiprobable paths. -/
theorem executableEncodedAcceptance_eq_ratio (r C₀ : ℕ) (x : List Bool) :
    executableEncodedAcceptance r C₀ x =
      (witnessCount (executableEncodedBranch r C₀ x) : ℚ) /
        (2 : ℚ) ^ (2 * encodedCutoffExponent r C₀ x + 5) := by
  classical
  cases hdecode : decodeTerms x with
  | none =>
      have hb (X : ℕ) : executableEncodedBranchAt x X = fun _ ↦ False := by
        funext w
        simp [executableEncodedBranchAt, executableEncodedDecision, hdecode]
      change executableEncodedAcceptance r C₀ x =
        (witnessCount (executableEncodedBranchAt x (2 ^ encodedCutoffExponent r C₀ x)) : ℚ) /
          (2 : ℚ) ^ (2 * encodedCutoffExponent r C₀ x + 5)
      simp [hb, executableEncodedAcceptance, hdecode, witnessCount]
  | some l =>
      have hb (X : ℕ) : executableEncodedBranchAt x X = executableTermBranch l X := by
        funext w
        simp only [executableEncodedBranchAt, executableEncodedDecision, hdecode,
          executableTermBranch]
      change executableEncodedAcceptance r C₀ x =
        (witnessCount (executableEncodedBranchAt x (2 ^ encodedCutoffExponent r C₀ x)) : ℚ) /
          (2 : ℚ) ^ (2 * encodedCutoffExponent r C₀ x + 5)
      simp only [hb, executableEncodedAcceptance, hdecode]
      have hm : termCutoffExponent r C₀ l = encodedCutoffExponent r C₀ x := by
        simp only [encodedCutoffExponent, hdecode]
      exact congrArg (fun m ↦ (witnessCount (executableTermBranch l (2 ^ m)) : ℚ) /
        (2 : ℚ) ^ (2 * m + 5)) hm

/-- The complete executable procedure realizes the precise probability in the final theorem. -/
theorem executableEncodedAcceptance_eq (r C₀ : ℕ) (x : List Bool) :
    executableEncodedAcceptance r C₀ x = primeCountingAcceptance r C₀ x := by
  cases hdecode : decodeTerms x with
  | none =>
      simp [executableEncodedAcceptance, hdecode, primeCountingAcceptance,
        decodePoly_eq_map_decodeTerms]
  | some l =>
      have hl := ((decodeTerms_eq_some_iff x l).mp hdecode).1
      simpa only [executableEncodedAcceptance, primeCountingAcceptance,
        decodePoly_eq_map_decodeTerms, hdecode, Option.map_some] using
          executableTermAcceptance_eq r C₀ l hl

/-- The verified executable branches decide the encoded irreducibility language by majority. -/
theorem executableEncodedAcceptance_gt_half_iff (r C₀ : ℕ) (hr : 1 ≤ r) (hC : 1 ≤ C₀)
    (hExternal : ScaledPrimeIdealEstimate r C₀) (x : List Bool) :
    executableEncodedAcceptance r C₀ x > 1 / 2 ↔ x ∈ IrredLang := by
  rw [executableEncodedAcceptance_eq]
  exact primeCountingAcceptance_gt_half_iff_mem_IrredLang r C₀ hr hC hExternal x

/-- The number of supplied random bits has a uniform linear bound in the input length. -/
theorem encodedCutoffExponent_le (r C₀ : ℕ) (x : List Bool) :
    encodedCutoffExponent r C₀ x ≤ 128 * r * (38 + Nat.clog 2 C₀ + 2 * Nat.clog 2 r) + 768 * r * x.length := by
  cases hdecode : decodeTerms x with
  | none => simp [encodedCutoffExponent, hdecode]
  | some l =>
      simpa only [encodedCutoffExponent, hdecode] using termCutoffExponent_le r C₀ x l hdecode

/-- The total number of binary choices is linear in the actual encoded input length. -/
theorem encodedPrimeChoice_bits_le (r C₀ : ℕ) (x : List Bool) :
    2 * encodedCutoffExponent r C₀ x + 5 ≤
      256 * r * (38 + Nat.clog 2 C₀ + 2 * Nat.clog 2 r) + 1536 * r * x.length + 5 := by
  have h := encodedCutoffExponent_le r C₀ x
  nlinarith



end SparseIrred.UpperBounds.GeneralGap
