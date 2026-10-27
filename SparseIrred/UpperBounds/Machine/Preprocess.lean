import SparseIrred.UpperBounds.RawInputBounds

/-!
# Executable preprocessing for the Section 3.7 machine

The implementation keeps sparse integer term lists throughout. It checks the exact
canonical encoding used by `IrredLang`, computes the content and the cutoff exponent,
and never constructs a dense polynomial. The theorems connect these executable data
operations to the mathematical definitions. Running-time certificates are separate.
-/

open Polynomial SparseDiv SparseDiv.Appendix

namespace SparseIrred.UpperBounds.Machine

/-- Check increasing exponents and nonzero coefficients on an actual finite list. -/
def normalizedTerms (l : ITerms) : Bool :=
  decide (l.Pairwise (fun s t ↦ s.2 < t.2)) && l.all (fun t ↦ decide (t.1 ≠ 0))

@[simp] theorem normalizedTerms_eq_true (l : ITerms) :
    normalizedTerms l = true ↔ NormalizedZ l := by
  simp [normalizedTerms, NormalizedZ]

/-- Reject malformed codes, noncanonical numerals and noncanonical sparse lists. -/
def decodeTerms (x : List Bool) : Option ITerms :=
  match decITerms x with
  | none => none
  | some l => if normalizedTerms l && decide (encITerms l = x) then some l else none

/-- Successful executable decoding gives exactly a canonical list and its original code. -/
theorem decodeTerms_eq_some_iff (x : List Bool) (l : ITerms) :
    decodeTerms x = some l ↔ NormalizedZ l ∧ encITerms l = x := by
  constructor
  · intro h
    unfold decodeTerms at h
    split at h
    · contradiction
    · rename_i ls hls
      split at h
      · rename_i hvalid
        have heq : ls = l := Option.some.inj h
        subst ls
        simpa using hvalid
      · contradiction
  · rintro ⟨hn, rfl⟩
    simp [decodeTerms, hn]

/-- Executable decoding agrees with the existing semantic polynomial decoder. -/
theorem decodePoly_eq_map_decodeTerms (x : List Bool) :
    decodePoly x = (decodeTerms x).map toPolyZ := by
  classical
  unfold decodePoly decodeTerms
  cases h : decITerms x with
  | none => rfl
  | some l =>
    by_cases hn : NormalizedZ l ∧ encITerms l = x
    · simp [hn.1, hn.2]
    · simp only [Option.map]
      simp [hn]

/-- The paper's `Δ`, computed on the sparse list. -/
def termDelta (l : ITerms) : ℕ :=
  Nat.clog 2 (degreeZ l + 2) + Nat.clog 2 (SparseIrred.Machine.absSum l + 2) + 2

/-- The number of random bits used for each of the two integer candidates. -/
def termCutoffExponent (C₀ : ℕ) (l : ITerms) : ℕ :=
  128 * cutoffLog C₀ (degreeZ l) (termDelta l)

theorem termDelta_eq (l : ITerms) (hl : NormalizedZ l) :
    termDelta l = inputDelta (toPolyZ l) := by
  simp only [termDelta, inputDelta, natDegree_toPolyZ_of_normalizedZ hl,
    integerL1, canonTerms_toPolyZ hl]

theorem termCutoffExponent_eq (C₀ : ℕ) (l : ITerms) (hl : NormalizedZ l) :
    termCutoffExponent C₀ l = inputCutoffExponent C₀ (toPolyZ l) := by
  simp only [termCutoffExponent, inputCutoffExponent, termDelta_eq l hl,
    natDegree_toPolyZ_of_normalizedZ hl]

/-- The executable content test is exactly the primitive-polynomial test. -/
theorem contentZ_eq_one_iff (l : ITerms) (hl : NormalizedZ l) :
    contentZ l = 1 ↔ (toPolyZ l).IsPrimitive := by
  rw [Polynomial.isPrimitive_iff_content_eq_one, ← contentZ_eq_content hl]
  exact_mod_cast (Iff.rfl : contentZ l = 1 ↔ contentZ l = 1)

/-- Linear random-bit bound in the length of the actual input string. -/
theorem termCutoffExponent_le (C₀ : ℕ) (x : List Bool) (l : ITerms)
    (h : decodeTerms x = some l) :
    termCutoffExponent C₀ l ≤ 128 * (38 + Nat.clog 2 C₀) + 768 * x.length := by
  obtain ⟨hl, hx⟩ := (decodeTerms_eq_some_iff x l).mp h
  rw [termCutoffExponent_eq C₀ l hl, ← hx]
  exact inputCutoffExponent_le_raw_length C₀ l

end SparseIrred.UpperBounds.Machine
