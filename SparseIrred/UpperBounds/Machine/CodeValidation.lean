import SparseIrred.UpperBounds.Machine.Preprocess
import SparseIrred.Machine.StrArith

/-!
# Polynomial-time validation of the exact sparse input encoding

A total string canonicalizer outputs a canonical sparse code even on malformed input.
Equality with that output recognizes exactly the input codes accepted by `decodeTerms`.
Cobham's theorem supplies an actual polynomial-time deterministic machine for this check.
-/

open Polynomial Complexity SparseDiv SparseDiv.Appendix SparseDiv.StringArith SparseGcd

namespace SparseIrred.UpperBounds.Machine

/-- Total signed-integer canonicalization, including negative and malformed zero. -/
def canonicalInteger (x : List Bool) : List Bool :=
  caseBit₀ (isZeroBits (magOf x)) (encInt 0) (SparseIrred.Machine.canonIntStr x)

theorem canonicalInteger_eq (x : List Bool) : canonicalInteger x = encInt (decInt x) := by
  by_cases hz : decInt x = 0
  · have hm : decNat (magOf x) = 0 := by
      rw [← natAbs_decInt, hz]
      rfl
    simp [canonicalInteger, (isZeroBits_eq_true_iff _).mpr hm, hz]
  · have hm : decNat (magOf x) ≠ 0 := by
      rw [← natAbs_decInt]
      exact Int.natAbs_ne_zero.mpr hz
    simp [canonicalInteger, SparseGcd.isZeroBits_eq_false hm,
      SparseIrred.Machine.canonIntStr_of_ne_zero hz]

theorem cobham_canonicalInteger {n : ℕ} {g : (Fin n → List Bool) → List Bool}
    (hg : Cobham g) : Cobham fun v ↦ canonicalInteger (g v) := by
  unfold canonicalInteger SparseIrred.Machine.canonIntStr
  exact Cobham.iteFn (cobham_isZeroBits_comp (cobham_magOf_comp hg))
    (Cobham.const (encInt 0))
    (cobham_pair_comp (cobham_negFlag_comp hg)
      (cobham_canonBits_comp (cobham_magOf_comp hg)))

/-- Lenient data extraction used only inside the total canonicalizer. -/
def lenientTerms (s : List Bool) : ITerms :=
  (blocks s).map fun b ↦ (decInt (pairFst b), decNat (pairSnd b))

/-- Canonicalize every numeral before normalizing the sparse list. -/
def canonicalNumerals (s : List Bool) : List Bool :=
  mapBlocks (fun b ↦ pair (canonicalInteger (pairFst b)) (canonBits (pairSnd b))) s

theorem canonicalNumerals_eq (s : List Bool) :
    canonicalNumerals s = encITerms (lenientTerms s) := by
  simp [canonicalNumerals, mapBlocks, encITerms, lenientTerms, List.map_map,
    Function.comp_def, encITerm, canonicalInteger_eq, canonBits]

theorem cobham_canonicalNumerals {n : ℕ} {g : (Fin n → List Bool) → List Bool}
    (hg : Cobham g) : Cobham fun v ↦ canonicalNumerals (g v) := by
  unfold canonicalNumerals
  exact SparseGcd.TermsStr.cobham_mapBlocks_comp
    (F := fun b _ ↦ pair (canonicalInteger (pairFst b)) (canonBits (pairSnd b)))
    (cobham_pair_comp (cobham_canonicalInteger (cobham_pairFst_comp (.proj 0)))
      (cobham_canonBits_comp (cobham_pairSnd_comp (.proj 0)))) hg

/-- A total polynomial-time function whose output is always a canonical sparse code. -/
def canonicalCode (s : List Bool) : List Bool :=
  SparseIrred.Machine.canonITermsStr (normalizeZStr (canonicalNumerals s))

theorem canonicalCode_eq (s : List Bool) :
    canonicalCode s = encITerms (normalizeZ (lenientTerms s)) := by
  rw [canonicalCode, canonicalNumerals_eq,
    SparseIrred.Machine.canonITermsStr_normalizeZStr]

theorem cobham_canonicalCode {n : ℕ} {g : (Fin n → List Bool) → List Bool}
    (hg : Cobham g) : Cobham fun v ↦ canonicalCode (g v) :=
  SparseIrred.Machine.cobham_canonITermsStr_comp
    (SparseIrred.Machine.cobham_normalizeZStr_comp (cobham_canonicalNumerals hg))

theorem lenientTerms_encITerms (l : ITerms) : lenientTerms (encITerms l) = l := by
  simp [lenientTerms, encITerms, blocks_frame, List.map_map, Function.comp_def, encITerm]

theorem canonicalCode_encITerms (l : ITerms) (hl : NormalizedZ l) :
    canonicalCode (encITerms l) = encITerms l := by
  rw [canonicalCode_eq, lenientTerms_encITerms]
  have h := canonTerms_toPolyZ (normalizedZ_normalizeZ l)
  rw [toPolyZ_normalizeZ, canonTerms_toPolyZ hl] at h
  rw [← h]

/-- The fixed points of the total canonicalizer are exactly the legitimate input codes. -/
theorem canonicalCode_eq_self_iff (s : List Bool) :
    canonicalCode s = s ↔ ∃ l, decodeTerms s = some l := by
  constructor
  · intro h
    refine ⟨normalizeZ (lenientTerms s), (decodeTerms_eq_some_iff _ _).mpr ?_⟩
    exact ⟨normalizedZ_normalizeZ _, (canonicalCode_eq s).symm.trans h⟩
  · rintro ⟨l, hl⟩
    obtain ⟨hn, rfl⟩ := (decodeTerms_eq_some_iff _ _).mp hl
    exact canonicalCode_encITerms l hn

/-- Validation is exact string equality, so malformed framing cannot be accepted. -/
def validCode (s : List Bool) : List Bool := Cobham.eqFlag (canonicalCode s) s

theorem validCode_mem_FP : validCode ∈ FP := by
  apply CobhamFP_subset_FP
  exact Cobham.eqFlag_mem (cobham_canonicalCode (.proj 0)) (.proj 0)

theorem validCode_eq_true_iff (s : List Bool) :
    validCode s = [true] ↔ ∃ l, decodeTerms s = some l := by
  rw [validCode, Cobham.eqFlag_eq_true_iff, canonicalCode_eq_self_iff]

end SparseIrred.UpperBounds.Machine
