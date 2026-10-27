import SparseIrred.UpperBounds.Machine.CodeValidation
import SparseIrred.UpperBounds.Machine.ModularVerifier

/-!
# Polynomial-time computation of the cutoff exponent

All large numbers are binary strings. Ceiling logarithms are computed by the bit length
of the predecessor, and sparse coefficient magnitudes are summed without expanding exponents.
-/

open Polynomial Complexity SparseDiv SparseDiv.Appendix SparseDiv.StringArith SparseGcd

namespace SparseIrred.UpperBounds.Machine

theorem clog_two_eq_size_pred (n : ℕ) : Nat.clog 2 n = (n - 1).size := by
  apply Nat.le_antisymm
  · apply Nat.clog_le_of_le_pow
    have h := Nat.lt_size_self (n - 1)
    omega
  · apply Nat.size_le.mpr
    have h := Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) n
    have hp : 0 < 2 ^ Nat.clog 2 n := by positivity
    omega

/-- Binary ceiling logarithm, including the zero and one cases. -/
def clogTwoStr (x : List Bool) : List Bool :=
  unaryToBinStr (canonBits (subBits x [true]))

theorem clogTwoStr_eq (x : List Bool) :
    clogTwoStr x = encNat (Nat.clog 2 (decNat x)) := by
  rw [clogTwoStr, unaryToBinStr, canonBits_succBits_iterate, canonBits,
    length_encNat, decNat_subBits]
  simp [clog_two_eq_size_pred, decNat_cons]

theorem cobham_clogTwoStr {n : ℕ} {g : (Fin n → List Bool) → List Bool}
    (hg : Cobham g) : Cobham fun v ↦ clogTwoStr (g v) :=
  (Cobham.comp cobham_unaryToBinStr fun _ : Fin 1 ↦
    cobham_canonBits_comp (cobham_subBits_comp hg (Cobham.const [true]))).of_eq fun _ ↦ rfl

/-- The sum of coefficient magnitudes in a framed sparse code. -/
def magnitudeSumStr (s : List Bool) : List Bool :=
  sumNumeralsStr (mapBlocks (fun t ↦ magOf (pairFst t)) s)

theorem cobham_magnitudeSumStr {n : ℕ} {g : (Fin n → List Bool) → List Bool}
    (hg : Cobham g) : Cobham fun v ↦ magnitudeSumStr (g v) := by
  have hm := TermsStr.cobham_mapBlocks_comp
    (F := fun t (_ : Fin n → List Bool) ↦ magOf (pairFst t))
    (cobham_magOf_comp (cobham_pairFst_comp (.proj 0))) hg
  exact (Cobham.comp cobham_sumNumeralsStr fun _ : Fin 1 ↦ hm).of_eq fun _ ↦ rfl

theorem decNat_magnitudeSumStr (l : ITerms) :
    decNat (magnitudeSumStr (encITerms l)) = SparseIrred.Machine.absSum l := by
  rw [magnitudeSumStr, encITerms, mapBlocks_frame, decNat_sumNumeralsStr_frame]
  simp [List.map_map, Function.comp_def, encITerm, SparseIrred.Machine.magOf_encInt,
    SparseIrred.Machine.absSum]

/-- The exact integer `Δ` in binary. -/
def deltaStr (s : List Bool) : List Bool :=
  addBits (addBits (clogTwoStr (addBits (degreeStr s) (encNat 2)))
    (clogTwoStr (addBits (magnitudeSumStr s) (encNat 2)))) (encNat 2)

theorem cobham_deltaStr {n : ℕ} {g : (Fin n → List Bool) → List Bool}
    (hg : Cobham g) : Cobham fun v ↦ deltaStr (g v) := by
  have hd : Cobham fun v ↦ degreeStr (g v) :=
    (Cobham.comp (FP_subset_CobhamFP degreeStr_mem_FP) fun _ : Fin 1 ↦ hg).of_eq fun _ ↦ rfl
  exact cobham_addBits_comp (cobham_addBits_comp
    (cobham_clogTwoStr (cobham_addBits_comp hd (Cobham.const (encNat 2))))
    (cobham_clogTwoStr (cobham_addBits_comp (cobham_magnitudeSumStr hg)
      (Cobham.const (encNat 2))))) (Cobham.const (encNat 2))

theorem decNat_deltaStr (l : ITerms) : decNat (deltaStr (encITerms l)) = termDelta l := by
  simp [deltaStr, decNat_addBits, clogTwoStr_eq, decNat_degreeStr,
    decNat_magnitudeSumStr, termDelta]

/-- The cutoff exponent `m = 128 ceil(log₂ U)`, with the fixed machine constant `C₀`. -/
def cutoffExponentStr (C₀ : ℕ) (s : List Bool) : List Bool :=
  let n := degreeStr s
  let d := addBits (deltaStr s) [true]
  canonBits (mulBits (encNat 128)
    (clogTwoStr (mulBits (mulBits (encNat (2 ^ 20 * C₀)) (mulBits n n)) (mulBits d d))))

theorem cobham_cutoffExponentStr (C₀ : ℕ) {n : ℕ}
    {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v ↦ cutoffExponentStr C₀ (g v) := by
  have hn : Cobham fun v ↦ degreeStr (g v) :=
    (Cobham.comp (FP_subset_CobhamFP degreeStr_mem_FP) fun _ : Fin 1 ↦ hg).of_eq fun _ ↦ rfl
  have hd := cobham_addBits_comp (cobham_deltaStr hg) (Cobham.const [true])
  exact cobham_canonBits_comp (cobham_mulBits_comp (Cobham.const (encNat 128))
    (cobham_clogTwoStr (cobham_mulBits_comp
      (cobham_mulBits_comp (Cobham.const (encNat (2 ^ 20 * C₀)))
        (cobham_mulBits_comp hn hn)) (cobham_mulBits_comp hd hd))))

theorem cutoffExponentStr_eq (C₀ : ℕ) (l : ITerms) :
    cutoffExponentStr C₀ (encITerms l) = encNat (termCutoffExponent C₀ l) := by
  simp [cutoffExponentStr, canonBits, decNat_mulBits, clogTwoStr_eq, decNat_degreeStr,
    decNat_addBits, decNat_deltaStr, termCutoffExponent, cutoffLog, cutoffScale, pow_two,
    decNat_cons]

theorem cutoffExponentStr_mem_FP (C₀ : ℕ) : cutoffExponentStr C₀ ∈ FP :=
  CobhamFP_subset_FP (cobham_cutoffExponentStr C₀ (.proj 0))

/-- A linear ruler bounding the candidate width, including on malformed strings. -/
def cutoffRuler (C₀ : ℕ) (x : List Bool) : List Bool :=
  List.replicate (128 * (38 + Nat.clog 2 C₀)) false ++ (List.replicate 768 x).flatten

theorem cutoffRuler_length (C₀ : ℕ) (x : List Bool) :
    (cutoffRuler C₀ x).length = 128 * (38 + Nat.clog 2 C₀) + 768 * x.length := by
  simp only [cutoffRuler, List.length_append, List.length_replicate,
    List.length_flatten, List.map_replicate, List.sum_replicate, smul_eq_mul]

theorem cobham_cutoffRuler (C₀ : ℕ) {n : ℕ}
    {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v ↦ cutoffRuler C₀ (g v) :=
  Cobham.appendFn (Cobham.const _) (Cobham.repeatFn hg 768)

/-- Convert the candidate width to unary under the proved linear input-length cap. -/
def cutoffUnary (C₀ : ℕ) (x : List Bool) : List Bool :=
  SparseIrred.Machine.binToUnaryStr (cutoffExponentStr C₀ x) (cutoffRuler C₀ x)

theorem cobham_cutoffUnary (C₀ : ℕ) {n : ℕ}
    {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v ↦ cutoffUnary C₀ (g v) :=
  SparseIrred.Machine.cobham_binToUnaryStr_comp (cobham_cutoffExponentStr C₀ hg)
    (cobham_cutoffRuler C₀ hg)

/-- The cap never truncates the width on a legitimate sparse input code. -/
theorem cutoffUnary_eq (C₀ : ℕ) (x : List Bool) (l : ITerms)
    (h : decodeTerms x = some l) : cutoffUnary C₀ x = unaryN (termCutoffExponent C₀ l) := by
  have hx := ((decodeTerms_eq_some_iff x l).mp h).2
  have hb := termCutoffExponent_le C₀ x l h
  rw [cutoffUnary, ← hx, cutoffExponentStr_eq]
  apply SparseIrred.Machine.binToUnaryStr_eq
  rwa [cutoffRuler_length, hx]

theorem cutoffUnary_mem_FP (C₀ : ℕ) : cutoffUnary C₀ ∈ FP :=
  CobhamFP_subset_FP (cobham_cutoffUnary C₀ (.proj 0))

end SparseIrred.UpperBounds.Machine
