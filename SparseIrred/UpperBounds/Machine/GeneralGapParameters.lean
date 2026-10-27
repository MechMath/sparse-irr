import SparseIrred.UpperBounds.GeneralGapDecision
import SparseIrred.UpperBounds.Machine.CutoffParameters

/-! # Polynomial-time cutoff parameters for a fixed positive gap -/
open Polynomial Complexity SparseDiv SparseDiv.Appendix SparseDiv.StringArith SparseGcd
open SparseIrred.UpperBounds.Machine
namespace SparseIrred.UpperBounds.GeneralGap

def termCutoffExponent (r C₀ : ℕ) (l : ITerms) : ℕ :=
  128 * r * cutoffLog C₀ (r * degreeZ l) (termDelta l)

theorem termCutoffExponent_eq (r C₀ : ℕ) (l : ITerms) (hl : NormalizedZ l) :
    termCutoffExponent r C₀ l = scaledInputCutoffExponent r C₀ (toPolyZ l) := by
  simp only [termCutoffExponent, scaledInputCutoffExponent,
    natDegree_toPolyZ_of_normalizedZ hl, termDelta_eq l hl]

theorem termCutoffExponent_le (r C₀ : ℕ) (x : List Bool) (l : ITerms)
    (hx : decodeTerms x = some l) :
    termCutoffExponent r C₀ l ≤
      128 * r * (38 + Nat.clog 2 C₀ + 2 * Nat.clog 2 r) + 768 * r * x.length := by
  obtain ⟨hl, henc⟩ := (decodeTerms_eq_some_iff x l).mp hx
  rw [termCutoffExponent_eq r C₀ l hl, ← henc]
  exact scaledInputCutoffExponent_le_raw_length r C₀ l

/-- The cutoff exponent `m = 128*r*ceil(log₂ U)`, using degree parameter `r*n`. -/
def cutoffExponentStr (r C₀ : ℕ) (s : List Bool) : List Bool :=
  let n := mulBits (encNat r) (degreeStr s)
  let d := addBits (deltaStr s) [true]
  canonBits (mulBits (encNat (128 * r))
    (clogTwoStr (mulBits (mulBits (encNat (2 ^ 20 * C₀)) (mulBits n n)) (mulBits d d))))

theorem cobham_cutoffExponentStr (r C₀ : ℕ) {n : ℕ}
    {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v ↦ cutoffExponentStr r C₀ (g v) := by
  have hn : Cobham fun v ↦ degreeStr (g v) :=
    (Cobham.comp (FP_subset_CobhamFP degreeStr_mem_FP) fun _ : Fin 1 ↦ hg).of_eq fun _ ↦ rfl
  have hn := cobham_mulBits_comp (Cobham.const (encNat r)) hn
  have hd := cobham_addBits_comp (cobham_deltaStr hg) (Cobham.const [true])
  exact cobham_canonBits_comp (cobham_mulBits_comp (Cobham.const (encNat (128 * r)))
    (cobham_clogTwoStr (cobham_mulBits_comp
      (cobham_mulBits_comp (Cobham.const (encNat (2 ^ 20 * C₀)))
        (cobham_mulBits_comp hn hn)) (cobham_mulBits_comp hd hd))))

theorem cutoffExponentStr_eq (r C₀ : ℕ) (l : ITerms) :
    cutoffExponentStr r C₀ (encITerms l) = encNat (termCutoffExponent r C₀ l) := by
  simp [cutoffExponentStr, canonBits, decNat_mulBits, clogTwoStr_eq, decNat_degreeStr,
    decNat_addBits, decNat_deltaStr, termCutoffExponent, cutoffLog, cutoffScale, pow_two,
    decNat_cons, mul_assoc]

theorem cutoffExponentStr_mem_FP (r C₀ : ℕ) : cutoffExponentStr r C₀ ∈ FP :=
  CobhamFP_subset_FP (cobham_cutoffExponentStr r C₀ (.proj 0))

/-- A linear ruler bounding the candidate width, including on malformed strings. -/
def cutoffRuler (r C₀ : ℕ) (x : List Bool) : List Bool :=
  List.replicate (128 * r * (38 + Nat.clog 2 C₀ + 2 * Nat.clog 2 r)) false ++ (List.replicate (768 * r) x).flatten

theorem cutoffRuler_length (r C₀ : ℕ) (x : List Bool) :
    (cutoffRuler r C₀ x).length = 128 * r * (38 + Nat.clog 2 C₀ + 2 * Nat.clog 2 r) + 768 * r * x.length := by
  simp only [cutoffRuler, List.length_append, List.length_replicate,
    List.length_flatten, List.map_replicate, List.sum_replicate, smul_eq_mul]

theorem cobham_cutoffRuler (r C₀ : ℕ) {n : ℕ}
    {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v ↦ cutoffRuler r C₀ (g v) :=
  Cobham.appendFn (Cobham.const _) (Cobham.repeatFn hg (768 * r))

/-- Convert the candidate width to unary under the proved linear input-length cap. -/
def cutoffUnary (r C₀ : ℕ) (x : List Bool) : List Bool :=
  SparseIrred.Machine.binToUnaryStr (cutoffExponentStr r C₀ x) (cutoffRuler r C₀ x)

theorem cobham_cutoffUnary (r C₀ : ℕ) {n : ℕ}
    {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v ↦ cutoffUnary r C₀ (g v) :=
  SparseIrred.Machine.cobham_binToUnaryStr_comp (cobham_cutoffExponentStr r C₀ hg)
    (cobham_cutoffRuler r C₀ hg)

/-- The cap never truncates the width on a legitimate sparse input code. -/
theorem cutoffUnary_eq (r C₀ : ℕ) (x : List Bool) (l : ITerms)
    (h : decodeTerms x = some l) : cutoffUnary r C₀ x = unaryN (termCutoffExponent r C₀ l) := by
  have hx := ((decodeTerms_eq_some_iff x l).mp h).2
  have hb := termCutoffExponent_le r C₀ x l h
  rw [cutoffUnary, ← hx, cutoffExponentStr_eq]
  apply SparseIrred.Machine.binToUnaryStr_eq
  rwa [cutoffRuler_length, hx]

theorem cutoffUnary_mem_FP (r C₀ : ℕ) : cutoffUnary r C₀ ∈ FP :=
  CobhamFP_subset_FP (cobham_cutoffUnary r C₀ (.proj 0))

end SparseIrred.UpperBounds.GeneralGap
