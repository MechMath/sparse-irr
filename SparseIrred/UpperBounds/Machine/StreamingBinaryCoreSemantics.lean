import SparseIrred.UpperBounds.Machine.StreamingBinaryCoreSpace
import SparseIrred.UpperBounds.Machine.StreamingSemantics
import SparseIrred.UpperBounds.Machine.StreamingBinaryInput
import SparseIrred.UpperBounds.Machine.StreamingStepFP

/-! # The two binary counters are the paper's prime and root counts -/

namespace SparseIrred.UpperBounds.Machine
open Complexity BinaryRoutine SparseDiv SparseDiv.Appendix
open scoped BigOperators

def unpackedInput (n : ℕ) : List Bool := n.bits.dropLast

@[simp] theorem unpackedInput_packedInput (x : List Bool) :
    unpackedInput (packedInput x) = x := by simp [unpackedInput, packedInput_bits]

@[nolint unusedArguments]
def corePrimeContribution (input p a : ℕ) : ℕ := streamPrimeIncrement p a

def coreRootContribution (input p a : ℕ) : ℕ := streamRootIncrement (unpackedInput input) p a

def ValidCoreInput (input : ℕ) : Prop := ∃ l : ITerms, input = packedInput (encITerms l)

theorem corePrimeContribution_le (input p a : ℕ) : corePrimeContribution input p a ≤ 1 :=
  streamPrimeIncrement_le p a

theorem coreRootContribution_le (input p a : ℕ) : coreRootContribution input p a ≤ 2 :=
  streamRootIncrement_le _ _ _

theorem core_contribution_sums (l : ITerms) (X : ℕ) :
    (∑ p ∈ Finset.range X, ∑ a ∈ Finset.range X,
        corePrimeContribution (packedInput (encITerms l)) p a) = primeCountBelow X ∧
      (∑ p ∈ Finset.range X, ∑ a ∈ Finset.range X,
        coreRootContribution (packedInput (encITerms l)) p a) = primeRootSum (toPolyZ l) X := by
  have h := streamCounts_eq_counts l X
  have hP := congrArg Prod.fst h
  have hA := congrArg Prod.snd h
  simp only [streamCounts] at hP hA
  rw [sum_rectangle_div_mod] at hP hA
  simpa only [corePrimeContribution, coreRootContribution, unpackedInput_packedInput] using
    (show _ ∧ _ from ⟨hP, hA⟩)

theorem coreEnumeration_eq_paper_counts {cell : BinaryRoutine 70}
    (spec : CoreCellSpec cell corePrimeContribution coreRootContribution)
    (l : ITerms) (X : ℕ) (hv : spec.valid (packedInput (encITerms l))) :
    (coreEnumeration cell).effect (coreValues (packedInput (encITerms l)) X 0 0 0 0) =
      coreValues (packedInput (encITerms l)) X X 0 (primeCountBelow X)
        (primeRootSum (toPolyZ l) X) := by
  rw [coreEnumeration_effect spec _ _ _ _ hv]
  rw [(core_contribution_sums l X).1, (core_contribution_sums l X).2]
  simp

/-- A uniform bound for both complete and incomplete rectangular counter sums. -/
theorem core_prefix_sum_bounds (input X p a : ℕ) (hp : p < X) (ha : a < X) :
    (∑ q ∈ Finset.range p, ∑ b ∈ Finset.range X, corePrimeContribution input q b) +
        (∑ b ∈ Finset.range a, corePrimeContribution input p b) ≤ X * X ∧
      (∑ q ∈ Finset.range p, ∑ b ∈ Finset.range X, coreRootContribution input q b) +
        (∑ b ∈ Finset.range a, coreRootContribution input p b) ≤ 2 * (X * X) := by
  have hP (p a : ℕ) : (∑ q ∈ Finset.range p, ∑ b ∈ Finset.range a,
      corePrimeContribution input q b) ≤ p * a := by
    calc
      _ ≤ ∑ _q ∈ Finset.range p, ∑ _b ∈ Finset.range a, 1 :=
        Finset.sum_le_sum fun q _ ↦ Finset.sum_le_sum fun b _ ↦ corePrimeContribution_le _ _ _
      _ = _ := by simp [Nat.mul_comm]
  have hA (p a : ℕ) : (∑ q ∈ Finset.range p, ∑ b ∈ Finset.range a,
      coreRootContribution input q b) ≤ 2 * (p * a) := by
    calc
      _ ≤ ∑ _q ∈ Finset.range p, ∑ _b ∈ Finset.range a, 2 :=
        Finset.sum_le_sum fun q _ ↦ Finset.sum_le_sum fun b _ ↦ coreRootContribution_le _ _ _
      _ = _ := by simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  have hPr : (∑ b ∈ Finset.range a, corePrimeContribution input p b) ≤ a := by
    calc
      _ ≤ ∑ _b ∈ Finset.range a, 1 := Finset.sum_le_sum fun b _ ↦ corePrimeContribution_le _ _ _
      _ = _ := by simp
  have hAr : (∑ b ∈ Finset.range a, coreRootContribution input p b) ≤ 2 * a := by
    calc
      _ ≤ ∑ _b ∈ Finset.range a, 2 := Finset.sum_le_sum fun b _ ↦ coreRootContribution_le _ _ _
      _ = _ := by simp [Nat.mul_comm]
  have hindex : p * X + a ≤ X * X := by nlinarith
  constructor
  · exact (Nat.add_le_add (hP p X) hPr).trans hindex
  · have := Nat.add_le_add (hA p X) hAr
    nlinarith

def coreNumericWidth (input X : ℕ) : ℕ := input + X + 2 * (X * X) + 3

theorem coreValues_le_width (input X p a P A : ℕ)
    (hp : p ≤ X) (ha : a ≤ X) (hP : P ≤ X * X) (hA : A ≤ 2 * (X * X)) :
    ∀ i, coreValues input X p a P A i ≤ coreNumericWidth input X := by
  intro i
  refine Fin.addCases (m := 64) (n := 6) (fun i ↦ ?_) (fun i ↦ ?_) i
  · rw [coreValues, Fin.append_left]
    exact Nat.zero_le _
  · change coreValues input X p a P A (coreReg i) ≤ _
    rw [coreValues_reg]
    fin_cases i <;> simp [coreNumericWidth] <;> omega

theorem coreCellInputs_values_le {cell : BinaryRoutine 70}
    (spec : CoreCellSpec cell corePrimeContribution coreRootContribution)
    (input X : ℕ → ℕ) (hvalid : ∀ j, spec.valid (input j)) (hX : ∀ j, 0 < X j)
    (code : ℕ) (i : Fin 70) :
    coreCellInputs cell input X (fun _ ↦ 0) (fun _ ↦ 0) code i ≤
      coreNumericWidth (input (Nat.unpair (Nat.unpair code).1).1)
        (X (Nat.unpair (Nat.unpair code).1).1) := by
  rw [coreCellInputs_eq spec input X (fun _ ↦ 0) (fun _ ↦ 0) hvalid hX]
  simp only [Nat.zero_add]
  have hp := coreRowIndex_lt X hX (Nat.unpair code).1
  have ha : min (Nat.unpair code).2 (X (Nat.unpair (Nat.unpair code).1).1 - 1) <
      X (Nat.unpair (Nat.unpair code).1).1 := by
    have := Nat.min_le_right (Nat.unpair code).2 (X (Nat.unpair (Nat.unpair code).1).1 - 1)
    have := hX (Nat.unpair (Nat.unpair code).1).1
    omega
  have hc := core_prefix_sum_bounds (input (Nat.unpair (Nat.unpair code).1).1)
    (X (Nat.unpair (Nat.unpair code).1).1) _ _ hp ha
  exact coreValues_le_width _ _ _ _ _ _ hp.le ha.le hc.1 hc.2 i

/-- The common value envelope has only a fixed affine number of input bits. -/
theorem coreNumericWidth_size_le (C₀ : ℕ) (x : List Bool) :
    (coreNumericWidth (packedInput x) (streamCutoff C₀ x)).size ≤
      1537 * x.length + 256 * (38 + Nat.clog 2 C₀) + 5 := by
  let m := (cutoffUnary C₀ x).length
  let e := x.length + 2 * m + 2
  have hm := cutoffUnary_length_le C₀ x
  have he4 : 4 ≤ (2 : ℕ) ^ e := by
    have h := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 2 ≤ e by dsimp [e]; omega)
    exact h
  have hinput : packedInput x ≤ 2 ^ e := by
    have h := Nat.le_of_lt (Nat.lt_size_self (packedInput x))
    rw [packedInput_size] at h
    exact h.trans (Nat.pow_le_pow_right (by decide) (by dsimp [e]; omega))
  have hX : streamCutoff C₀ x ≤ 2 ^ e := by
    change 2 ^ m ≤ _
    exact Nat.pow_le_pow_right (by decide) (by dsimp [e]; omega)
  have hsq : streamCutoff C₀ x * streamCutoff C₀ x = 2 ^ (2 * m) := by
    change 2 ^ m * 2 ^ m = _
    rw [← pow_add]
    congr 1
    omega
  have hsq2 : 2 * (streamCutoff C₀ x * streamCutoff C₀ x) ≤ 2 ^ e := by
    rw [hsq, ← pow_succ']
    exact Nat.pow_le_pow_right (by decide) (by dsimp [e]; omega)
  have hbound : coreNumericWidth (packedInput x) (streamCutoff C₀ x) ≤ 2 ^ (e + 2) := by
    unfold coreNumericWidth
    rw [pow_add]
    norm_num
    omega
  have hsize := (Nat.size_le_size hbound).trans_eq (Nat.size_pow)
  dsimp [e, m] at hsize
  omega

/-- A single natural index ranges over all well-framed sparse term lists. -/
def coreListFamily (code : ℕ) : ITerms := lenientTerms (unpackedInput code)

def coreEncodedFamily (code : ℕ) : List Bool := encITerms (coreListFamily code)

def corePackedFamily (code : ℕ) : ℕ := packedInput (coreEncodedFamily code)

def coreLimitFamily (C₀ code : ℕ) : ℕ := streamCutoff C₀ (coreEncodedFamily code)

def coreWidthFamily (C₀ code : ℕ) : ℕ :=
  coreNumericWidth (corePackedFamily code) (coreLimitFamily C₀ code)

@[simp] theorem coreListFamily_encode (l : ITerms) :
    coreListFamily (packedInput (encITerms l)) = l := by
  simp [coreListFamily, lenientTerms_encITerms]

@[simp] theorem coreEncodedFamily_encode (l : ITerms) :
    coreEncodedFamily (packedInput (encITerms l)) = encITerms l := by simp [coreEncodedFamily]

theorem corePackedFamily_valid (code : ℕ) : ValidCoreInput (corePackedFamily code) :=
  ⟨coreListFamily code, rfl⟩

theorem coreLimitFamily_pos (C₀ code : ℕ) : 0 < coreLimitFamily C₀ code := by
  exact Nat.two_pow_pos _

theorem coreLimitFamily_le_width (C₀ code : ℕ) :
    coreLimitFamily C₀ code ≤ coreWidthFamily C₀ code := by
  unfold coreWidthFamily coreNumericWidth
  omega

theorem coreWidthFamily_size_le (C₀ code : ℕ) :
    (coreWidthFamily C₀ code).size ≤
      1537 * (coreEncodedFamily code).length + 256 * (38 + Nat.clog 2 C₀) + 5 :=
  coreNumericWidth_size_le C₀ (coreEncodedFamily code)

end SparseIrred.UpperBounds.Machine
