import SparseIrred.UpperBounds.Machine.StreamingBinaryCellCompleteSpace
import SparseIrred.UpperBounds.Machine.StreamingBinaryVerdict
import SparseIrred.UpperBounds.Machine.StreamingBinaryDecisionSpace
import SparseIrred.UpperBounds.Machine.StreamingBinaryCoreSemantics

/-!
# Section 3.6: the actual enumeration core has linear work space

This is a single fixed deterministic machine, with 70 binary work registers.
Its input register and cutoff are supplied by the already verified arithmetic
preprocessing. It uses internally proved trial division, sparse modular
evaluation, and two nested binary loops, and emits the strict threshold result.
The bound covers every machine configuration and the output head, not merely
the values present at loop boundaries. No AKS or algorithm certificate is used.
-/

namespace SparseIrred.UpperBounds.Machine
open Complexity BinaryRoutine SparseDiv SparseDiv.Appendix

set_option maxRecDepth 8192

/-- The real two-loop enumerator followed by the real threshold-output machine. -/
def section3BinaryCore : BinaryRoutine 70 := seq (coreEnumeration completeCell) coreVerdict

theorem section3BinaryCore_sound : section3BinaryCore.Sound :=
  (coreEnumeration_sound completeCell_sound).seq coreVerdict_sound

def section3CoreValues (C₀ : ℕ) (l : ITerms) : BinaryValues 70 :=
  coreValues (packedInput (encITerms l)) (streamCutoff C₀ (encITerms l)) 0 0 0 0

theorem section3BinaryCore_requires (C₀ : ℕ) (l : ITerms) :
    section3BinaryCore.requires (section3CoreValues C₀ l) := by
  change (coreEnumeration completeCell).requires (section3CoreValues C₀ l) ∧
    coreVerdict.requires ((coreEnumeration completeCell).effect (section3CoreValues C₀ l))
  have he := coreEnumeration_requires completeCellSpec (packedInput (encITerms l))
    (streamCutoff C₀ (encITerms l)) 0 0 (show ValidCoreInput _ from ⟨l, rfl⟩)
  refine ⟨?_, coreVerdict_requires _⟩
  simpa only [section3CoreValues] using he

/-- The actual output is the exact strict comparison in the paper. -/
theorem section3BinaryCore_emitted (C₀ : ℕ) (l : ITerms) :
    section3BinaryCore.emitted (section3CoreValues C₀ l) =
      [decide (2 * primeRootSum (toPolyZ l) (streamCutoff C₀ (encITerms l)) <
        3 * primeCountBelow (streamCutoff C₀ (encITerms l)))] := by
  change (coreEnumeration completeCell).emitted _ ++ coreVerdict.emitted _ = _
  rw [coreEnumeration_silent completeCell_silent _, List.nil_append]
  rw [show section3CoreValues C₀ l = coreValues (packedInput (encITerms l))
    (streamCutoff C₀ (encITerms l)) 0 0 0 0 from rfl]
  rw [coreEnumeration_eq_paper_counts completeCellSpec l _ ⟨l, rfl⟩, coreVerdict_emitted]
  rfl

theorem section3BinaryCore_width (C₀ : ℕ) :
    SpaceBoundByWidthAt section3BinaryCore (fun _ ↦ 1)
      (coreInitial corePackedFamily (coreLimitFamily C₀) (fun _ ↦ 0) (fun _ ↦ 0))
      (coreWidthFamily C₀) := by
  have hvalid : ∀ j, completeCellSpec.valid (corePackedFamily j) := corePackedFamily_valid
  have hX : ∀ j, 0 < coreLimitFamily C₀ j := coreLimitFamily_pos C₀
  apply SpaceBoundByWidthAt.seq
  · apply coreEnumeration_space completeCellSpec corePackedFamily (coreLimitFamily C₀)
      (fun _ ↦ 0) (fun _ ↦ 0) (fun _ ↦ 1) (coreWidthFamily C₀)
      hvalid hX (coreLimitFamily_le_width C₀)
    apply completeCell_space
    · intro code
      rw [coreCellInputs_eq completeCellSpec corePackedFamily (coreLimitFamily C₀)
        (fun _ ↦ 0) (fun _ ↦ 0) hvalid hX]
      simpa only [coreValues_reg, Matrix.cons_val_zero] using
        corePackedFamily_valid (Nat.unpair (Nat.unpair code).1).1
    · intro code i
      exact coreCellInputs_values_le completeCellSpec corePackedFamily (coreLimitFamily C₀)
        hvalid hX code i
  · apply coreVerdict_space
    intro code i
    change (coreEnumeration completeCell).effect
      (coreValues (packedInput (encITerms (coreListFamily code)))
        (streamCutoff C₀ (encITerms (coreListFamily code))) 0 0 0 0) i ≤ _
    rw [coreEnumeration_eq_paper_counts completeCellSpec (coreListFamily code) _ ⟨_, rfl⟩]
    have hc := streamCounts_bounds (encITerms (coreListFamily code))
      (coreLimitFamily C₀ code) (coreLimitFamily C₀ code * coreLimitFamily C₀ code)
    rw [streamCounts_eq_counts] at hc
    exact coreValues_le_width _ _ _ _ _ _ le_rfl (Nat.zero_le _) hc.1 hc.2 i

/-- One pair of affine constants bounds the advertised space for every sparse input. -/
theorem section3BinaryCore_space_linear (C₀ : ℕ) :
    ∃ A B : ℕ, ∀ l : ITerms,
      section3BinaryCore.spaceBound 1 (section3CoreValues C₀ l) ≤
        A * (encITerms l).length + B := by
  obtain ⟨K, hK⟩ := section3BinaryCore_width C₀
  refine ⟨1537 * K, 1 + K * (256 * (38 + Nat.clog 2 C₀) + 6), fun l ↦ ?_⟩
  have h := hK (packedInput (encITerms l))
  have hw := coreWidthFamily_size_le C₀ (packedInput (encITerms l))
  simp only [coreEncodedFamily_encode] at hw
  have hinitial : coreInitial corePackedFamily (coreLimitFamily C₀) (fun _ ↦ 0) (fun _ ↦ 0)
      (packedInput (encITerms l)) = section3CoreValues C₀ l := by
    simp [coreInitial, corePackedFamily, coreLimitFamily, section3CoreValues]
  rw [hinitial] at h
  have hmul := Nat.mul_le_mul_left K hw
  nlinarith

/-- The normalized-input starting configuration of the enumeration core. -/
def section3CoreStart (C₀ : ℕ) (l : ITerms) : Cfg 70 section3BinaryCore.machine.Q :=
  { state := section3BinaryCore.machine.qstart
    input := (Tape.init ((encITerms l).map Γ.ofBool)).move Dir3.right
    work := workTapes (section3CoreValues C₀ l)
    output := TM.parkedBlank }

/-- Original Section 3.6, including the stronger linear-space claim for the core.
The actual trial-division enumerator halts with the correct irreducibility verdict;
every reachable configuration, including subroutine steps and the output tape,
has an affine space bound in the sparse input length. -/
theorem section3_linear_streaming_core (C₀ : ℕ) (hC : 1 ≤ C₀)
    (hExternal : UniformPrimeIdealEstimate C₀) :
    ∃ A B : ℕ, ∀ (l : ITerms), NormalizedZ l → (toPolyZ l).IsPrimitive →
      0 < (toPolyZ l).natDegree →
      (∀ c, section3BinaryCore.machine.reaches (section3CoreStart C₀ l) c →
        c.WithinDecisionSpace (encITerms l).length (A * (encITerms l).length + B)) ∧
      ∃ c t, t ≤ section3BinaryCore.timeBound (section3CoreValues C₀ l) ∧
        section3BinaryCore.machine.reachesIn t (section3CoreStart C₀ l) c ∧
        section3BinaryCore.machine.halted c ∧
        (c.output.cells 1 = Γ.one ↔ Irreducible (toPolyZ l)) := by
  obtain ⟨A, B, hspace⟩ := section3BinaryCore_space_linear C₀
  refine ⟨A, B + 1, fun l hl hf hdegree ↦ ?_⟩
  let input := (Tape.init ((encITerms l).map Γ.ofBool)).move Dir3.right
  let answer := decide (2 * primeRootSum (toPolyZ l) (streamCutoff C₀ (encITerms l)) <
    3 * primeCountBelow (streamCutoff C₀ (encITerms l)))
  have hpark : TM.Parked input := by
    refine ⟨by simp [input, Tape.move, Tape.init], ?_⟩
    exact Tape.init_ofBool_move_right_cells_ne_start _
  obtain ⟨hprefix, c, t, ht, hreach, hhalt, hout⟩ := binaryRoutine_bit_decisionSpace
    section3BinaryCore section3BinaryCore_sound (section3CoreValues C₀ l)
    input TM.parkedBlank (encITerms l).length 1 answer (section3BinaryCore_requires C₀ l)
    hpark le_rfl (by simp [input, Tape.move, Tape.init]) TM.outAcc_nil_of_parkedBlank
    (section3BinaryCore_emitted C₀ l)
  refine ⟨?_, c, t, ht, hreach, hhalt, ?_⟩
  · intro d hd
    have h := hprefix d hd
    have hb := hspace l
    have hbudget : max (section3BinaryCore.spaceBound 1 (section3CoreValues C₀ l)) 1 ≤
        A * (encITerms l).length + (B + 1) := by omega
    exact ⟨h.1.mono le_rfl hbudget, h.2.trans (Nat.add_le_add_right hbudget 1)⟩
  · rw [hout]
    have hbool : Γ.ofBool answer = Γ.one ↔
        2 * primeRootSum (toPolyZ l) (streamCutoff C₀ (encITerms l)) <
          3 * primeCountBelow (streamCutoff C₀ (encITerms l)) := by
      by_cases h : 2 * primeRootSum (toPolyZ l) (streamCutoff C₀ (encITerms l)) <
          3 * primeCountBelow (streamCutoff C₀ (encITerms l)) <;>
        simp [answer, h, Γ.ofBool]
    rw [hbool, streamCutoff_encITerms C₀ l hl]
    exact (integer_irreducible_iff_primeCounting_threshold_of_uniform_estimate
      C₀ (toPolyZ l) hC hf hdegree hExternal).symm

end SparseIrred.UpperBounds.Machine
