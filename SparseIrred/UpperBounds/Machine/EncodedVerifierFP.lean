import SparseIrred.UpperBounds.Machine.CodeValidation
import SparseIrred.UpperBounds.Machine.ExecutableBranch
import SparseIrred.UpperBounds.Machine.WitnessFP

/-!
# Polynomial-time verification of complete encoded branches

The verifier checks the canonical sparse code, handles signed-prime constants,
rejects nonprimitive nonconstant inputs, and otherwise runs the eight-mode verifier.
Its polynomial-time proof uses only the cited binary primality theorem. No correctness
or running-time assumption about the complete verifier is introduced.
-/

open Polynomial Complexity SparseDiv SparseDiv.Appendix SparseDiv.StringArith SparseGcd

namespace SparseIrred.UpperBounds.Machine

/-- The full six-input string verifier, including every deterministic boundary branch. -/
def encodedVerifierStr (s mode p a b coin : List Bool) : List Bool :=
  caseBit₀ (validCode s)
    (caseBit₀ (isZeroBits (degreeStr s))
      (binaryPrimeFlag (contentStr s))
      (caseBit₀ (eqBits (contentStr s) [true]) (primeMajorityStr s mode p a b coin) [false]))
    [false]

/-- Polynomial-time closure assembles the complete verifier from its verified components. -/
theorem cobham_encodedVerifierStr_comp (hAKS : BinaryPrimalityInFP) {n : ℕ}
    {gs gm gp ga gb gc : (Fin n → List Bool) → List Bool}
    (hs : Cobham gs) (hm : Cobham gm) (hp : Cobham gp) (ha : Cobham ga)
    (hb : Cobham gb) (hc : Cobham gc) :
    Cobham fun v ↦ encodedVerifierStr (gs v) (gm v) (gp v) (ga v) (gb v) (gc v) := by
  have hv : Cobham fun v ↦ validCode (gs v) :=
    (Cobham.comp (FP_subset_CobhamFP validCode_mem_FP) fun _ : Fin 1 ↦ hs).of_eq fun _ ↦ rfl
  have hd : Cobham fun v ↦ degreeStr (gs v) :=
    (Cobham.comp (FP_subset_CobhamFP degreeStr_mem_FP) fun _ : Fin 1 ↦ hs).of_eq fun _ ↦ rfl
  have hcontent : Cobham fun v ↦ contentStr (gs v) :=
    (Cobham.comp (FP_subset_CobhamFP contentStr_mem_FP) fun _ : Fin 1 ↦ hs).of_eq fun _ ↦ rfl
  exact Cobham.iteFn hv (Cobham.iteFn (cobham_isZeroBits_comp hd)
    (cobham_binaryPrimeFlag_comp hAKS hcontent)
    (Cobham.iteFn (cobham_eqBits_comp hcontent (Cobham.const [true]))
      (cobham_primeMajorityStr_comp hAKS hs hm hp ha hb hc) (Cobham.const [false])))
    (Cobham.const [false])

/-- The complete verifier belongs to Cobham's algebra with its six explicit inputs. -/
theorem cobham_encodedVerifierStr (hAKS : BinaryPrimalityInFP) :
    Cobham fun v : Fin 6 → List Bool ↦
      encodedVerifierStr (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) :=
  cobham_encodedVerifierStr_comp hAKS (.proj 0) (.proj 1) (.proj 2) (.proj 3)
    (.proj 4) (.proj 5)

/-- An actual polynomial-time deterministic transducer realizes the complete verifier. -/
theorem encodedVerifierStr_mem_FPn (hAKS : BinaryPrimalityInFP) :
    Cobham.FPn fun v : Fin 6 → List Bool ↦
      encodedVerifierStr (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) :=
  Cobham.cobham_iff_FPn.mp (cobham_encodedVerifierStr hAKS)

/-- Numeric equality flags ignore harmless padding in a binary numeral. -/
theorem eqBits_eq_decide_decNat (a b : List Bool) :
    eqBits a b = [decide (decNat a = decNat b)] := by
  rcases eqBits_flag a b with h | h
  · rw [h, decide_eq_true ((eqBits_eq_true_iff a b).mp h)]
  · rw [h, decide_eq_false (by
      intro heq
      have ht := (eqBits_eq_true_iff a b).mpr heq
      rw [h] at ht
      simp at ht)]

/-- On constant canonical inputs the content is the absolute value of the constant. -/
theorem contentZ_eq_natAbs_constant (l : ITerms) (hl : NormalizedZ l)
    (hd : degreeZ l = 0) : contentZ l = (termConstantCoefficient l).natAbs := by
  have hpoly : toPolyZ l = C ((toPolyZ l).coeff 0) :=
    eq_C_of_natDegree_le_zero (by rw [natDegree_toPolyZ_of_normalizedZ hl, hd])
  have hcontent := contentZ_eq_content hl
  rw [hpoly, content_C, ← Int.abs_eq_normalize] at hcontent
  have h := congrArg Int.natAbs hcontent
  simpa only [Int.natAbs_natCast, Int.natAbs_abs, termConstantCoefficient_eq] using h

/-- The exact code validator returns the false flag on every decoding failure. -/
theorem validCode_eq_false_of_decode_none (s : List Bool) (h : decodeTerms s = none) :
    validCode s = [false] := by
  rcases Cobham.eqFlag_flag (canonicalCode s) s with hv | hv
  · have hex := (validCode_eq_true_iff s).mp hv
    obtain ⟨l, hl⟩ := hex
    rw [h] at hl
    contradiction
  · exact hv

/-- On canonical term lists all string branches agree with the executable term decision. -/
theorem encodedVerifierStr_encITerms (l : ITerms) (hl : NormalizedZ l)
    (mode p a : List Bool) (b coin : Bool) :
    encodedVerifierStr (encITerms l) mode p a [b] [coin] =
      [executableTermDecision l (decNat mode) (decNat p) (decNat a) b coin] := by
  have hvalid : validCode (encITerms l) = [true] :=
    (validCode_eq_true_iff _).mpr ⟨l, (decodeTerms_eq_some_iff _ _).mpr ⟨hl, rfl⟩⟩
  simp only [encodedVerifierStr, hvalid, caseBit₀_cons, Bool.cond_true,
    isZeroBits_eq_decide_decNat, decNat_degreeStr, binaryPrimeFlag, decNat_contentStr,
    eqBits_eq_decide_decNat, decNat_cons, decNat_nil, primeMajorityStr_eq]
  by_cases hd : degreeZ l = 0
  · simp [hd, contentZ_eq_natAbs_constant l hl hd, executableTermDecision]
  · by_cases hc : contentZ l = 1 <;> simp [hd, hc, executableTermDecision]

/-- Every binary input is handled exactly as in the verified executable decision function. -/
theorem encodedVerifierStr_eq (s mode p a : List Bool) (b coin : Bool) :
    encodedVerifierStr s mode p a [b] [coin] =
      [executableEncodedDecision s (decNat mode) (decNat p) (decNat a) b coin] := by
  cases hdecode : decodeTerms s with
  | none =>
      simp [encodedVerifierStr, validCode_eq_false_of_decode_none s hdecode,
        executableEncodedDecision, hdecode]
  | some l =>
      obtain ⟨hl, hs⟩ := (decodeTerms_eq_some_iff s l).mp hdecode
      rw [executableEncodedDecision, hdecode]
      rw [← hs]
      exact encodedVerifierStr_encITerms l hl mode p a b coin

end SparseIrred.UpperBounds.Machine
