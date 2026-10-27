import SparseIrred.UpperBounds.Machine.ModularVerifier
import SparseIrred.UpperBounds.Machine.ExecutableWitness

/-!
# Polynomial-time implementation of the Section 3.7 branch verifier

Only binary primality testing is supplied by the cited AKS theorem. Sparse evaluation,
derivative evaluation, witness predicates and the eight-mode selection are assembled
from already verified polynomial-time string functions. The external hypothesis does
not concern irreducibility, the majority threshold or the complete verifier.
-/

open Polynomial Complexity SparseDiv SparseDiv.StringArith SparseDiv.Appendix SparseGcd

namespace SparseIrred.UpperBounds

/-- The exact output flag of binary primality testing. -/
def binaryPrimeFlag (p : List Bool) : List Bool := [decide (decNat p).Prime]

/-- The cited AKS result, stated for the binary encoding used by this project. -/
def BinaryPrimalityInFP : Prop := binaryPrimeFlag ∈ FP

theorem cobham_binaryPrimeFlag_comp (hAKS : BinaryPrimalityInFP) {n : ℕ}
    {gp : (Fin n → List Bool) → List Bool} (hp : Cobham gp) :
    Cobham fun v ↦ binaryPrimeFlag (gp v) :=
  (Cobham.comp (FP_subset_CobhamFP hAKS) fun _ : Fin 1 ↦ hp).of_eq fun _ ↦ rfl

/-- The unique positive witness tag attached to each prime. -/
def positivePrimeWitnessStr (p a b : List Bool) : List Bool :=
  andBit (andBit (binaryPrimeFlag p) (isZeroBits a)) (notBit b)

/-- Negative witnesses count an ordinary root once and a multiple root twice. -/
def negativePrimeWitnessStr (s p a b : List Bool) : List Bool :=
  andBit (andBit (andBit (binaryPrimeFlag p) (ltBits a p))
    (isZeroBits (sparseEvalModStr false p a s)))
    (orBit (notBit b) (isZeroBits (sparseEvalModStr true p a s)))

/-- The complete eight-mode verifier on a supplied random branch. -/
def primeMajorityStr (s mode p a b coin : List Bool) : List Bool :=
  caseBit₀ (ltBits mode (encNat 3))
    (orBit (positivePrimeWitnessStr p a b) coin)
    (caseBit₀ (ltBits mode (encNat 5))
      (andBit (notBit (negativePrimeWitnessStr s p a b)) coin)
      (notBit (notBit coin)))

theorem cobham_positivePrimeWitnessStr_comp (hAKS : BinaryPrimalityInFP) {n : ℕ}
    {gp ga gb : (Fin n → List Bool) → List Bool}
    (hp : Cobham gp) (ha : Cobham ga) (hb : Cobham gb) :
    Cobham fun v ↦ positivePrimeWitnessStr (gp v) (ga v) (gb v) :=
  Cobham.andFn (Cobham.andFn (cobham_binaryPrimeFlag_comp hAKS hp)
    (cobham_isZeroBits_comp ha)) (Cobham.notFn hb)

theorem cobham_negativePrimeWitnessStr_comp (hAKS : BinaryPrimalityInFP) {n : ℕ}
    {gs gp ga gb : (Fin n → List Bool) → List Bool}
    (hs : Cobham gs) (hp : Cobham gp) (ha : Cobham ga) (hb : Cobham gb) :
    Cobham fun v ↦ negativePrimeWitnessStr (gs v) (gp v) (ga v) (gb v) :=
  Cobham.andFn (Cobham.andFn (Cobham.andFn (cobham_binaryPrimeFlag_comp hAKS hp)
    (cobham_ltBits_comp ha hp))
    (cobham_isZeroBits_comp (cobham_sparseEvalModStr_comp false hp ha hs)))
    (Cobham.orFn (Cobham.notFn hb)
      (cobham_isZeroBits_comp (cobham_sparseEvalModStr_comp true hp ha hs)))

theorem cobham_primeMajorityStr_comp (hAKS : BinaryPrimalityInFP) {n : ℕ}
    {gs gm gp ga gb gc : (Fin n → List Bool) → List Bool}
    (hs : Cobham gs) (hm : Cobham gm) (hp : Cobham gp) (ha : Cobham ga)
    (hb : Cobham gb) (hc : Cobham gc) :
    Cobham fun v ↦ primeMajorityStr (gs v) (gm v) (gp v) (ga v) (gb v) (gc v) :=
  Cobham.iteFn (cobham_ltBits_comp hm (Cobham.const (encNat 3)))
    (Cobham.orFn (cobham_positivePrimeWitnessStr_comp hAKS hp ha hb) hc)
    (Cobham.iteFn (cobham_ltBits_comp hm (Cobham.const (encNat 5)))
      (Cobham.andFn (Cobham.notFn (cobham_negativePrimeWitnessStr_comp hAKS hs hp ha hb)) hc)
      (Cobham.notFn (Cobham.notFn hc)))

/-- All six inputs of the branch verifier belong to Cobham's algebra. -/
theorem cobham_primeMajorityStr (hAKS : BinaryPrimalityInFP) :
    Cobham fun v : Fin 6 → List Bool ↦
      primeMajorityStr (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) :=
  cobham_primeMajorityStr_comp hAKS (.proj 0) (.proj 1) (.proj 2) (.proj 3) (.proj 4) (.proj 5)

/-- An actual polynomial-time transducer exists for the fixed-arity encoded verifier. -/
theorem primeMajorityStr_mem_FPn (hAKS : BinaryPrimalityInFP) :
    Cobham.FPn fun v : Fin 6 → List Bool ↦
      primeMajorityStr (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) :=
  Cobham.cobham_iff_FPn.mp (cobham_primeMajorityStr hAKS)

theorem isZeroBits_eq_decide_decNat (a : List Bool) :
    isZeroBits a = [decide (decNat a = 0)] := by
  rcases isZeroBits_flag a with h | h
  · rw [h, decide_eq_true ((isZeroBits_eq_true_iff a).mp h)]
  · rw [h, decide_eq_false (by
      intro hz
      have ht := (isZeroBits_eq_true_iff a).mpr hz
      rw [h] at ht
      simp at ht)]

theorem ltBits_eq_decide_decNat (a b : List Bool) :
    ltBits a b = [decide (decNat a < decNat b)] := by
  rcases ltBits_flag a b with h | h
  · rw [h, decide_eq_true ((ltBits_eq_true_iff a b).mp h)]
  · rw [h, decide_eq_false (Nat.not_lt.mpr ((ltBits_eq_false_iff a b).mp h))]

theorem positivePrimeWitnessStr_eq (p a : List Bool) (b : Bool) :
    positivePrimeWitnessStr p a [b] = [executablePositivePrimeWitness (decNat p) (decNat a) b] := by
  simp [positivePrimeWitnessStr, binaryPrimeFlag, isZeroBits_eq_decide_decNat,
    executablePositivePrimeWitness]

theorem negativePrimeWitnessStr_eq (l : ITerms) (p a : List Bool) (b : Bool) :
    negativePrimeWitnessStr (encITerms l) p a [b] =
      [executableNegativePrimeWitness l (decNat p) (decNat a) b] := by
  by_cases hp : (decNat p).Prime
  · simp [negativePrimeWitnessStr, binaryPrimeFlag, ltBits_eq_decide_decNat,
      sparseEvalModStr_zero_flag _ p a l hp.ne_zero, executableNegativePrimeWitness,
      executableModularEval_eq, executableModularDerivativeEval_eq]
  · simp [negativePrimeWitnessStr, binaryPrimeFlag, hp, executableNegativePrimeWitness,
      andBit]

/-- The concrete string verifier computes the previously verified executable branch exactly. -/
theorem primeMajorityStr_eq (l : ITerms) (mode p a : List Bool) (b coin : Bool) :
    primeMajorityStr (encITerms l) mode p a [b] [coin] =
      [executablePrimeMajority l (decNat mode) (decNat p) (decNat a) b coin] := by
  simp only [primeMajorityStr, ltBits_eq_decide_decNat, decNat_encNat,
    positivePrimeWitnessStr_eq, negativePrimeWitnessStr_eq, orBit_single,
    notBit_single, andBit_single, Bool.not_not, caseBit₀_cons]
  unfold executablePrimeMajority
  by_cases h3 : decNat mode < 3 <;> by_cases h5 : decNat mode < 5 <;> simp [h3, h5]

end SparseIrred.UpperBounds
