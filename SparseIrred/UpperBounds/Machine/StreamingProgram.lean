import SparseIrred.UpperBounds.Machine.CutoffParameters
import SparseIrred.UpperBounds.Machine.EncodedVerifierFP
import SparseIrred.UpperBounds.PrimeStreaming

/-!
# Binary state of the deterministic prime/root enumeration

The rectangular enumeration visits all `p,a < X`; positions with `a ≥ p` or
nonprime `p` make no root contribution. Its two accumulators are exactly those
of Section 3.6. The enumeration stores only a binary position and two counters.
-/

open Complexity SparseDiv SparseDiv.Appendix SparseDiv.StringArith SparseGcd
open scoped BigOperators

namespace SparseIrred.UpperBounds.Machine

/-- One prime-counter increment in the rectangular scan. -/
def streamPrimeIncrement (p a : ℕ) : ℕ := if p.Prime ∧ a = 0 then 1 else 0

/-- One root-counter increment, including the extra contribution of a multiple root. -/
def streamRootIncrement (s : List Bool) (p a : ℕ) : ℕ :=
  if p.Prime ∧ a < p ∧
      isZeroBits (sparseEvalModStr false (encNat p) (encNat a) s) = [true] then
    1 + if isZeroBits (sparseEvalModStr true (encNat p) (encNat a) s) = [true] then 1 else 0
  else 0

/-- The mathematical invariant of the two binary accumulators after `t` positions. -/
def streamCounts (s : List Bool) (X t : ℕ) : ℕ × ℕ :=
  (∑ i ∈ Finset.range t, streamPrimeIncrement (i / X) (i % X),
   ∑ i ∈ Finset.range t, streamRootIncrement s (i / X) (i % X))

/-- String implementation of the prime-counter increment. -/
def streamPrimeIncrementStr (p a : List Bool) : List Bool :=
  caseBit₀ (andBit (binaryPrimeFlag p) (isZeroBits a)) [true] []

/-- String implementation of the root-counter increment. -/
def streamRootIncrementStr (s p a : List Bool) : List Bool :=
  caseBit₀ (andBit (andBit (binaryPrimeFlag p) (ltBits a p))
      (isZeroBits (sparseEvalModStr false p a s)))
    (caseBit₀ (isZeroBits (sparseEvalModStr true p a s)) (encNat 2) [true]) []

/-- Final threshold comparison together with all canonical-input boundary cases. -/
def streamVerdictStr (s P A : List Bool) : List Bool :=
  caseBit₀ (validCode s)
    (caseBit₀ (isZeroBits (degreeStr s)) (binaryPrimeFlag (contentStr s))
      (andBit (eqBits (contentStr s) [true])
        (ltBits (mulBits (encNat 2) A) (mulBits (encNat 3) P)))) [false]

def streamVerdict (s : List Bool) (P A : ℕ) : Bool :=
  (streamVerdictStr s (encNat P) (encNat A)).headD false

/-- A running state carries its input, cutoff, position, and two accumulators. -/
def streamRunCode (s : List Bool) (X t P A : ℕ) : List Bool :=
  false :: false :: pair s (pair (encNat X) (pair (encNat t) (pair (encNat P) (encNat A))))

/-- The stop marker is followed by the computed verdict. -/
def streamDoneCode (answer : Bool) : List Bool := [true, answer]

/-- The bounded unary width gives a binary encoding of its power of two. -/
def streamCutoffStr (C₀ : ℕ) (s : List Bool) : List Bool :=
  List.replicate (cutoffUnary C₀ s).length false ++ [true]

def streamCutoff (C₀ : ℕ) (s : List Bool) : ℕ := 2 ^ (cutoffUnary C₀ s).length

/-- First state, before examining any prime or residue. -/
def streamInitStr (C₀ : ℕ) (s : List Bool) : List Bool :=
  false :: false :: pair s (pair (streamCutoffStr C₀ s) (pair [] (pair [] [])))

/-- The running-state transition uses binary quotient/remainder to enumerate pairs. -/
def streamAdvanceStr (z : List Bool) : List Bool :=
  let s := pairFst z
  let X := pairFst (pairSnd z)
  let t := pairFst (pairSnd (pairSnd z))
  let P := pairFst (pairSnd (pairSnd (pairSnd z)))
  let A := pairSnd (pairSnd (pairSnd (pairSnd z)))
  let p := canonBits (divStr t X)
  let a := canonBits (redStr t X)
  caseBit₀ (ltBits t (mulBits X X))
    (false :: false :: pair s (pair X (pair (canonBits (succBits t))
      (pair (canonBits (addBits P (streamPrimeIncrementStr p a)))
        (canonBits (addBits A (streamRootIncrementStr s p a)))))))
    (true :: streamVerdictStr s P A)

/-- Total transition of the deterministic streaming state machine.
The library's initial encoding `pair [] x` is the tag `false,true` followed by `x`. -/
def streamStepStr (C₀ : ℕ) (state : List Bool) : List Bool :=
  caseBit₀ state state.tail
    (caseBit₀ state.tail (streamInitStr C₀ (state.drop 2))
      (streamAdvanceStr (state.drop 2)))

end SparseIrred.UpperBounds.Machine
