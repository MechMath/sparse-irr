import SparseIrred.UpperBounds.Section4.BinaryAddressFrobenius
import SparseIrred.UpperBounds.Section4.EntryMachinePolynomialEncoding

/-! # A uniform polynomial-time decoder for every polynomial-test instruction -/

namespace SparseIrred.UpperBounds.Section4

open Complexity SparseDiv SparseDiv.StringArith SparseGcd Matrix Polynomial

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def binaryNatDiv (a b : List Bool) : List Bool := canonBits (divBits a b)
def binaryNatMod (a b : List Bool) : List Bool := canonBits (modBits a b)

theorem binaryNatDiv_enc (a b : ℕ) (hb : b ≠ 0) :
    binaryNatDiv (encNat a) (encNat b) = encNat (a / b) := by
  simp [binaryNatDiv, canonBits, decNat_divBits (encNat a) (encNat b) (by simpa using hb)]
theorem binaryNatMod_enc (a b : ℕ) (hb : b ≠ 0) :
    binaryNatMod (encNat a) (encNat b) = encNat (a % b) := by
  simp [binaryNatMod, canonBits, decNat_modBits (encNat a) (encNat b) (by simpa using hb)]

def binaryMinorWidth (dim : List Bool) : List Bool :=
  binaryNatAdd (binaryNatSub dim (encNat 1)) (encNat 1)

def binaryMinorSearchLeaf (companion : List Bool → List Bool)
    (dim q zero one negOne query : List Bool) : List Bool :=
  let width := binaryMinorWidth dim
  binaryTestInstruction
    (binaryMinorInstruction companion dim q zero one negOne
      (binaryNatDiv (pairFst query) width) (binaryNatMod (pairFst query) width))
    [false, false, false] (pairSnd query)

def binaryMinorSearchInstruction (companion : List Bool → List Bool)
    (dim q zero one negOne addr : List Bool) : List Bool :=
  let width := binaryMinorWidth dim
  binaryOrInstruction (binaryMinorSearchLeaf companion dim q zero one negOne)
    (binaryNatMul width width) [false, false] addr

def binaryPositiveInstruction (sylvester companion : List Bool → List Bool)
    (dim derivDim q zero one negOne addr : List Bool) : List Bool :=
  let sylDim := binaryNatAdd dim derivDim
  let width := binaryMinorWidth dim
  binaryBinaryInstruction .mul
    (binaryTestInstruction (binaryBerkowitzInstruction sylvester sylDim zero one negOne
      (binaryParitySign sylDim one negOne)) [false, false])
    (binaryMinorSearchInstruction companion dim q zero one negOne)
    [false, false] (binaryOrRange (encNat 0) (binaryNatMul width width)) addr

/-- Only individual Sylvester and companion entries remain as coefficient-arithmetic callbacks. -/
def polynomialInstructionStr (sylvester companion : List Bool → List Bool)
    (dim derivDim q zero one negOne addr : List Bool) : List Bool :=
  binaryEq dim (encNat 0) (binaryValue [true, false, false])
    (binaryBit addr
      (binaryLift [true] (binaryPositiveInstruction sylvester companion
        dim derivDim q zero one negOne addr.tail))
      (binaryValue [true, false, false]))

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem binaryMinorSearchLeaf_eq (f : K[X]) (hf : 0 < f.natDegree)
    (er : K → List Bool) (companion : List Bool → List Bool)
    (hc : ∀ i j, companion (pair (encNat i.val) (encNat j.val)) = er (coefficientCompanion f i j))
    (k : Fin ((f.natDegree - 1 + 1) * (f.natDegree - 1 + 1)))
    (a : TestAddress (FrobeniusMinorAddress f.natDegree)) :
    binaryMinorSearchLeaf companion (encNat f.natDegree) (encNat (Fintype.card K))
      (er 0) (er 1) (er (-1))
      (pair (encNat k.val) (a.binaryCode frobeniusMinorCode)) =
      ((nonzeroProgram (minorProgram f hf (minorPair _ k).1 (minorPair _ k).2)
        (minorInitial f.natDegree)).instruction a).binaryCode
        (TestAddress.binaryCode frobeniusMinorCode) (DecisionScalar.binaryCode er) := by
  unfold binaryMinorSearchLeaf binaryMinorWidth
  rw [binaryNatSub_enc, binaryNatAdd_enc]
  dsimp only
  rw [pairFst_pair, pairSnd_pair, binaryNatDiv_enc _ _ (by omega),
    binaryNatMod_enc _ _ (by omega)]
  apply binaryTestInstruction_eq
    (minorProgram f hf (minorPair _ k).1 (minorPair _ k).2) (minorInitial f.natDegree)
    frobeniusMinorCode er
  intro a
  simpa [minorPair, finProdFinEquiv] using binaryMinorInstruction_eq f hf er companion hc
    (minorPair _ k).1 (minorPair _ k).2 a

theorem binaryMinorSearchInstruction_eq (f : K[X]) (hf : 0 < f.natDegree)
    (er : K → List Bool) (companion : List Bool → List Bool)
    (hc : ∀ i j, companion (pair (encNat i.val) (encNat j.val)) = er (coefficientCompanion f i j))
    (a : MinorSearchAddress f.natDegree) :
    binaryMinorSearchInstruction companion (encNat f.natDegree) (encNat (Fintype.card K))
      (er 0) (er 1) (er (-1)) (minorSearchCode _ a) =
      ((minorSearchProgram f hf).instruction a).binaryCode (minorSearchCode _) (DecisionScalar.binaryCode er) := by
  unfold binaryMinorSearchInstruction binaryMinorWidth
  rw [binaryNatSub_enc, binaryNatAdd_enc]
  dsimp only
  rw [binaryNatMul_enc]
  apply binaryOrInstruction_eq
  · intro; rfl
  · exact binaryMinorSearchLeaf_eq f hf er companion hc

theorem binaryPositiveInstruction_eq (f : K[X]) (hf : 0 < f.natDegree)
    (er : K → List Bool) (sylvester companion : List Bool → List Bool)
    (hs : ∀ i j : Fin (f.natDegree + f.derivative.natDegree),
      sylvester (pair (encNat i.val) (encNat j.val)) = er (coefficientSylvesterEntry f i.val j.val))
    (hc : ∀ i j, companion (pair (encNat i.val) (encNat j.val)) = er (coefficientCompanion f i j))
    (a : PositivePolynomialAddress f.natDegree f.derivative.natDegree) :
    binaryPositiveInstruction sylvester companion (encNat f.natDegree) (encNat f.derivative.natDegree)
      (encNat (Fintype.card K)) (er 0) (er 1) (er (-1)) (positivePolynomialCode _ _ a) =
      ((positivePolynomialProgram f hf).instruction a).binaryCode
        (positivePolynomialCode _ _) (DecisionScalar.binaryCode er) := by
  unfold binaryPositiveInstruction binaryMinorWidth
  rw [binaryNatAdd_enc, binaryNatSub_enc, binaryNatAdd_enc]
  dsimp only
  rw [binaryParitySign_eq, binaryNatMul_enc]
  have hinit : (minorSearchCode f.natDegree) (minorSearchInitial f.natDegree) =
      binaryOrRange (encNat 0) (encNat ((f.natDegree - 1 + 1) * (f.natDegree - 1 + 1))) := by
    simp [minorSearchCode, minorSearchInitial, OrAddress.binaryCode, binaryOrRange,
      ← binaryFields_encNat]
  rw [← hinit]
  apply binaryBinaryInstruction_eq .mul (nonzeroProgram (sylvesterProgram f) .initial)
    (minorSearchProgram f hf) .test (minorSearchInitial f.natDegree)
  · intro a
    apply binaryTestInstruction_eq (sylvesterProgram f) .initial BerkowitzAddress.binaryCode er
    exact binaryBerkowitzInstruction_eq _ er sylvester hs
  · exact binaryMinorSearchInstruction_eq f hf er companion hc

theorem polynomialInstructionStr_eq (f : K[X]) (er : K → List Bool)
    (sylvester companion : List Bool → List Bool)
    (hs : ∀ i j : Fin (f.natDegree + f.derivative.natDegree),
      sylvester (pair (encNat i.val) (encNat j.val)) = er (coefficientSylvesterEntry f i.val j.val))
    (hc : ∀ i j, companion (pair (encNat i.val) (encNat j.val)) = er (coefficientCompanion f i j))
    (a : PolynomialAddress f.natDegree f.derivative.natDegree) :
    polynomialInstructionStr sylvester companion (encNat f.natDegree) (encNat f.derivative.natDegree)
      (encNat (Fintype.card K)) (er 0) (er 1) (er (-1)) (polynomialAddressCode _ _ a) =
      ((polynomialProgram f).instruction a).binaryCode
        (polynomialAddressCode _ _) (DecisionScalar.binaryCode er) := by
  by_cases hf : 0 < f.natDegree
  · have hne : f.natDegree ≠ 0 := by omega
    cases a with
    | none => simp [polynomialInstructionStr, binaryEq, hne, polynomialAddressCode,
        binaryBit, binaryValue, polynomialProgram, hf, optionProgram,
        EntryInstruction.binaryCode, DecisionScalar.binaryCode]
    | some a =>
      simp only [polynomialInstructionStr, binaryEq, decNat_encNat, hne, ↓reduceIte,
        polynomialAddressCode, binaryBit, List.headD_cons, List.tail_cons,
        binaryPositiveInstruction_eq f hf er sylvester companion hs hc]
      have h := binaryLift_eq (positivePolynomialCode _ _) (polynomialAddressCode _ _)
        (DecisionScalar.binaryCode er) some [true] (fun _ ↦ rfl)
        ((positivePolynomialProgram f hf).instruction a)
      cases hp : (positivePolynomialProgram f hf).instruction a <;>
        simpa [polynomialProgram, hf, optionProgram, hp] using h
  · have hzero : f.natDegree = 0 := by omega
    simp [polynomialInstructionStr, binaryEq, hzero, binaryValue, polynomialProgram,
      EntryInstruction.binaryCode, DecisionScalar.binaryCode]

theorem cobham_binaryNatDiv {n : ℕ} {a b : (Fin n → List Bool) → List Bool}
    (ha : Cobham a) (hb : Cobham b) : Cobham fun v ↦ binaryNatDiv (a v) (b v) :=
  cobham_canonBits_comp (cobham_divBits_comp ha hb)
theorem cobham_binaryNatMod {n : ℕ} {a b : (Fin n → List Bool) → List Bool}
    (ha : Cobham a) (hb : Cobham b) : Cobham fun v ↦ binaryNatMod (a v) (b v) :=
  cobham_canonBits_comp (cobham_modBits_comp ha hb)
theorem cobham_binaryMinorWidth {n : ℕ} {d : (Fin n → List Bool) → List Bool}
    (hd : Cobham d) : Cobham fun v ↦ binaryMinorWidth (d v) :=
  cobham_binaryNatAdd (cobham_binaryNatSub hd (.const (encNat 1))) (.const (encNat 1))

theorem cobham_binaryMinorSearchLeaf {n : ℕ}
    {companion : (Fin n → List Bool) → List Bool → List Bool} (hc : BinaryCobhamFamily companion)
    {dim q zero one negOne query : (Fin n → List Bool) → List Bool}
    (hd : Cobham dim) (hq : Cobham q) (hz : Cobham zero) (ho : Cobham one)
    (hn : Cobham negOne) (ha : Cobham query) :
    Cobham fun v ↦ binaryMinorSearchLeaf (companion v) (dim v) (q v) (zero v)
      (one v) (negOne v) (query v) := by
  have hw := cobham_binaryMinorWidth hd
  have hk := cobham_pairFst_comp ha
  apply cobham_binaryTestInstruction (n := n)
    (inner := fun v ↦ binaryMinorInstruction (companion v) (dim v) (q v) (zero v) (one v) (negOne v)
      (binaryNatDiv (pairFst (query v)) (binaryMinorWidth (dim v)))
      (binaryNatMod (pairFst (query v)) (binaryMinorWidth (dim v))))
  · intro g hg
    exact cobham_binaryMinorInstruction hc hd hq hz ho hn
      (cobham_binaryNatDiv hk hw) (cobham_binaryNatMod hk hw) hg
  · exact .const [false, false, false]
  · exact cobham_pairSnd_comp ha

theorem cobham_binaryMinorSearchInstruction {n : ℕ}
    {companion : (Fin n → List Bool) → List Bool → List Bool} (hc : BinaryCobhamFamily companion)
    {dim q zero one negOne addr : (Fin n → List Bool) → List Bool}
    (hd : Cobham dim) (hq : Cobham q) (hz : Cobham zero) (ho : Cobham one)
    (hn : Cobham negOne) (ha : Cobham addr) :
    Cobham fun v ↦ binaryMinorSearchInstruction (companion v) (dim v) (q v) (zero v)
      (one v) (negOne v) (addr v) :=
  cobham_binaryOrInstruction (n := n)
    (inner := fun v ↦ binaryMinorSearchLeaf (companion v) (dim v) (q v) (zero v) (one v) (negOne v))
    (fun _ h ↦ cobham_binaryMinorSearchLeaf hc hd hq hz ho hn h)
    (cobham_binaryNatMul (cobham_binaryMinorWidth hd) (cobham_binaryMinorWidth hd))
    (.const [false, false]) ha

theorem cobham_binaryPositiveInstruction {n : ℕ}
    {sylvester companion : (Fin n → List Bool) → List Bool → List Bool}
    (hs : BinaryCobhamFamily sylvester) (hc : BinaryCobhamFamily companion)
    {dim derivDim q zero one negOne addr : (Fin n → List Bool) → List Bool}
    (hd : Cobham dim) (he : Cobham derivDim) (hq : Cobham q) (hz : Cobham zero) (ho : Cobham one)
    (hn : Cobham negOne) (ha : Cobham addr) :
    Cobham fun v ↦ binaryPositiveInstruction (sylvester v) (companion v) (dim v) (derivDim v)
      (q v) (zero v) (one v) (negOne v) (addr v) := by
  have hsum := cobham_binaryNatAdd hd he
  have hw := cobham_binaryMinorWidth hd
  apply cobham_binaryBinaryInstruction (n := n) .mul
    (left := fun v ↦ binaryTestInstruction
      (binaryBerkowitzInstruction (sylvester v) (binaryNatAdd (dim v) (derivDim v))
        (zero v) (one v) (negOne v)
        (binaryParitySign (binaryNatAdd (dim v) (derivDim v)) (one v) (negOne v))) [false, false])
    (right := fun v ↦ binaryMinorSearchInstruction (companion v) (dim v) (q v) (zero v) (one v) (negOne v))
  · intro g hg
    apply cobham_binaryTestInstruction (n := n)
      (inner := fun v ↦ binaryBerkowitzInstruction (sylvester v) (binaryNatAdd (dim v) (derivDim v))
        (zero v) (one v) (negOne v)
        (binaryParitySign (binaryNatAdd (dim v) (derivDim v)) (one v) (negOne v)))
    · intro g' hg'
      exact cobham_binaryBerkowitzInstruction hs hsum hz ho hn
        (cobham_binaryParitySign hsum ho hn) hg'
    · exact .const [false, false]
    · exact hg
  · intro g hg
    exact cobham_binaryMinorSearchInstruction hc hd hq hz ho hn hg
  · exact .const [false, false]
  · exact cobham_binaryOrRange (.const (encNat 0)) (cobham_binaryNatMul hw hw)
  · exact ha

/-- All instruction dispatch, including malformed strings, is a single uniform Cobham function. -/
theorem cobham_polynomialInstructionStr {n : ℕ}
    {sylvester companion : (Fin n → List Bool) → List Bool → List Bool}
    (hs : BinaryCobhamFamily sylvester) (hc : BinaryCobhamFamily companion)
    {dim derivDim q zero one negOne addr : (Fin n → List Bool) → List Bool}
    (hd : Cobham dim) (he : Cobham derivDim) (hq : Cobham q) (hz : Cobham zero) (ho : Cobham one)
    (hn : Cobham negOne) (ha : Cobham addr) :
    Cobham fun v ↦ polynomialInstructionStr (sylvester v) (companion v) (dim v) (derivDim v)
      (q v) (zero v) (one v) (negOne v) (addr v) :=
  cobham_binaryEq hd (.const (encNat 0)) (.const (binaryValue [true, false, false]))
    (cobham_binaryBit ha
      (cobham_binaryLift [true] (cobham_binaryPositiveInstruction hs hc hd he hq hz ho hn
        (cobham_binaryTail ha))) (.const (binaryValue [true, false, false])))

end SparseIrred.UpperBounds.Section4
