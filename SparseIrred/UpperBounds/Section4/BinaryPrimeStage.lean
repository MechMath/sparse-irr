import SparseIrred.UpperBounds.Section4.BinaryInputView
import SparseIrred.UpperBounds.Section4.BinaryPrimePolynomial
import SparseIrred.UpperBounds.Section4.BinaryFieldPrimeCanonical
import SparseIrred.UpperBounds.Section4.BinaryMatrixEntries
import SparseIrred.UpperBounds.Section4.BinaryAddressPolynomial
import SparseIrred.UpperBounds.Section4.BinaryControl

/-! # Concrete polynomial-time binary realization of the modulus-validation stage -/

namespace SparseIrred.UpperBounds.Section4

set_option backward.isDefEq.respectTransparency false

open Polynomial Matrix Complexity SparseDiv SparseDiv.StringArith SparseGcd

def binaryModulusOne (s : List Bool) : List Bool := redStr [true] (binaryInputPrime s)

def binaryModulusSylvester (s query : List Bool) : List Bool :=
  sylvesterEntryStr (primePolynomialCoeffStr (binaryInputPrime s) (binaryInputModulus s))
    (primePolynomialDerivativeCoeffStr (binaryInputPrime s) (binaryInputModulus s))
    (primePolynomialDegreeStr (binaryInputModulus s))
    (primePolynomialDerivativeDegreeStr (binaryInputPrime s) (binaryInputModulus s)) [] query

def binaryModulusCompanion (s query : List Bool) : List Bool :=
  companionEntryStr (primePolynomialCoeffStr (binaryInputPrime s) (binaryInputModulus s))
    (primeMulStr (binaryInputPrime s)) (primeNegStr (binaryInputPrime s))
    (primePolynomialDegreeStr (binaryInputModulus s)) (binaryModulusOne s) []
    (binaryModulusOne s) query

def binaryModulusInstruction (s address : List Bool) : List Bool :=
  polynomialInstructionStr (binaryModulusSylvester s) (binaryModulusCompanion s)
    (primePolynomialDegreeStr (binaryInputModulus s))
    (primePolynomialDerivativeDegreeStr (binaryInputPrime s) (binaryInputModulus s))
    (binaryInputPrime s) [] (binaryModulusOne s)
    (primeNegStr (binaryInputPrime s) (binaryModulusOne s)) address

def binaryModulusAdd (s a b : List Bool) : List Bool :=
  binaryDecisionAdd (primeAddStr (binaryInputPrime s)) a b
def binaryModulusMul (s a b : List Bool) : List Bool :=
  binaryDecisionMul (primeMulStr (binaryInputPrime s)) isZeroBits a b

def binaryModulusAdvance (s cfg : List Bool) : List Bool :=
  binaryStackStep (binaryModulusInstruction s) (binaryModulusAdd s) (binaryModulusMul s) cfg

theorem cobham_binaryModulusOne {n : ℕ} {s : (Fin n → List Bool) → List Bool}
    (hs : Cobham s) : Cobham fun v ↦ binaryModulusOne (s v) :=
  cobham_redStr_comp (.const _) (cobham_binaryInputPrime hs)

theorem cobham_binaryModulusSylvester {n : ℕ} {s q : (Fin n → List Bool) → List Bool}
    (hs : Cobham s) (hq : Cobham q) :
    Cobham fun v ↦ binaryModulusSylvester (s v) (q v) := by
  have hp := cobham_binaryInputPrime hs
  have hh := cobham_binaryInputModulus hs
  exact cobham_sylvesterEntryStr
    (fun _ hi ↦ cobham_primePolynomialCoeffStr hp hh hi)
    (fun _ hi ↦ cobham_primePolynomialDerivativeCoeffStr hp hh hi)
    (cobham_primePolynomialDegreeStr hh) (cobham_primePolynomialDerivativeDegreeStr hp hh)
    (.const []) hq

theorem cobham_binaryModulusCompanion {n : ℕ} {s q : (Fin n → List Bool) → List Bool}
    (hs : Cobham s) (hq : Cobham q) :
    Cobham fun v ↦ binaryModulusCompanion (s v) (q v) := by
  have hp := cobham_binaryInputPrime hs
  have hh := cobham_binaryInputModulus hs
  have ho := cobham_binaryModulusOne hs
  exact cobham_companionEntryStr (fun _ hi ↦ cobham_primePolynomialCoeffStr hp hh hi)
    (fun _ _ ha hb ↦ cobham_primeMulStr_comp hp ha hb)
    (fun _ ha ↦ cobham_primeNegStr_comp hp ha)
    (cobham_primePolynomialDegreeStr hh) ho (.const []) ho hq

theorem cobham_binaryModulusInstruction {n : ℕ} {s a : (Fin n → List Bool) → List Bool}
    (hs : Cobham s) (ha : Cobham a) :
    Cobham fun v ↦ binaryModulusInstruction (s v) (a v) := by
  have hp := cobham_binaryInputPrime hs
  have hh := cobham_binaryInputModulus hs
  have ho := cobham_binaryModulusOne hs
  exact cobham_polynomialInstructionStr
    (fun _ hq ↦ cobham_binaryModulusSylvester hs hq)
    (fun _ hq ↦ cobham_binaryModulusCompanion hs hq)
    (cobham_primePolynomialDegreeStr hh) (cobham_primePolynomialDerivativeDegreeStr hp hh)
    hp (.const []) ho (cobham_primeNegStr_comp hp ho) ha

theorem cobham_binaryModulusAdd {n : ℕ} {s a b : (Fin n → List Bool) → List Bool}
    (hs : Cobham s) (ha : Cobham a) (hb : Cobham b) :
    Cobham fun v ↦ binaryModulusAdd (s v) (a v) (b v) :=
  cobham_binaryDecisionAdd (add := fun v ↦ primeAddStr (binaryInputPrime (s v)))
    (cobham_primeAddStr_comp
      (cobham_binaryInputPrime (TermsStr.cobham_tail_comp (TermsStr.cobham_tail_comp hs)))
      (.proj 0) (.proj 1)) ha hb

theorem cobham_binaryModulusMul {n : ℕ} {s a b : (Fin n → List Bool) → List Bool}
    (hs : Cobham s) (ha : Cobham a) (hb : Cobham b) :
    Cobham fun v ↦ binaryModulusMul (s v) (a v) (b v) :=
  cobham_binaryDecisionMul (mul := fun v ↦ primeMulStr (binaryInputPrime (s v)))
    (zero := fun _ ↦ isZeroBits)
    (cobham_primeMulStr_comp
      (cobham_binaryInputPrime (TermsStr.cobham_tail_comp (TermsStr.cobham_tail_comp hs)))
      (.proj 0) (.proj 1))
    (cobham_isZeroBits_comp (.proj 0)) ha hb

theorem cobham_binaryModulusAdvance {n : ℕ} {s cfg : (Fin n → List Bool) → List Bool}
    (hs : Cobham s) (hc : Cobham cfg) :
    Cobham fun v ↦ binaryModulusAdvance (s v) (cfg v) :=
  cobham_binaryStackStep
    (instruction := fun v ↦ binaryModulusInstruction (s v))
    (add := fun v ↦ binaryModulusAdd (s v)) (mul := fun v ↦ binaryModulusMul (s v))
    (cobham_binaryModulusInstruction (TermsStr.cobham_tail_comp hs) (.proj 0))
    (cobham_binaryModulusAdd (TermsStr.cobham_tail_comp (TermsStr.cobham_tail_comp hs))
      (.proj 0) (.proj 1))
    (cobham_binaryModulusMul (TermsStr.cobham_tail_comp (TermsStr.cobham_tail_comp hs))
      (.proj 0) (.proj 1)) hc

def binaryModulusStage : BinaryStageRoutines where
  initial _ := binaryEval [true, false, false] [false]
  advance := binaryModulusAdvance
  accept _ := binaryDecisionAsBool
  initial_cobham := .const _
  advance_cobham := cobham_binaryModulusAdvance (.proj 0) (.proj 1)
  accept_cobham := cobham_binaryDecisionAsBool (.proj 1)

theorem binaryModulusOne_correct (s : List Bool) [Fact (Input.decode s).field.characteristic.Prime] :
    binaryModulusOne s = encNat (1 : ZMod (Input.decode s).field.characteristic).val := by
  rw [binaryModulusOne, binaryInputPrime_eq, redStr_eq_zmod_val]
  change encNat ((1 : ℕ) : ZMod (Input.decode s).field.characteristic).val = _
  rw [Nat.cast_one]

theorem binaryModulusSylvester_correct (s : List Bool)
    [Fact (Input.decode s).field.characteristic.Prime]
    (hs : (Input.decode s).field.Structural) (i j : ℕ) :
    binaryModulusSylvester s (pair (encNat i) (encNat j)) =
      encNat (coefficientSylvesterEntry (Input.decode s).field.polynomial i j).val := by
  rw [binaryModulusSylvester, binaryInputPrime_eq, binaryInputModulus_eq,
    primePolynomialDegreeStr_correct _ hs, primePolynomialDerivativeDegreeStr_correct _ hs]
  have h := sylvesterEntryStr_correct (Input.decode s).field.polynomial (fun a ↦ encNat a.val)
    (primePolynomialCoeffStr (encNat (Input.decode s).field.characteristic)
      (encodeNumerals (Input.decode s).field.modulus))
    (primePolynomialDerivativeCoeffStr (encNat (Input.decode s).field.characteristic)
      (encodeNumerals (Input.decode s).field.modulus))
    (primePolynomialCoeffStr_encoded _ _) (primePolynomialDerivativeCoeffStr_encoded _ _) i j
  simpa only [FieldCode.degree, ZMod.val_zero, show encNat 0 = [] from rfl] using h

theorem binaryModulusCompanion_correct (s : List Bool)
    [Fact (Input.decode s).field.characteristic.Prime]
    (hs : (Input.decode s).field.Structural)
    (i j : Fin (Input.decode s).field.polynomial.natDegree) :
    binaryModulusCompanion s (pair (encNat i.val) (encNat j.val)) =
      encNat (coefficientCompanion (Input.decode s).field.polynomial i j).val := by
  rw [binaryModulusCompanion, binaryInputPrime_eq, binaryInputModulus_eq,
    primePolynomialDegreeStr_correct _ hs, binaryModulusOne_correct]
  have h := companionEntryStr_correct (Input.decode s).field.polynomial (fun a ↦ encNat a.val)
    (primePolynomialCoeffStr (encNat (Input.decode s).field.characteristic)
      (encodeNumerals (Input.decode s).field.modulus))
    (primeMulStr (encNat (Input.decode s).field.characteristic))
    (primeNegStr (encNat (Input.decode s).field.characteristic))
    (primePolynomialCoeffStr_encoded _ _) (primeMulStr_encoded _) (primeNegStr_encoded _) i j
  simpa only [hs.monic.leadingCoeff, inv_one, ZMod.val_zero, FieldCode.degree,
    show encNat 0 = [] from rfl] using h

theorem binaryModulusInstruction_correct (s : List Bool)
    [Fact (Input.decode s).field.characteristic.Prime]
    (hs : (Input.decode s).field.Structural)
    (a : PolynomialAddress (Input.decode s).field.polynomial.natDegree
      (Input.decode s).field.polynomial.derivative.natDegree) :
    binaryModulusInstruction s (polynomialAddressCode _ _ a) =
      ((polynomialProgram (Input.decode s).field.polynomial).instruction a).binaryCode
        (polynomialAddressCode _ _) (DecisionScalar.binaryCode (fun x ↦ encNat x.val)) := by
  rw [binaryModulusInstruction, binaryInputPrime_eq, binaryInputModulus_eq,
    primePolynomialDegreeStr_correct _ hs, primePolynomialDerivativeDegreeStr_correct _ hs,
    binaryModulusOne_correct, primeNegStr_encoded]
  have h := polynomialInstructionStr_eq (Input.decode s).field.polynomial (fun a ↦ encNat a.val)
    (binaryModulusSylvester s) (binaryModulusCompanion s)
    (fun i j ↦ binaryModulusSylvester_correct s hs i.val j.val)
    (binaryModulusCompanion_correct s hs) a
  simpa only [ZMod.card, ZMod.val_zero, FieldCode.degree, show encNat 0 = [] from rfl] using h

theorem binaryModulusAdd_correct (s : List Bool)
    [Fact (Input.decode s).field.characteristic.Prime]
    (a b : DecisionScalar (ZMod (Input.decode s).field.characteristic)) :
    binaryModulusAdd s (a.binaryCode (fun x ↦ encNat x.val))
        (b.binaryCode (fun x ↦ encNat x.val)) =
      (a + b).binaryCode (fun x ↦ encNat x.val) := by
  rw [binaryModulusAdd, binaryInputPrime_eq]
  exact binaryDecisionAdd_correct (fun x ↦ encNat x.val) _ (primeAddStr_encoded _) a b

theorem binaryModulusMul_correct (s : List Bool)
    [Fact (Input.decode s).field.characteristic.Prime]
    (a b : DecisionScalar (ZMod (Input.decode s).field.characteristic)) :
    binaryModulusMul s (a.binaryCode (fun x ↦ encNat x.val))
        (b.binaryCode (fun x ↦ encNat x.val)) =
      (a * b).binaryCode (fun x ↦ encNat x.val) := by
  rw [binaryModulusMul, binaryInputPrime_eq]
  exact binaryDecisionMul_correct (fun x ↦ encNat x.val) _ _
    (primeMulStr_encoded _) (isZeroBits_encNat_zmod_val _) a b

theorem binaryModulusAdvance_correct (s : List Bool) (h : (primeStage s).answer = true)
    (c : (modulusStage s h).ReachableCfg) :
    binaryModulusStage.advance s (modulusConfigCode s h c) =
      modulusConfigCode s h ((modulusStage s h).advance c) := by
  have := primeFactOfStage s h
  have hs := ((preflightAnswer_correct s).mp h).2.1
  exact binaryStackStep_correct (polynomialProgram (Input.decode s).field.polynomial)
    (polynomialAddressCode _ _) (DecisionScalar.binaryCode (fun x ↦ encNat x.val))
    (binaryModulusInstruction s) (binaryModulusAdd s) (binaryModulusMul s)
    (binaryModulusInstruction_correct s hs) (binaryModulusAdd_correct s)
    (binaryModulusMul_correct s) c.val

theorem binaryModulusInitial_correct (s : List Bool) (h : (primeStage s).answer = true) :
    binaryModulusStage.initial s = modulusConfigCode s h (modulusStage s h).initialCfg := rfl

theorem binaryModulusAccept_correct (s : List Bool) (h : (primeStage s).answer = true)
    (v : (modulusStage s h).Scalar) :
    binaryModulusStage.accept s
      (DecisionScalar.binaryCode (fun x : ZMod (Input.decode s).field.characteristic ↦ encNat x.val) v) =
      [(modulusStage s h).output v] := by
  exact binaryDecisionAsBool_correct _ v

/-- The validated modulus stage has a concrete binary realization; there are no
remaining implementation hypotheses in this instance. -/
theorem binaryModulusStage_realization (s : List Bool) (h : (primeStage s).answer = true) :
    BinaryStageRealization s binaryModulusStage (modulusStage s h) (modulusConfigCode s h) := by
  have := primeFactOfStage s h
  have hs := ((preflightAnswer_correct s).mp h).2.1
  apply binaryStageRealization_of_encoded s binaryModulusStage (modulusStage s h)
    (polynomialAddressCode _ _) (DecisionScalar.binaryCode (fun x ↦ encNat x.val))
    (binaryModulusInitial_correct s h)
  · intro cfg
    exact binaryStackStep_correct (polynomialProgram (Input.decode s).field.polynomial)
      (polynomialAddressCode _ _) (DecisionScalar.binaryCode (fun x ↦ encNat x.val))
      (binaryModulusInstruction s) (binaryModulusAdd s) (binaryModulusMul s)
      (binaryModulusInstruction_correct s hs) (binaryModulusAdd_correct s)
      (binaryModulusMul_correct s) cfg
  · exact binaryModulusAccept_correct s h

end SparseIrred.UpperBounds.Section4
