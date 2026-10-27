import SparseIrred.UpperBounds.Section4.PolynomialProgram
import SparseIrred.UpperBounds.Section4.Language
import SparseIrred.UpperBounds.Section4.StageMachine

/-!
# Uniform execution over all encoded finite fields

The scalar type changes only after a preceding computation has returned a true
flag. First syntax and trial division are checked; then the modulus is tested
over the now validated prime field; finally the sparse polynomial is tested over
the now validated extension. No input-validity proposition is used as an oracle.
-/

noncomputable section

namespace SparseIrred.UpperBounds.Section4

open Polynomial

set_option backward.isDefEq.respectTransparency false

def primeStage (s : List Bool) : StageSpec where
  Addr := PrimeAddress (Input.decode s).field.characteristic
  Scalar := DecisionScalar (ZMod 2)
  add := inferInstance
  mul := inferInstance
  program := primeDivisorProgram (Input.decode s).field.characteristic
  initial := primeDivisorInitial (Input.decode s).field.characteristic
  output := preflightOutput s

theorem primeStage_answer (s : List Bool) : (primeStage s).answer = preflightAnswer s := rfl

def primeFactOfStage (s : List Bool) (h : (primeStage s).answer = true) :
    Fact (Input.decode s).field.characteristic.Prime :=
  ⟨((preflightAnswer_correct s).mp h).2.2⟩

def modulusStage (s : List Bool) (h : (primeStage s).answer = true) : StageSpec := by
  letI := primeFactOfStage s h
  let f := (Input.decode s).field.polynomial
  exact
    { Addr := PolynomialAddress f.natDegree f.derivative.natDegree
      Scalar := DecisionScalar (ZMod (Input.decode s).field.characteristic)
      add := inferInstance
      mul := inferInstance
      program := polynomialProgram f
      initial := polynomialInitial _ _
      output := DecisionScalar.asBool }

theorem modulusStage_answer_correct (s : List Bool) (h : (primeStage s).answer = true) :
    (modulusStage s h).answer = true ↔ Irreducible (Input.decode s).field.polynomial := by
  letI := primeFactOfStage s h
  exact polynomialProgram_correct _

/-- This proof is obtained from two completed stage answers, rather than provided
as an input premise. It justifies installing the genuine extension-field instance. -/
def validFieldOfStages (s : List Bool) (h : (primeStage s).answer = true)
    (h' : (modulusStage s h).answer = true) : (Input.decode s).field.Valid := by
  have hs := ((preflightAnswer_correct s).mp h).2.1
  exact ⟨(primeFactOfStage s h).out, hs.monic, (modulusStage_answer_correct s h).mp h',
    hs.coefficients, hs.trailing⟩

def sparseStage (s : List Bool) (h : (primeStage s).answer = true)
    (h' : (modulusStage s h).answer = true) : StageSpec := by
  classical
  let x := Input.decode s
  letI : Fact x.field.Valid := ⟨validFieldOfStages s h h'⟩
  let f := x.field.sparsePolynomial x.terms
  exact
    { Addr := PolynomialAddress f.natDegree f.derivative.natDegree
      Scalar := DecisionScalar x.field.Carrier
      add := inferInstance
      mul := inferInstance
      program := polynomialProgram f
      initial := polynomialInitial _ _
      output := fun v ↦ decide (∀ t ∈ x.terms, x.field.CanonicalElement t.1) && v.asBool }

theorem sparseStage_answer_correct (s : List Bool) (h : (primeStage s).answer = true)
    (h' : (modulusStage s h).answer = true) :
    (sparseStage s h h').answer = true ↔
      (∀ t ∈ (Input.decode s).terms, (Input.decode s).field.CanonicalElement t.1) ∧
      Irreducible ((Input.decode s).field.sparsePolynomial (Input.decode s).terms) := by
  classical
  letI : Fact (Input.decode s).field.Valid := ⟨validFieldOfStages s h h'⟩
  change (decide (∀ t ∈ (Input.decode s).terms, (Input.decode s).field.CanonicalElement t.1) &&
    ((polynomialProgram ((Input.decode s).field.sparsePolynomial (Input.decode s).terms)).value
      (polynomialInitial _ _)).asBool) = true ↔ _
  rw [Bool.and_eq_true, decide_eq_true_eq, polynomialProgram_correct]

/-- All input checks and both polynomial tests share one uniform staged control machine. -/
def uniformStages (s : List Bool) : ThreeStages where
  first := primeStage s
  second := modulusStage s
  third := sparseStage s

theorem uniformStages_correct (s : List Bool) :
    (uniformStages s).answer = true ↔ s ∈ UniformIrredLang := by
  rw [mem_UniformIrredLang_iff]
  change (if h : (primeStage s).answer = true then
    if h' : (modulusStage s h).answer = true then (sparseStage s h h').answer else false
    else false) = true ↔ _
  split_ifs with h h'
  · rw [sparseStage_answer_correct]
    have hs := (preflightAnswer_correct s).mp h
    have hv := validFieldOfStages s h h'
    constructor
    · rintro ⟨hc, hi⟩
      exact ⟨hs.1, ⟨hv, hc⟩, hi⟩
    · rintro ⟨_, hv, hi⟩
      exact ⟨hv.coefficients, hi⟩
  · simp only [false_iff]
    rintro ⟨_, hv, _⟩
    exact h' ((modulusStage_answer_correct s h).mpr hv.field.irreducible)
  · simp only [false_iff]
    rintro ⟨he, hv, _⟩
    exact h ((preflightAnswer_correct s).mpr ⟨he, hv.field.structural, hv.field.prime⟩)

theorem uniformStages_answer_eq (s : List Bool) :
    (uniformStages s).answer = uniformDecision s := by
  apply Bool.eq_iff_iff.mpr
  rw [uniformStages_correct, uniformDecision_correct]

end SparseIrred.UpperBounds.Section4
