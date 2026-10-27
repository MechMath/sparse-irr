import SparseIrred.UpperBounds.Section4.OracleMachineMatrixInput
import SparseIrred.UpperBounds.Section4.BinaryBerkowitzController
import SparseIrred.UpperBounds.Section4.OracleMachineDomainCompiler

/-! # An arbitrary-space entry TM supplies the only oracle input to Lemma 17 -/

noncomputable section
namespace SparseIrred.UpperBounds.Section4

open Complexity Matrix SparseDiv SparseDiv.StringArith
set_option backward.isDefEq.respectTransparency false

abbrev OracleMatrixFamily := ∀ x : List Bool,
  Matrix (Fin (oracleMatrixDimension x)) (Fin (oracleMatrixDimension x)) (oracleMatrixField x).Carrier

def oracleMatrixScalarCode (x : List Bool) (hx : OracleMatrixInputValid x)
    (v : (oracleMatrixField x).Carrier) : List Bool := by
  letI : Fact (oracleMatrixField x).Valid := ⟨hx.1⟩
  exact (oracleMatrixField x).scalarCode v

/-- The original hypothesis of Lemma 17: a real machine computes each entry and
its reachable configurations respect a polynomial spatial budget. -/
structure MatrixEntryMachine {k : ℕ} (M : TM k) (A : OracleMatrixFamily)
    (space : Polynomial ℕ) : Prop where
  bounded : ∀ x (hx : OracleMatrixInputValid x)
    (i j : Fin (oracleMatrixDimension x)) c,
    M.reaches (M.initCfg (oracleMatrixQuery x i.val j.val)) c →
      c.WithinDecisionSpace (oracleMatrixQuery x i.val j.val).length (space.eval x.length)
  computes : ∀ x (hx : OracleMatrixInputValid x) (i j : Fin (oracleMatrixDimension x)),
    ∃ c, M.reaches (M.initCfg (oracleMatrixQuery x i.val j.val)) c ∧ M.halted c ∧
      c.output.HasOutput (oracleMatrixScalarCode x hx (A x i j))

variable {k : ℕ} {M : TM k} {A : OracleMatrixFamily} {space : Polynomial ℕ}

def MatrixEntryMachine.source (E : MatrixEntryMachine M A space)
    (x : List Bool) (hx : OracleMatrixInputValid x) :
    EntryMachineSource M (fun ij : Fin (oracleMatrixDimension x) × Fin (oracleMatrixDimension x) ↦
      A x ij.1 ij.2) := by
  letI : Fact (oracleMatrixField x).Valid := ⟨hx.1⟩
  refine
    { query := fun ij ↦ oracleMatrixQuery x ij.1.val ij.2.val
      encode := (oracleMatrixField x).scalarCode
      decode := fun z ↦ (oracleMatrixField x).element (decodeNumerals z)
      roundtrip := ?_
      space := fun _ ↦ space.eval x.length
      window := fun _ ↦ (matrixOracleWindow M space).eval x.length
      window_space := fun ij ↦ matrixOracleWindow_space M space x _ hx.dimension_size ij.1 ij.2
      window_states := fun _ ↦ matrixOracleWindow_states M space x.length
      window_output := ?_
      bounded := fun ij ↦ E.bounded x hx ij.1 ij.2
      computes := fun ij ↦ E.computes x hx ij.1 ij.2 }
  · intro v
    simp only [FieldCode.scalarCode, decodeNumerals_encode,
      FieldCode.element_encodeElement]
  · intro ij
    exact matrixOracleWindow_output M space x.length _ (hx.scalar_size (A x ij.1 ij.2))

/-- The controller has the mathematical matrix only in its proved semantics;
its executable instruction decoder queries the real entry machine instead. -/
def MatrixEntryMachine.programInput (E : MatrixEntryMachine M A space)
    (x : List Bool) (hx : OracleMatrixInputValid x) : OracleProgramInput M := by
  letI : Fact (oracleMatrixField x).Valid := ⟨hx.1⟩
  exact
    { Addr := BerkowitzAddress (oracleMatrixDimension x)
      Scalar := (oracleMatrixField x).Carrier
      Query := Fin (oracleMatrixDimension x) × Fin (oracleMatrixDimension x)
      add := inferInstance
      mul := inferInstance
      program := berkowitzProgram (A x)
      request := berkowitzEntryRequest
      answer := fun ij ↦ A x ij.1 ij.2
      source := E.source x hx
      initial := .initial
      output := fun _ ↦ false
      code := concreteControllerCode (oracleMatrixField x) (oracleMatrixDescription x)
        ((matrixOracleWindow M space).eval x.length)
      request_correct := berkowitzEntryRequest_instruction (A x) }

/-- All four controller operations are actual proved FP functions; no such property is assumed. -/
theorem MatrixEntryMachine.controller_laws (E : MatrixEntryMachine M A space)
    (x : List Bool) (hx : OracleMatrixInputValid x) :
    OracleControllerLaws binaryBerkowitzController (E.programInput x hx).program
      (E.programInput x hx).request (E.programInput x hx).source (E.programInput x hx).code := by
  letI : Fact (oracleMatrixField x).Valid := ⟨hx.1⟩
  apply binaryBerkowitzController_laws
  · intro ij
    change oracleMatrixQuery x ij.1.val ij.2.val = _
    rw [concreteControllerParams, controllerQueryParams_pack]
    change pair x _ = pair
      (oracleMatrixInput (oracleMatrixDimension x) (oracleMatrixField x) (oracleMatrixDescription x)) _
    rw [hx.2]
  · intro ij; rfl
  · intro z; rfl

def determinantControllerBound (W : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C 1000000 * (Polynomial.C 2 * Polynomial.X + W + Polynomial.C 6) ^ 8

def determinantValueBound : Polynomial ℕ :=
  Polynomial.C 2 * Polynomial.X ^ 2 + Polynomial.C 2 * Polynomial.X

def determinantDepthBound : Polynomial ℕ := Polynomial.C 100 * (Polynomial.X + Polynomial.C 3) ^ 4

theorem MatrixEntryMachine.controller_space (E : MatrixEntryMachine M A space)
    (x : List Bool) (hx : OracleMatrixInputValid x) (t : ℕ) :
    ((E.programInput x hx).code ((E.programInput x hx).program.step^[t]
      (.eval (E.programInput x hx).initial []))).length ≤
        (determinantControllerBound (matrixOracleWindow M space)).eval x.length := by
  letI : Fact (oracleMatrixField x).Valid := ⟨hx.1⟩
  let W := (matrixOracleWindow M space).eval x.length
  let L := 2 * x.length + W + 3
  have hp : (concreteControllerParams (oracleMatrixDimension x) (oracleMatrixField x)
      (oracleMatrixDescription x) W).length ≤ L := by
    have h := concreteControllerParams_length (oracleMatrixDimension x) (oracleMatrixField x)
      (oracleMatrixDescription x) W
    change _ ≤ 2 * (oracleMatrixInput _ _ _).length + W + 3 at h
    rw [hx.2] at h
    exact h
  have hn : (oracleMatrixDimension x).size ≤ L := hx.dimension_size.trans (by dsimp [L]; omega)
  have hscalar : ∀ v : (oracleMatrixField x).Carrier,
      ((oracleMatrixField x).scalarCode v).length ≤ 2 * L ^ 2 + 2 * L := by
    intro v
    have h := hx.scalar_size v
    have hl : x.length ≤ L := by dsimp [L]; omega
    nlinarith
  have hb := berkowitzOracleControllerCode_length (A x)
    (concreteControllerParams (oracleMatrixDimension x) (oracleMatrixField x)
      (oracleMatrixDescription x) W) (oracleMatrixField x).scalarCode L hp hn hscalar t
  change (berkowitzOracleControllerCode
    (concreteControllerParams (oracleMatrixDimension x) (oracleMatrixField x)
      (oracleMatrixDescription x) W) (oracleMatrixField x).scalarCode
      ((berkowitzProgram (A x)).step^[t] (.eval .initial []))).length ≤ _
  apply hb.trans
  simp only [determinantControllerBound, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, L, W]
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  omega

theorem MatrixEntryMachine.value_space (E : MatrixEntryMachine M A space)
    (x : List Bool) (hx : OracleMatrixInputValid x) :
    ((E.programInput x hx).source.encode
      ((E.programInput x hx).program.value (E.programInput x hx).initial)).length ≤
      determinantValueBound.eval x.length := by
  letI : Fact (oracleMatrixField x).Valid := ⟨hx.1⟩
  change ((oracleMatrixField x).scalarCode _).length ≤ _
  simpa [determinantValueBound] using hx.scalar_size
    ((E.programInput x hx).program.value (E.programInput x hx).initial)

theorem MatrixEntryMachine.depth_bound (E : MatrixEntryMachine M A space)
    (x : List Bool) (hx : OracleMatrixInputValid x) :
    (E.programInput x hx).program.rank (E.programInput x hx).initial ≤
      determinantDepthBound.eval x.length := by
  letI : Fact (oracleMatrixField x).Valid := ⟨hx.1⟩
  change (berkowitzProgram (A x)).rank .initial ≤ _
  simpa only [determinantDepthBound, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X] using
    berkowitzProgram_rank_input (A x) x.length hx.dimension_size

theorem MatrixEntryMachine.output_eq_det (E : MatrixEntryMachine M A space)
    (x : List Bool) (hx : OracleMatrixInputValid x) :
    (E.programInput x hx).source.encode
      ((E.programInput x hx).program.value (E.programInput x hx).initial) =
      oracleMatrixScalarCode x hx (A x).det := by
  change oracleMatrixScalarCode x hx ((berkowitzProgram (A x)).value .initial) = _
  rw [berkowitzProgram_value]

end SparseIrred.UpperBounds.Section4
