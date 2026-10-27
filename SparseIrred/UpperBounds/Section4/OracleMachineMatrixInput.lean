import SparseIrred.UpperBounds.Section4.OracleMachineBerkowitzSpace
import SparseIrred.UpperBounds.Section4.BinaryField

/-!
# Uniform matrix metadata and spatial windows for Lemma 17

The matrix dimension and finite-field presentation are binary input data. A
validity hypothesis describes the input domain of the lemma; no validity test
is consulted by the arithmetic controller. Entry queries contain the original
input and two binary indices, never the controller's workspace ruler.
-/

noncomputable section
namespace SparseIrred.UpperBounds.Section4

open Complexity SparseDiv SparseDiv.StringArith

/-- Original matrix input: dimension, characteristic, dense modulus and opaque matrix description. -/
def oracleMatrixInput (n : ℕ) (c : FieldCode) (description : List Bool) : List Bool :=
  pair (encNat n) (pair (encNat c.characteristic) (pair (encodeNumerals c.modulus) description))

def oracleMatrixDimension (x : List Bool) : ℕ := decNat (pairFst x)

def oracleMatrixField (x : List Bool) : FieldCode :=
  ⟨decNat (pairFst (pairSnd x)), decodeNumerals (pairFst (pairSnd (pairSnd x)))⟩

def oracleMatrixDescription (x : List Bool) : List Bool := pairSnd (pairSnd (pairSnd x))

/-- Exactly the valid finite-field input domain assumed in Lemma 17. -/
def OracleMatrixInputValid (x : List Bool) : Prop :=
  (oracleMatrixField x).Valid ∧
    oracleMatrixInput (oracleMatrixDimension x) (oracleMatrixField x) (oracleMatrixDescription x) = x

@[simp] theorem oracleMatrixDimension_input (n : ℕ) (c : FieldCode) (description : List Bool) :
    oracleMatrixDimension (oracleMatrixInput n c description) = n := by
  simp [oracleMatrixDimension, oracleMatrixInput]

@[simp] theorem oracleMatrixField_input (n : ℕ) (c : FieldCode) (description : List Bool) :
    oracleMatrixField (oracleMatrixInput n c description) = c := by
  cases c
  simp [oracleMatrixField, oracleMatrixInput, decodeNumerals_encode]

@[simp] theorem oracleMatrixDescription_input (n : ℕ) (c : FieldCode) (description : List Bool) :
    oracleMatrixDescription (oracleMatrixInput n c description) = description := by
  simp [oracleMatrixDescription, oracleMatrixInput]

theorem oracleMatrixInput_valid (n : ℕ) (c : FieldCode) (hc : c.Valid) (description : List Bool) :
    OracleMatrixInputValid (oracleMatrixInput n c description) := by
  simp only [OracleMatrixInputValid, oracleMatrixDimension_input, oracleMatrixField_input,
    oracleMatrixDescription_input, and_true]
  exact hc

theorem oracleMatrixInput_dimension_size (n : ℕ) (c : FieldCode) (description : List Bool) :
    n.size ≤ (oracleMatrixInput n c description).length := by
  simp only [oracleMatrixInput, pair_length, length_encNat]
  omega

theorem oracleMatrixInput_characteristic_size (n : ℕ) (c : FieldCode) (description : List Bool) :
    c.characteristic.size ≤ (oracleMatrixInput n c description).length := by
  simp only [oracleMatrixInput, pair_length, length_encNat]
  omega

theorem oracleMatrixInput_modulus_length (n : ℕ) (c : FieldCode) (description : List Bool) :
    c.modulus.length ≤ (oracleMatrixInput n c description).length := by
  have h := length_le_encodeNumerals_length c.modulus
  simp only [oracleMatrixInput, pair_length]
  omega

theorem oracleMatrixInput_scalar_size (n : ℕ) (c : FieldCode) [Fact c.Valid]
    (description : List Bool) (v : c.Carrier) :
    (c.scalarCode v).length ≤ 2 * (oracleMatrixInput n c description).length ^ 2 +
      2 * (oracleMatrixInput n c description).length := by
  have h := c.canonical_element_length_le _ (c.encodeElement_canonical v)
  have hp := oracleMatrixInput_characteristic_size n c description
  have hm := oracleMatrixInput_modulus_length n c description
  have hd := c.degree_lt_modulus_length
  change (encodeNumerals (c.encodeElement v)).length ≤ _
  have hmul := Nat.mul_le_mul (show 2 * c.characteristic.size + 2 ≤
      2 * (oracleMatrixInput n c description).length + 2 by omega)
    (show c.degree ≤ (oracleMatrixInput n c description).length by omega)
  nlinarith

/-- The oracle reads the original matrix metadata and two indices only. -/
def oracleMatrixQuery (x : List Bool) (i j : ℕ) : List Bool :=
  pair x (pair (encNat i) (encNat j))

theorem oracleMatrixQuery_length (x : List Bool) (n : ℕ) (hn : n.size ≤ x.length)
    (i j : Fin n) : (oracleMatrixQuery x i.val j.val).length ≤ 5 * x.length + 4 := by
  have hi := (Nat.size_le_size (Nat.le_of_lt i.isLt)).trans hn
  have hj := (Nat.size_le_size (Nat.le_of_lt j.isLt)).trans hn
  simp only [oracleMatrixQuery, pair_length, length_encNat]
  omega

/-- The internal simulation window covers input, oracle space, scalar output and finite state. -/
def matrixOracleWindow {k : ℕ} (M : TM k) (space : Polynomial ℕ) : Polynomial ℕ :=
  space + Polynomial.C 2 * Polynomial.X ^ 2 + Polynomial.C 7 * Polynomial.X +
    Polynomial.C (Fintype.card M.Q + 10)

theorem matrixOracleWindow_eval {k : ℕ} (M : TM k) (space : Polynomial ℕ) (L : ℕ) :
    (matrixOracleWindow M space).eval L = space.eval L + 2 * L ^ 2 + 7 * L +
      Fintype.card M.Q + 10 := by
  simp [matrixOracleWindow]
  ring

theorem matrixOracleWindow_space {k : ℕ} (M : TM k) (space : Polynomial ℕ) (x : List Bool)
    (n : ℕ) (hn : n.size ≤ x.length) (i j : Fin n) :
    (oracleMatrixQuery x i.val j.val).length + space.eval x.length + 1 ≤
      (matrixOracleWindow M space).eval x.length := by
  have h := oracleMatrixQuery_length x n hn i j
  rw [matrixOracleWindow_eval]
  omega

theorem matrixOracleWindow_states {k : ℕ} (M : TM k) (space : Polynomial ℕ) (L : ℕ) :
    Fintype.card M.Q ≤ Cobham.blockWidth ((matrixOracleWindow M space).eval L) := by
  rw [matrixOracleWindow_eval, Cobham.blockWidth]
  omega

theorem matrixOracleWindow_output {k : ℕ} (M : TM k) (space : Polynomial ℕ) (L len : ℕ)
    (hl : len ≤ 2 * L ^ 2 + 2 * L) : len + 1 ≤ (matrixOracleWindow M space).eval L := by
  rw [matrixOracleWindow_eval]
  omega

theorem OracleMatrixInputValid.dimension_size {x : List Bool} (hx : OracleMatrixInputValid x) :
    (oracleMatrixDimension x).size ≤ x.length := by
  have h := oracleMatrixInput_dimension_size (oracleMatrixDimension x) (oracleMatrixField x)
    (oracleMatrixDescription x)
  rw [hx.2] at h
  exact h

theorem OracleMatrixInputValid.scalar_size {x : List Bool} (hx : OracleMatrixInputValid x)
    [Fact (oracleMatrixField x).Valid] (v : (oracleMatrixField x).Carrier) :
    ((oracleMatrixField x).scalarCode v).length ≤ 2 * x.length ^ 2 + 2 * x.length := by
  have h := oracleMatrixInput_scalar_size (oracleMatrixDimension x) (oracleMatrixField x)
    (oracleMatrixDescription x) v
  rw [hx.2] at h
  exact h

end SparseIrred.UpperBounds.Section4
