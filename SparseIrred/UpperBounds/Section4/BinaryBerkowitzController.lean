import SparseIrred.UpperBounds.Section4.BinaryAddressFrobenius
import SparseIrred.UpperBounds.Section4.BinaryField
import SparseIrred.UpperBounds.Section4.BinaryStack
import SparseIrred.UpperBounds.Section4.OracleMachineControl

/-!
# A concrete binary controller for the arbitrary-time determinant oracle

The saved state carries the dimension, finite-field presentation, original input,
and oracle window ruler. Every controller operation is an explicit Cobham function.
Only the original matrix-entry Turing machine remains a source parameter.
-/

namespace SparseIrred.UpperBounds.Section4

open Complexity SparseDiv SparseDiv.StringArith Matrix

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

def berkowitzControllerParams (dim prime modulus input ruler : List Bool) : List Bool :=
  pair dim (pair prime (pair modulus (pair input ruler)))

def controllerDimension (params : List Bool) : List Bool := pairFst params
def controllerPrime (params : List Bool) : List Bool := pairFst (pairSnd params)
def controllerModulus (params : List Bool) : List Bool := pairFst (pairSnd (pairSnd params))
def controllerRuler (params : List Bool) : List Bool := pairSnd (pairSnd (pairSnd (pairSnd params)))

/-- Query metadata omits the workspace ruler: the queried machine must not receive
its own unary window as part of the input it is required to fit inside that window. -/
def controllerQueryParams (params : List Bool) : List Bool :=
  pair (controllerDimension params) (pair (controllerPrime params)
    (pair (controllerModulus params) (pairFst (pairSnd (pairSnd (pairSnd params))))))

/-- Add a workspace ruler to the input metadata, without including that ruler in
the strings passed to the entry oracle. -/
def controllerParamsOf (input ruler : List Bool) : List Bool :=
  berkowitzControllerParams (pairFst input) (pairFst (pairSnd input))
    (pairFst (pairSnd (pairSnd input))) (pairSnd (pairSnd (pairSnd input))) ruler

@[simp] theorem controllerParamsOf_pair (dim prime modulus input ruler : List Bool) :
    controllerParamsOf (pair dim (pair prime (pair modulus input))) ruler =
      berkowitzControllerParams dim prime modulus input ruler := by
  simp [controllerParamsOf]

@[simp] theorem controllerQueryParams_pack (dim prime modulus input ruler : List Bool) :
    controllerQueryParams (berkowitzControllerParams dim prime modulus input ruler) =
      pair dim (pair prime (pair modulus input)) := by
  simp [controllerQueryParams, berkowitzControllerParams, controllerDimension,
    controllerPrime, controllerModulus]

@[simp] theorem controllerRuler_pack (dim prime modulus input ruler : List Bool) :
    controllerRuler (berkowitzControllerParams dim prime modulus input ruler) = ruler := by
  simp [controllerRuler, berkowitzControllerParams]

/-- The private unary window is workspace, not an enlargement of the original input. -/
theorem controllerParamsOf_pair_length (dim prime modulus input : List Bool) (window : ℕ) :
    (controllerParamsOf (pair dim (pair prime (pair modulus input))) (oracleRuler window)).length ≤
      2 * (pair dim (pair prime (pair modulus input))).length + window + 3 := by
  simp only [controllerParamsOf_pair, berkowitzControllerParams, pair_length,
    oracleRuler, List.length_replicate]
  omega

def controllerScalarNormalize (params scalar : List Bool) : List Bool :=
  fieldNormalizeStr (controllerPrime params) (controllerModulus params) (canonicalNumeralsStr scalar)

def controllerBerkowitzInstruction (params addr : List Bool) : List Bool :=
  let dim := controllerDimension params
  let p := controllerPrime params
  let h := controllerModulus params
  let z := fieldZeroStr h
  let o := fieldOneStr p h
  let neg := fieldNegStr p h o
  binaryBerkowitzInstruction (fun _ ↦ z) dim z o neg (binaryParitySign dim o neg) addr

def controllerPlainStep (state : List Bool) : List Bool :=
  let params := pairFst state
  pair params (binaryStackStep (controllerBerkowitzInstruction params)
    (fieldAddStr (controllerPrime params) (controllerModulus params))
    (fieldMulStr (controllerPrime params) (controllerModulus params)) (pairSnd state))

def controllerHasQuery (state : List Bool) : List Bool :=
  let cfg := pairSnd state
  binaryBit cfg [false]
    (binaryBit (binaryBerkowitzRequest (pairFst cfg.tail)) [true] [false])

def controllerQueryInput (state : List Bool) : List Bool :=
  let params := pairFst state
  let cfg := pairSnd state
  pair (controllerRuler params)
    (pair (controllerQueryParams params) (binaryBerkowitzRequest (pairFst cfg.tail)).tail)

def controllerResume (savedAndOutput : List Bool) : List Bool :=
  let saved := pairFst savedAndOutput
  let params := pairFst saved
  let stack := pairSnd (pairSnd saved).tail
  pair params (binaryReturn (controllerScalarNormalize params (pairSnd savedAndOutput)) stack)

theorem cobham_controllerDimension {n : ℕ} {p : (Fin n → List Bool) → List Bool} (hp : Cobham p) :
    Cobham fun v ↦ controllerDimension (p v) := cobham_pairFst_comp hp
theorem cobham_controllerPrime {n : ℕ} {p : (Fin n → List Bool) → List Bool} (hp : Cobham p) :
    Cobham fun v ↦ controllerPrime (p v) := cobham_pairFst_comp (cobham_pairSnd_comp hp)
theorem cobham_controllerModulus {n : ℕ} {p : (Fin n → List Bool) → List Bool} (hp : Cobham p) :
    Cobham fun v ↦ controllerModulus (p v) :=
  cobham_pairFst_comp (cobham_pairSnd_comp (cobham_pairSnd_comp hp))
theorem cobham_controllerRuler {n : ℕ} {p : (Fin n → List Bool) → List Bool} (hp : Cobham p) :
    Cobham fun v ↦ controllerRuler (p v) :=
  cobham_pairSnd_comp (cobham_pairSnd_comp (cobham_pairSnd_comp (cobham_pairSnd_comp hp)))
theorem cobham_controllerQueryParams {n : ℕ} {p : (Fin n → List Bool) → List Bool} (hp : Cobham p) :
    Cobham fun v ↦ controllerQueryParams (p v) :=
  cobham_pair_comp (cobham_controllerDimension hp) (cobham_pair_comp (cobham_controllerPrime hp)
    (cobham_pair_comp (cobham_controllerModulus hp)
      (cobham_pairFst_comp (cobham_pairSnd_comp (cobham_pairSnd_comp (cobham_pairSnd_comp hp))))))

theorem cobham_controllerParamsOf {n : ℕ} {i r : (Fin n → List Bool) → List Bool}
    (hi : Cobham i) (hr : Cobham r) : Cobham fun v ↦ controllerParamsOf (i v) (r v) :=
  cobham_pair_comp (cobham_pairFst_comp hi)
    (cobham_pair_comp (cobham_pairFst_comp (cobham_pairSnd_comp hi))
      (cobham_pair_comp (cobham_pairFst_comp (cobham_pairSnd_comp (cobham_pairSnd_comp hi)))
        (cobham_pair_comp (cobham_pairSnd_comp (cobham_pairSnd_comp (cobham_pairSnd_comp hi))) hr)))

theorem cobham_controllerScalarNormalize {n : ℕ} {p s : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (hs : Cobham s) : Cobham fun v ↦ controllerScalarNormalize (p v) (s v) :=
  cobham_fieldNormalizeStr_comp (cobham_controllerPrime hp) (cobham_controllerModulus hp)
    (cobham_canonicalNumeralsStr hs)

theorem cobham_controllerBerkowitzInstruction {n : ℕ} {p a : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (ha : Cobham a) : Cobham fun v ↦ controllerBerkowitzInstruction (p v) (a v) := by
  have hd := cobham_controllerDimension hp
  have hprime := cobham_controllerPrime hp
  have hmod := cobham_controllerModulus hp
  have hz := cobham_fieldZeroStr_comp hmod
  have ho := cobham_fieldOneStr_comp hprime hmod
  have hn := cobham_fieldNegStr_comp hprime hmod ho
  exact cobham_binaryBerkowitzInstruction (n := n) (entry := fun v _ ↦ fieldZeroStr (controllerModulus (p v)))
    (fun _ _ ↦ hz) hd hz ho hn (cobham_binaryParitySign hd ho hn) ha

theorem controllerPlainStep_mem_FP : controllerPlainStep ∈ FP := by
  apply CobhamFP_subset_FP
  have hp := cobham_pairFst_comp (Cobham.proj (n := 1) 0)
  apply cobham_pair_comp hp
  apply cobham_binaryStackStep (n := 1)
    (instruction := fun v ↦ controllerBerkowitzInstruction (pairFst (v 0)))
    (add := fun v ↦ fieldAddStr (controllerPrime (pairFst (v 0))) (controllerModulus (pairFst (v 0))))
    (mul := fun v ↦ fieldMulStr (controllerPrime (pairFst (v 0))) (controllerModulus (pairFst (v 0))))
  · exact cobham_controllerBerkowitzInstruction (cobham_pairFst_comp (.proj 1)) (.proj 0)
  · exact cobham_fieldAddStr_comp (cobham_controllerPrime (cobham_pairFst_comp (.proj 2)))
      (cobham_controllerModulus (cobham_pairFst_comp (.proj 2))) (.proj 0) (.proj 1)
  · exact cobham_fieldMulStr_comp (cobham_controllerPrime (cobham_pairFst_comp (.proj 2)))
      (cobham_controllerModulus (cobham_pairFst_comp (.proj 2))) (.proj 0) (.proj 1)
  · exact cobham_pairSnd_comp (.proj 0)

theorem controllerHasQuery_mem_FP : controllerHasQuery ∈ FP := by
  apply CobhamFP_subset_FP
  have hc := cobham_pairSnd_comp (Cobham.proj (n := 1) 0)
  exact cobham_binaryBit hc (.const [false])
    (cobham_binaryBit (cobham_binaryBerkowitzRequest (cobham_pairFst_comp (cobham_binaryTail hc)))
      (.const [true]) (.const [false]))

theorem controllerQueryInput_mem_FP : controllerQueryInput ∈ FP := by
  apply CobhamFP_subset_FP
  have hp := cobham_pairFst_comp (Cobham.proj (n := 1) 0)
  have hc := cobham_pairSnd_comp (Cobham.proj (n := 1) 0)
  exact cobham_pair_comp (cobham_controllerRuler hp)
    (cobham_pair_comp (cobham_controllerQueryParams hp) (cobham_binaryTail
      (cobham_binaryBerkowitzRequest (cobham_pairFst_comp (cobham_binaryTail hc)))))

theorem controllerResume_mem_FP : controllerResume ∈ FP := by
  apply CobhamFP_subset_FP
  have hs := cobham_pairFst_comp (Cobham.proj (n := 1) 0)
  have hp := cobham_pairFst_comp hs
  exact cobham_pair_comp hp (cobham_binaryReturn
    (cobham_controllerScalarNormalize hp (cobham_pairSnd_comp (.proj 0)))
    (cobham_pairSnd_comp (cobham_binaryTail (cobham_pairSnd_comp hs))))

/-- A fixed controller independent of matrix dimension, characteristic, extension degree and input. -/
def binaryBerkowitzController : OracleControllerOps where
  plainStep := controllerPlainStep
  hasQuery := controllerHasQuery
  queryInput := controllerQueryInput
  resume := controllerResume
  plainStep_FP := controllerPlainStep_mem_FP
  hasQuery_FP := controllerHasQuery_mem_FP
  queryInput_FP := controllerQueryInput_mem_FP
  resume_FP := controllerResume_mem_FP

noncomputable section

def encodedFieldScalar (c : FieldCode) [Fact c.Valid] (a : c.Carrier) : List Bool :=
  encodeNumerals (c.encodeElement a)

def concreteControllerParams (n : ℕ) (c : FieldCode) (input : List Bool) (window : ℕ) : List Bool :=
  berkowitzControllerParams (encNat n) (encNat c.characteristic) (encodeNumerals c.modulus)
    input (oracleRuler window)

theorem concreteControllerParams_length (n : ℕ) (c : FieldCode) (input : List Bool) (window : ℕ) :
    (concreteControllerParams n c input window).length ≤
      2 * (pair (encNat n) (pair (encNat c.characteristic) (pair (encodeNumerals c.modulus) input))).length +
        window + 3 := by
  simpa only [controllerParamsOf_pair, concreteControllerParams] using
    controllerParamsOf_pair_length (encNat n) (encNat c.characteristic)
      (encodeNumerals c.modulus) input window

def concreteControllerCode {n : ℕ} (c : FieldCode) [Fact c.Valid]
    (input : List Bool) (window : ℕ)
    (config : EntryConfig (BerkowitzAddress n) c.Carrier) : List Bool :=
  pair (concreteControllerParams n c input window)
    (config.framedEncode BerkowitzAddress.binaryCode (encodedFieldScalar c))

theorem controllerBerkowitzInstruction_correct (n : ℕ) (c : FieldCode) [Fact c.Valid]
    (input : List Bool) (window : ℕ) (a : BerkowitzAddress n) :
    controllerBerkowitzInstruction (concreteControllerParams n c input window) a.binaryCode =
      ((berkowitzProgram (0 : Matrix (Fin n) (Fin n) c.Carrier)).instruction a).binaryCode
        BerkowitzAddress.binaryCode (encodedFieldScalar c) := by
  simp only [controllerBerkowitzInstruction, concreteControllerParams, berkowitzControllerParams,
    controllerDimension, controllerPrime, controllerModulus, pairFst_pair, pairSnd_pair,
    fieldZeroStr_encoded, fieldOneStr_encoded, fieldNegStr_encoded]
  rw [binaryParitySign_eq (fun a : c.Carrier ↦ encodeNumerals (c.encodeElement a)) n]
  exact binaryBerkowitzInstruction_eq 0 (encodedFieldScalar c) _ (fun _ _ ↦ rfl) a

theorem controllerScalarNormalize_correct (n : ℕ) (c : FieldCode) [Fact c.Valid]
    (input : List Bool) (window : ℕ) (s : List Bool) :
    controllerScalarNormalize (concreteControllerParams n c input window) s =
      encodedFieldScalar c (c.element (decodeNumerals s)) := by
  have hcan : canonicalNumeralsStr s = encodeNumerals (decodeNumerals s) := by
    simp [canonicalNumeralsStr_eq, encodeNumerals, decodeNumerals, List.map_map, Function.comp_def]
  simp only [controllerScalarNormalize, concreteControllerParams, berkowitzControllerParams,
    controllerPrime, controllerModulus, pairFst_pair, pairSnd_pair, hcan]
  exact fieldNormalizeStr_encoded c _

theorem binaryBerkowitzController_laws {n k : ℕ} (c : FieldCode) [Fact c.Valid]
    (A : Matrix (Fin n) (Fin n) c.Carrier) (input : List Bool) (window : ℕ)
    (M : TM k) (E : EntryMachineSource M (fun ij : Fin n × Fin n ↦ A ij.1 ij.2))
    (hquery : ∀ ij, E.query ij = pair (controllerQueryParams (concreteControllerParams n c input window))
      (pair (encNat ij.1.val) (encNat ij.2.val)))
    (hwindow : ∀ ij, E.window ij = window)
    (hdecode : ∀ s, E.decode s = c.element (decodeNumerals s)) :
    OracleControllerLaws binaryBerkowitzController (berkowitzProgram A) berkowitzEntryRequest E
      (concreteControllerCode c input window) := by
  let er := encodedFieldScalar c
  let params := concreteControllerParams n c input window
  have hadd : ∀ a b : c.Carrier,
      fieldAddStr (controllerPrime params) (controllerModulus params) (er a) (er b) = er (a + b) := by
    intro a b
    simpa only [params, er, encodedFieldScalar, concreteControllerParams, berkowitzControllerParams,
      controllerPrime, controllerModulus, pairFst_pair, pairSnd_pair] using fieldAddStr_encoded c a b
  have hmul : ∀ a b : c.Carrier,
      fieldMulStr (controllerPrime params) (controllerModulus params) (er a) (er b) = er (a * b) := by
    intro a b
    simpa only [params, er, encodedFieldScalar, concreteControllerParams, berkowitzControllerParams,
      controllerPrime, controllerModulus, pairFst_pair, pairSnd_pair] using fieldMulStr_encoded c a b
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a stack hnone
    simp only [binaryBerkowitzController, controllerPlainStep, concreteControllerCode,
      pairFst_pair, pairSnd_pair]
    congr 1
    rw [binaryStackStep, EntryConfig.framedEncode]
    simp only [List.tail_cons, pairFst_pair, pairSnd_pair, caseBit₀]
    rw [controllerBerkowitzInstruction_correct, berkowitzEntryRequest_none_instruction 0 A a hnone]
    exact binaryExecute_correct _ _ ((berkowitzProgram A).instruction a) stack
  · intro v stack
    simp only [binaryBerkowitzController, controllerPlainStep, concreteControllerCode,
      pairFst_pair, pairSnd_pair]
    congr 1
    rw [binaryStackStep_correct (berkowitzProgram (0 : Matrix (Fin n) (Fin n) c.Carrier))
      BerkowitzAddress.binaryCode er _ _ _
      (controllerBerkowitzInstruction_correct n c input window) hadd hmul]
    cases stack with
    | nil => rfl
    | cons f stack => cases f <;> rfl
  · intro a stack hnone
    simp [binaryBerkowitzController, controllerHasQuery, concreteControllerCode,
      EntryConfig.framedEncode, binaryBit, binaryBerkowitzRequest_eq, hnone, encodeEntryRequest]
  · intro a stack ij hsome
    simp [binaryBerkowitzController, controllerHasQuery, concreteControllerCode,
      EntryConfig.framedEncode, binaryBit, binaryBerkowitzRequest_eq, hsome, encodeEntryRequest,
      binarySomeEntry]
  · intro v stack
    simp [binaryBerkowitzController, controllerHasQuery, concreteControllerCode,
      EntryConfig.framedEncode, binaryBit]
  · intro a stack ij hsome
    simp [binaryBerkowitzController, controllerQueryInput, concreteControllerCode,
      EntryConfig.framedEncode, binaryBerkowitzRequest_eq, hsome, encodeEntryRequest,
      binarySomeEntry, hquery, hwindow, concreteControllerParams, berkowitzControllerParams,
      controllerRuler]
  · intro a stack s
    simp only [binaryBerkowitzController, controllerResume, concreteControllerCode,
      pairFst_pair, pairSnd_pair, EntryConfig.framedEncode, List.tail_cons,
      controllerScalarNormalize_correct, hdecode, binaryReturn]

end

end SparseIrred.UpperBounds.Section4
