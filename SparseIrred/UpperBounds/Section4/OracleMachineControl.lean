import SparseIrred.UpperBounds.Section4.OracleMachineSource

/-!
# Local controller laws imply correctness of the compiled oracle dispatcher

Only ordinary stack steps, query construction and insertion of a returned
scalar are supplied by the controller. The arbitrary-time oracle execution is
implemented internally by the encoded transition table of its actual TM.
-/

noncomputable section
namespace SparseIrred.UpperBounds.Section4

open Complexity Complexity.Cobham

/-- The ordinary controller operations. These do not run an oracle. -/
structure OracleControllerOps where
  plainStep : List Bool → List Bool
  hasQuery : List Bool → List Bool
  queryInput : List Bool → List Bool
  resume : List Bool → List Bool
  plainStep_FP : plainStep ∈ FP
  hasQuery_FP : hasQuery ∈ FP
  queryInput_FP : queryInput ∈ FP
  resume_FP : resume ∈ FP

variable {A R I : Type*} [Add R] [Mul R] {k : ℕ} {M : TM k}
    {answer : I → R}

/-- These equations describe a single local controller action on its binary representation. -/
structure OracleControllerLaws (F : OracleControllerOps) (P : EntryProgram A R)
    (request : A → Option I) (E : EntryMachineSource M answer)
    (code : EntryConfig A R → List Bool) : Prop where
  ordinary_eval : ∀ a stack, request a = none →
    F.plainStep (code (.eval a stack)) = code (P.step (.eval a stack))
  ordinary_ret : ∀ v stack, F.plainStep (code (.ret v stack)) = code (P.step (.ret v stack))
  request_none : ∀ a stack, request a = none → F.hasQuery (code (.eval a stack)) = [false]
  request_some : ∀ a stack i, request a = some i → F.hasQuery (code (.eval a stack)) = [true]
  request_ret : ∀ v stack, F.hasQuery (code (.ret v stack)) = [false]
  query : ∀ a stack i, request a = some i →
    F.queryInput (code (.eval a stack)) = pair (oracleRuler (E.window i)) (E.query i)
  returned : ∀ a stack z,
    F.resume (pair (code (.eval a stack)) z) = code (.ret (E.decode z) stack)

/-- The only query-phase code is the actual oracle configuration code. -/
def oracleCoroutineCode (code : EntryConfig A R → List Bool) :
    OracleCoroutineConfig A R (List Bool) → List Bool :=
  OracleCoroutineConfig.encode code id

/-- Every dispatcher transition matches the already verified mathematical coroutine. -/
theorem oracleDispatch_code (F : OracleControllerOps) (P : EntryProgram A R)
    (request : A → Option I) (E : EntryMachineSource M answer)
    (code : EntryConfig A R → List Bool) (H : OracleControllerLaws F P request E code)
    (c : OracleCoroutineConfig A R (List Bool)) :
    oracleDispatch M F.plainStep F.hasQuery F.queryInput F.resume (oracleCoroutineCode code c) =
      oracleCoroutineCode code (oracleCoroutineStep P request answer E.scalarOracle c) := by
  cases c with
  | outer c =>
    cases c with
    | eval a stack =>
      cases hr : request a with
      | none =>
        simp only [oracleCoroutineCode, OracleCoroutineConfig.encode,
          oracleDispatch_outer_none M _ _ _ _ _ (H.request_none a stack hr),
          H.ordinary_eval a stack hr, oracleCoroutineStep, hr]
      | some i =>
        simp only [oracleCoroutineCode, OracleCoroutineConfig.encode,
          oracleDispatch_outer_some M _ _ _ _ _ (H.request_some a stack i hr),
          H.query a stack i hr, oracleCoroutineStep, hr,
          EntryMachineSource.scalarOracle, id_eq, E.startCode_eq_init i]
    | ret v stack =>
      simp only [oracleCoroutineCode, OracleCoroutineConfig.encode,
        oracleDispatch_outer_none M _ _ _ _ _ (H.request_ret v stack),
        H.ordinary_ret v stack, oracleCoroutineStep]
  | query a stack z =>
    have hf : oracleHalt M z = [true] ∨ oracleHalt M z = [false] := eqFlag_flag _ _
    rcases hf with hh | hh
    · simp only [oracleCoroutineCode, OracleCoroutineConfig.encode, id_eq,
        oracleDispatch_query_returned M _ _ _ _ _ _ hh, H.returned,
        oracleCoroutineStep, EntryMachineSource.scalarOracle, EntryMachineSource.readCode,
        hh, List.headD_cons, ↓reduceIte]
    · simp only [oracleCoroutineCode, OracleCoroutineConfig.encode, id_eq,
        oracleDispatch_query_running M _ _ _ _ _ _ hh,
        oracleCoroutineStep, EntryMachineSource.scalarOracle, EntryMachineSource.readCode,
        hh, List.headD_cons, Bool.false_eq_true, ↓reduceIte]

theorem oracleDispatch_iterate_code (F : OracleControllerOps) (P : EntryProgram A R)
    (request : A → Option I) (E : EntryMachineSource M answer)
    (code : EntryConfig A R → List Bool) (H : OracleControllerLaws F P request E code)
    (c : OracleCoroutineConfig A R (List Bool)) (t : ℕ) :
    (oracleDispatch M F.plainStep F.hasQuery F.queryInput F.resume)^[t]
      (oracleCoroutineCode code c) = oracleCoroutineCode code
        ((oracleCoroutineStep P request answer E.scalarOracle)^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', ih, oracleDispatch_code F P request E code H,
      Function.iterate_succ_apply']

end SparseIrred.UpperBounds.Section4
