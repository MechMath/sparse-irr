import SparseIrred.UpperBounds.Section4.OracleMachineBound
import SparseIrred.UpperBounds.Machine.StreamingMachine

/-! # A concrete FP driver for controller/oracle co-execution -/

noncomputable section
namespace SparseIrred.UpperBounds.Section4

open Complexity Complexity.Cobham

/-- Initialization and completed-output handling are ordinary controller primitives. -/
structure OracleLoopOps extends OracleControllerOps where
  initializeState : List Bool → List Bool
  completed : List Bool → List Bool
  verdict : List Bool → List Bool
  initializeState_FP : initializeState ∈ FP
  completed_FP : completed ∈ FP
  verdict_FP : verdict ∈ FP

/-- A query cannot be a completed controller computation. -/
def oracleCoroutineDone (F : OracleLoopOps) (z : List Bool) : List Bool :=
  selectHead z [false] (F.completed z.tail)

/-- The driver uses `01` for initialization, `00` for running and `1b` for a completed verdict. -/
def oracleLoop {k : ℕ} (M : TM k) (F : OracleLoopOps) (z : List Bool) : List Bool :=
  selectHead z z.tail
    (selectHead z.tail
      ([false, false, false] ++ F.initializeState (pairSnd z))
      (selectHead (oracleCoroutineDone F (z.drop 2))
        (true :: F.verdict (z.drop 3))
        ([false, false] ++ oracleDispatch M F.plainStep F.hasQuery F.queryInput F.resume
          (z.drop 2))))

theorem oracleCoroutineDone_mem_FP (F : OracleLoopOps) : oracleCoroutineDone F ∈ FP := by
  have hid : (fun z : List Bool ↦ z) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have ht : (fun z : List Bool ↦ z.tail) ∈ FP := CobhamFP_subset_FP (tailFn (Cobham.proj 0))
  exact selectHeadFn_mem_FP hid (constFn_mem_FP [false]) (mem_FP_comp ht F.completed_FP)

theorem oracleLoop_mem_FP {k : ℕ} (M : TM k) (F : OracleLoopOps) : oracleLoop M F ∈ FP := by
  have hid : (fun z : List Bool ↦ z) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have ht : (fun z : List Bool ↦ z.tail) ∈ FP := CobhamFP_subset_FP (tailFn (Cobham.proj 0))
  have h2 : (fun z : List Bool ↦ z.drop 2) ∈ FP :=
    CobhamFP_subset_FP (dropFn (Cobham.const [false, false]) (Cobham.proj 0))
  have h3 : (fun z : List Bool ↦ z.drop 3) ∈ FP :=
    CobhamFP_subset_FP (dropFn (Cobham.const [false, false, false]) (Cobham.proj 0))
  have hinit := appendFn_mem_FP (constFn_mem_FP [false, false, false])
    (mem_FP_comp sndBlock_mem_FP F.initializeState_FP)
  have hdone := mem_FP_comp h2 (oracleCoroutineDone_mem_FP F)
  have houtput := mem_FP_comp (mem_FP_comp h3 F.verdict_FP) (cons_mem_FP true)
  have hnext := appendFn_mem_FP (constFn_mem_FP [false, false])
    (mem_FP_comp h2 (oracleDispatch_mem_FP M _ _ _ _ F.plainStep_FP F.hasQuery_FP
      F.queryInput_FP F.resume_FP))
  exact selectHeadFn_mem_FP hid ht (selectHeadFn_mem_FP ht hinit
    (selectHeadFn_mem_FP hdone houtput hnext))

@[simp] theorem oracleLoop_setup {k : ℕ} (M : TM k) (F : OracleLoopOps) (x : List Bool) :
    oracleLoop M F (pair [] x) = [false, false, false] ++ F.initializeState x := by
  have hx : pairSnd (false :: true :: x) = x := pairSnd_pair [] x
  simp [oracleLoop, pair, selectHead, hx]

@[simp] theorem oracleLoop_running {k : ℕ} (M : TM k) (F : OracleLoopOps) (z : List Bool)
    (hz : oracleCoroutineDone F z = [false]) :
    oracleLoop M F ([false, false] ++ z) =
      [false, false] ++ oracleDispatch M F.plainStep F.hasQuery F.queryInput F.resume z := by
  simp [oracleLoop, selectHead, hz]

@[simp] theorem oracleLoop_finished {k : ℕ} (M : TM k) (F : OracleLoopOps) (c : List Bool)
    (hc : F.completed c = [true]) :
    oracleLoop M F ([false, false, false] ++ c) = true :: F.verdict c := by
  simp [oracleLoop, oracleCoroutineDone, selectHead, hc]

@[simp] theorem oracleLoop_publish {k : ℕ} (M : TM k) (F : OracleLoopOps) (b : Bool) :
    oracleLoop M F [true, b] = [b] := rfl

end SparseIrred.UpperBounds.Section4
