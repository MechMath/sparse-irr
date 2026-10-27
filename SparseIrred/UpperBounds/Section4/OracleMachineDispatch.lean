import SparseIrred.UpperBounds.Section4.OracleMachineTM

/-!
# An explicit coroutine dispatcher around an arbitrary oracle Turing machine

The dispatcher invokes the polynomial-time single-transition simulator proved
in `OracleMachineTM`. The oracle's full computation is never supplied as a
polynomial-time function. Controller callbacks are its local instruction,
query construction and return-register operations.
-/

noncomputable section
namespace SparseIrred.UpperBounds.Section4

open Complexity Complexity.Cobham

variable {k : ℕ}

/-- A query state stores the suspended controller encoding and the oracle configuration.
An outer state stores only the controller configuration. -/
def oracleDispatch (M : TM k) (plainStep hasQuery queryInput resume : List Bool → List Bool)
    (z : List Bool) : List Bool :=
  let payload := z.tail
  let saved := pairFst payload
  let current := pairSnd payload
  selectHead z
    (selectHead (oracleHalt M current)
      (false :: resume (pair saved (oracleOutput current)))
      (true :: pair saved (oracleStep M current)))
    (selectHead (hasQuery payload)
      (true :: pair payload (oracleInit M (queryInput payload)))
      (false :: plainStep payload))

/-- The whole dispatcher is derived from controller primitives and the genuine oracle TM. -/
theorem oracleDispatch_mem_FP (M : TM k)
    (plainStep hasQuery queryInput resume : List Bool → List Bool)
    (hplain : plainStep ∈ FP) (hquery : hasQuery ∈ FP) (hinput : queryInput ∈ FP)
    (hresume : resume ∈ FP) : oracleDispatch M plainStep hasQuery queryInput resume ∈ FP := by
  have hid : (fun z : List Bool ↦ z) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have ht : (fun z : List Bool ↦ z.tail) ∈ FP := CobhamFP_subset_FP (tailFn (Cobham.proj 0))
  have hf : (fun z : List Bool ↦ pairFst z.tail) ∈ FP := mem_FP_comp ht fstBlock_mem_FP
  have hs : (fun z : List Bool ↦ pairSnd z.tail) ∈ FP := mem_FP_comp ht sndBlock_mem_FP
  have hhalt := mem_FP_comp hs (oracleHalt_mem_FP M)
  have hout := mem_FP_comp hs oracleOutput_mem_FP
  have hcontinue := mem_FP_comp hs (oracleStep_mem_FP M)
  have hresult := mem_FP_comp (pairFn_mem_FP hf hout) hresume
  have hres := mem_FP_comp hresult (cons_mem_FP false)
  have hcall := mem_FP_comp (pairFn_mem_FP hf hcontinue) (cons_mem_FP true)
  have hinit := mem_FP_comp (mem_FP_comp ht hinput) (oracleInit_mem_FP M)
  have hstart := mem_FP_comp (pairFn_mem_FP ht hinit) (cons_mem_FP true)
  have hordinary := mem_FP_comp (mem_FP_comp ht hplain) (cons_mem_FP false)
  exact selectHeadFn_mem_FP hid (selectHeadFn_mem_FP hhalt hres hcall)
    (selectHeadFn_mem_FP (mem_FP_comp ht hquery) hstart hordinary)

@[simp] theorem oracleDispatch_outer_none (M : TM k)
    (plainStep hasQuery queryInput resume : List Bool → List Bool) (c : List Bool)
    (hc : hasQuery c = [false]) :
    oracleDispatch M plainStep hasQuery queryInput resume (false :: c) = false :: plainStep c := by
  simp [oracleDispatch, selectHead, hc]

@[simp] theorem oracleDispatch_outer_some (M : TM k)
    (plainStep hasQuery queryInput resume : List Bool → List Bool) (c : List Bool)
    (hc : hasQuery c = [true]) :
    oracleDispatch M plainStep hasQuery queryInput resume (false :: c) =
      true :: pair c (oracleInit M (queryInput c)) := by
  simp [oracleDispatch, selectHead, hc]

@[simp] theorem oracleDispatch_query_running (M : TM k)
    (plainStep hasQuery queryInput resume : List Bool → List Bool) (c z : List Bool)
    (hc : oracleHalt M z = [false]) :
    oracleDispatch M plainStep hasQuery queryInput resume (true :: pair c z) =
      true :: pair c (oracleStep M z) := by
  simp [oracleDispatch, selectHead, hc]

@[simp] theorem oracleDispatch_query_returned (M : TM k)
    (plainStep hasQuery queryInput resume : List Bool → List Bool) (c z : List Bool)
    (hc : oracleHalt M z = [true]) :
    oracleDispatch M plainStep hasQuery queryInput resume (true :: pair c z) =
      false :: resume (pair c (oracleOutput z)) := by
  simp [oracleDispatch, selectHead, hc]

end SparseIrred.UpperBounds.Section4
