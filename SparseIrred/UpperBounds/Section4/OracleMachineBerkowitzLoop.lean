import SparseIrred.UpperBounds.Section4.BinaryBerkowitzController
import SparseIrred.UpperBounds.Section4.OracleMachineDomainCompiler
import SparseIrred.UpperBounds.Section4.OracleMachineMatrixInput

/-!
# Concrete endpoints of the Berkowitz oracle loop

Initialization adds a polynomial-size private workspace ruler. Completion reads
the return tag and empty continuation, and publication extracts the entire
encoded scalar. All three are proved polynomial-time binary functions.
-/

namespace SparseIrred.UpperBounds.Section4

open Complexity SparseDiv SparseDiv.StringArith

def binaryBerkowitzInitialize (W : Polynomial ℕ) (x : List Bool) : List Bool :=
  pair (controllerParamsOf x (oracleRuler (W.eval x.length)))
    (binaryEval [false, false] [false])

def binaryBerkowitzCompleted (state : List Bool) : List Bool :=
  binaryBit (pairSnd state)
    (Cobham.eqFlag (pairSnd (pairSnd state).tail) [false]) [false]

def binaryBerkowitzVerdict (state : List Bool) : List Bool :=
  pairFst (pairSnd state).tail

theorem binaryBerkowitzInitialize_mem_FP (W : Polynomial ℕ) : binaryBerkowitzInitialize W ∈ FP := by
  apply CobhamFP_subset_FP
  have hR : Cobham fun u : Fin 1 → List Bool ↦ oracleRuler (W.eval (u 0).length) := by
    refine (cobham_cons false (Cobham.zeroBlockFn (Cobham.polyLen_mem W (.proj 0)))).of_eq ?_
    intro u
    simp only [Cobham.polyLen_length, oracleRuler, List.replicate_succ]
  exact cobham_pair_comp (cobham_controllerParamsOf (.proj 0) hR) (.const _)

theorem binaryBerkowitzCompleted_mem_FP : binaryBerkowitzCompleted ∈ FP := by
  apply CobhamFP_subset_FP
  have hc := cobham_pairSnd_comp (Cobham.proj (n := 1) 0)
  exact cobham_binaryBit hc (Cobham.eqFlag_mem (cobham_pairSnd_comp hc.tailFn) (.const _)) (.const _)

theorem binaryBerkowitzVerdict_mem_FP : binaryBerkowitzVerdict ∈ FP :=
  CobhamFP_subset_FP (cobham_pairFst_comp (cobham_pairSnd_comp (Cobham.proj 0)).tailFn)

/-- The actual loop operations; no controller implementation is an input premise. -/
noncomputable def binaryBerkowitzLoopOps (W : Polynomial ℕ) : OracleLoopOps where
  toOracleControllerOps := binaryBerkowitzController
  initializeState := binaryBerkowitzInitialize W
  completed := binaryBerkowitzCompleted
  verdict := binaryBerkowitzVerdict
  initializeState_FP := binaryBerkowitzInitialize_mem_FP W
  completed_FP := binaryBerkowitzCompleted_mem_FP
  verdict_FP := binaryBerkowitzVerdict_mem_FP

theorem binaryBerkowitzLoop_setup (W : Polynomial ℕ) (n : ℕ) (c : FieldCode) [Fact c.Valid]
    (input : List Bool) :
    (binaryBerkowitzLoopOps W).initializeState (oracleMatrixInput n c input) =
      concreteControllerCode c input (W.eval (oracleMatrixInput n c input).length)
        (.eval (.initial : BerkowitzAddress n) []) := by
  simp only [binaryBerkowitzLoopOps, binaryBerkowitzInitialize, oracleMatrixInput,
    controllerParamsOf_pair, concreteControllerCode, concreteControllerParams]
  rfl

theorem binaryBerkowitzLoop_completed (W : Polynomial ℕ) {n : ℕ} (c : FieldCode) [Fact c.Valid]
    (input : List Bool) (window : ℕ) (cfg : EntryConfig (BerkowitzAddress n) c.Carrier) :
    (binaryBerkowitzLoopOps W).completed (concreteControllerCode c input window cfg) =
      [decide cfg.Halted] := by
  cases cfg with
  | eval a stack =>
      simp only [binaryBerkowitzLoopOps, binaryBerkowitzCompleted, concreteControllerCode,
        pairSnd_pair, EntryConfig.framedEncode, binaryBit, caseBit₀]
      rfl
  | ret v stack =>
      cases stack with
      | nil =>
          simp only [binaryBerkowitzLoopOps, binaryBerkowitzCompleted, concreteControllerCode,
            pairSnd_pair, EntryConfig.framedEncode, List.tail_cons, encodeFramedStack,
            binaryBit, caseBit₀, SparseDiv.StringArith.eqFlag_self]
          rfl
      | cons frame stack =>
          simp only [binaryBerkowitzLoopOps, binaryBerkowitzCompleted, concreteControllerCode,
            pairSnd_pair, EntryConfig.framedEncode, List.tail_cons, encodeFramedStack,
            binaryBit, List.headD_cons, ↓reduceIte, EntryConfig.Halted, decide_false]
          rcases Cobham.eqFlag_flag
            (true :: pair (frame.encode BerkowitzAddress.binaryCode (encodedFieldScalar c))
              (encodeFramedStack BerkowitzAddress.binaryCode (encodedFieldScalar c) stack))
            [false] with he | he
          · have hn := (Cobham.eqFlag_eq_true_iff _ _).mp he
            cases hn
          · exact he

theorem binaryBerkowitzLoop_verdict (W : Polynomial ℕ) {n : ℕ} (c : FieldCode) [Fact c.Valid]
    (input : List Bool) (window : ℕ) (v : c.Carrier) :
    (binaryBerkowitzLoopOps W).verdict
      (concreteControllerCode (n := n) c input window (.ret v [])) = encodedFieldScalar c v := by
  simp only [binaryBerkowitzLoopOps, binaryBerkowitzVerdict, concreteControllerCode,
    pairSnd_pair, EntryConfig.framedEncode, List.tail_cons, pairFst_pair]

end SparseIrred.UpperBounds.Section4
