import SparseIrred.UpperBounds.Section4.BerkowitzOracleSpace
import Complexitylib.Classes.Containments.Internal.CodeRewind

/-!
# Polynomial-time single-step simulation of an arbitrary space-bounded oracle TM

The oracle itself may require exponential time. Only one transition is simulated
per call to the encoded step function. Its code width depends on its tape-space
window, independently of the elapsed number of transitions.
-/

noncomputable section
namespace SparseIrred.UpperBounds.Section4

open Complexity Complexity.Cobham

variable {k : ℕ}

/-- The cell ruler has length `W+1`; its doubled version is the tape-block ruler. -/
def oracleRuler (W : ℕ) : List Bool := List.replicate (W + 1) false

@[simp] theorem oracleRuler_length (W : ℕ) : (oracleRuler W).length = W + 1 := by
  simp [oracleRuler]

@[simp] theorem clockRuler_oracleRuler (W : ℕ) : clockRuler (oracleRuler W) = blockRuler W := by
  rw [clockRuler_eq (by simp)]
  simp

/-- A space window together with the full code of one oracle configuration. -/
def oracleConfigCode (M : TM k) (W : ℕ) (c : Cfg k M.Q) : List Bool :=
  pair (oracleRuler W) (Cobham.cfgCode W c)

/-- Initialize the oracle on a query string, given its reusable space ruler. -/
def oracleInit (M : TM k) (z : List Bool) : List Bool :=
  pair (pairFst z) (initFn M (clockRuler (pairFst z)) (pairSnd z))

/-- Advance the oracle by exactly one actual transition, preserving its ruler. -/
def oracleStep (M : TM k) (z : List Bool) : List Bool :=
  pair (pairFst z) (stepFn M (clockRuler (pairFst z)) (pairSnd z))

/-- Inspect only the finite state block to detect a completed oracle call. -/
def oracleHalt (M : TM k) (z : List Bool) : List Bool :=
  eqFlag ((blockAt (clockRuler (pairFst z)) (pairSnd z) 0).take
    (stateCode M.qhalt).length) (stateCode M.qhalt)

/-- Rewind the encoded output head, then extract its finite binary result. -/
def oracleOutput (z : List Bool) : List Bool :=
  let u := pairFst z
  let R := clockRuler u
  let aligned := (rewindCode R u (outPair R (pairSnd z))).drop R.length
  (cellBits 3 aligned u.tail.length).take
    (runTrue (cellBits 2 aligned u.tail.length) u.tail.length).length

theorem oracleInit_mem_FP (M : TM k) : oracleInit M ∈ FP := by
  apply CobhamFP_subset_FP
  have hu := fstBlockFn (Cobham.proj (0 : Fin 1))
  have hz := sndBlockFn (Cobham.proj (0 : Fin 1))
  exact (comp₂ pairing hu (initFn_mem M (clockRulerFn hu) hz)).of_eq (fun _ ↦ rfl)

theorem oracleStep_mem_FP (M : TM k) : oracleStep M ∈ FP := by
  apply CobhamFP_subset_FP
  have hu := fstBlockFn (Cobham.proj (0 : Fin 1))
  have hz := sndBlockFn (Cobham.proj (0 : Fin 1))
  exact (comp₂ pairing hu (stepFn_mem M (clockRulerFn hu) hz)).of_eq (fun _ ↦ rfl)

theorem oracleHalt_mem_FP (M : TM k) : oracleHalt M ∈ FP := by
  apply CobhamFP_subset_FP
  have hu := fstBlockFn (Cobham.proj (0 : Fin 1))
  have hz := sndBlockFn (Cobham.proj (0 : Fin 1))
  exact (eqFlag_mem (takeFn (Cobham.const (stateCode M.qhalt))
    (takeFn (clockRulerFn hu) hz)) (Cobham.const (stateCode M.qhalt))).of_eq (fun _ ↦ by simp [oracleHalt, blockAt])

theorem oracleOutput_mem_FP : oracleOutput ∈ FP := by
  have hu : (fun z : List Bool ↦ pairFst z) ∈ FP := fstBlock_mem_FP
  have hz : (fun z : List Bool ↦ pairSnd z) ∈ FP := sndBlock_mem_FP
  have hR : (fun z : List Bool ↦ clockRuler (pairFst z)) ∈ FP := by
    exact CobhamFP_subset_FP (clockRulerFn (fstBlockFn (Cobham.proj 0)))
  have hpair := outPairFn_mem_FP hR hz
  have hrew := rewindCodeFn_mem_FP hR hu hpair (fun z ↦ by
    simp only [outPair, List.length_append]
    have h3 : (blockAt (clockRuler (pairFst z)) (pairSnd z) 3).length ≤
        (clockRuler (pairFst z)).length := by simp [blockAt]
    have h4 : (blockAt (clockRuler (pairFst z)) (pairSnd z) 4).length ≤
        (clockRuler (pairFst z)).length := by simp [blockAt]
    omega)
  apply CobhamFP_subset_FP
  have huC := fstBlockFn (Cobham.proj (0 : Fin 1))
  have hRC := clockRulerFn huC
  have hrC := FP_subset_CobhamFP hrew
  have haligned := dropFn hRC hrC
  have ht := tailFn huC
  exact (takeFn (runTrueFn ht (cellBitsFn 2 ht haligned))
    (cellBitsFn 3 ht haligned)).of_eq (fun _ ↦ rfl)

@[simp] theorem oracleInit_code (M : TM k) (W : ℕ) (x : List Bool) (hx : x.length ≤ W) :
    oracleInit M (pair (oracleRuler W) x) = oracleConfigCode M W (M.initCfg x) := by
  simp only [oracleInit, pairFst_pair, pairSnd_pair, clockRuler_oracleRuler, oracleConfigCode,
    initFn_eq M W x hx]

/-- Encoded transitions require a spatial invariant, not a time bound. -/
theorem oracleStep_code (M : TM k) (W : ℕ) (c : Cfg k M.Q)
    (hq : Fintype.card M.Q ≤ blockWidth W) (hc : CodeInv W c) :
    oracleStep M (oracleConfigCode M W c) = oracleConfigCode M W (((M.step c).getD c)) := by
  simp only [oracleStep, oracleConfigCode, pairFst_pair, pairSnd_pair, clockRuler_oracleRuler]
  congr 1
  cases hs : M.step c with
  | none =>
    have hh := TM.step_eq_none_iff_halted.mp hs
    simp only [hs, Option.getD_none, Option.getD_some]
    exact stepFn_halted M hh hq hc.head
  | some d =>
    simp only [hs, Option.getD_none, Option.getD_some]
    exact stepFn_eq M hs hq hc.head (hc.start _ (by simp [cfgTapes]))
      (fun i ↦ hc.start _ (by
        rw [cfgTapes]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i, rfl⟩))))
      (stepActs_forall₂ M c hc.start hc.head)

theorem oracleHalt_code (M : TM k) (W : ℕ) (c : Cfg k M.Q)
    (hq : Fintype.card M.Q ≤ blockWidth W) :
    oracleHalt M (oracleConfigCode M W c) = [decide (M.halted c)] := by
  simp only [oracleHalt, oracleConfigCode, pairFst_pair, pairSnd_pair, clockRuler_oracleRuler]
  rw [stateCode_length, state_of_cfgCode W c hq]
  have hf := eqFlag_flag (stateCode c.state) (stateCode M.qhalt)
  by_cases hh : M.halted c
  · have he : stateCode c.state = stateCode M.qhalt := congrArg stateCode hh
    have hd : decide (M.halted c) = true := decide_eq_true hh
    rw [hd]
    exact (eqFlag_eq_true_iff _ _).mpr he
  · have hn : eqFlag (stateCode c.state) (stateCode M.qhalt) ≠ [true] := by
      intro h
      exact hh (stateCode_injective ((eqFlag_eq_true_iff _ _).mp h))
    have hd : decide (M.halted c) = false := decide_eq_false hh
    rw [hd]
    exact hf.resolve_left hn

theorem oracleOutput_code (M : TM k) (W : ℕ) (c : Cfg k M.Q) (y : List Bool)
    (hc : CodeInv W c) (hy : c.output.HasOutput y) (hyW : y.length + 1 ≤ W) :
    oracleOutput (oracleConfigCode M W c) = y := by
  have hs : c.output.StartInvariant := hc.start _ (by simp [cfgTapes])
  have hh : c.output.head ≤ W := hc.head _ (by simp [cfgTapes])
  simp only [oracleOutput, oracleConfigCode, pairFst_pair, pairSnd_pair,
    clockRuler_oracleRuler, outPair_cfgCode,
    rewindCode_pairCode W c.output hs hh (oracleRuler W) (by simp), drop_pairCode_rewound,
    List.length_tail, oracleRuler_length, Nat.add_sub_cancel]
  exact output_of_cellsCode c.output y hy hyW

/-- The exact encoded size remains linear in the oracle's available tape window. -/
@[simp] theorem oracleConfigCode_length (M : TM k) (W : ℕ) (c : Cfg k M.Q) :
    (oracleConfigCode M W c).length = (2 * codeBlocks k + 2) * (W + 1) + 2 := by
  simp only [oracleConfigCode, pair_length, oracleRuler_length, cfgCode_length,
    blockRuler_length, blockWidth]
  ring

/-- Every reachable configuration satisfies the binary simulator's invariant. -/
theorem oracle_codeInv (M : TM k) (x : List Bool) (S W : ℕ)
    (hW : x.length + S + 1 ≤ W)
    (hspace : ∀ c, M.reaches (M.initCfg x) c → c.WithinDecisionSpace x.length S)
    (t : ℕ) : CodeInv W (M.runCfg (M.initCfg x) t) := by
  obtain ⟨u, hu, hr⟩ := TM.runCfg_reachesIn M (M.initCfg x) t
  obtain ⟨hi, hw, ho⟩ := TM.runCfg_startInvariant M x t
  have hsp := hspace _ (TM.reaches_of_reachesIn hr)
  refine ⟨fun z hz ↦ ?_, fun z hz ↦ ?_⟩ <;>
    rw [cfgTapes, List.mem_cons, List.mem_cons, List.mem_ofFn] at hz <;>
    rcases hz with rfl | rfl | ⟨i, rfl⟩
  · exact hi
  · exact ho
  · exact hw i
  · have := hsp.1.2; omega
  · have := hsp.2; omega
  · have := hsp.1.1 i; omega

/-- An arbitrary number of simulated transitions agrees with the actual oracle run. -/
theorem oracleStep_iterate_code (M : TM k) (x : List Bool) (S W : ℕ)
    (hq : Fintype.card M.Q ≤ blockWidth W) (hW : x.length + S + 1 ≤ W)
    (hspace : ∀ c, M.reaches (M.initCfg x) c → c.WithinDecisionSpace x.length S)
    (t : ℕ) :
    (oracleStep M)^[t] (oracleConfigCode M W (M.initCfg x)) =
      oracleConfigCode M W (M.runCfg (M.initCfg x) t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih,
      oracleStep_code M W _ hq (oracle_codeInv M x S W hW hspace t), TM.runCfg_succ]

end SparseIrred.UpperBounds.Section4
