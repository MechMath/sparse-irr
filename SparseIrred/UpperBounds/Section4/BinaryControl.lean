import SparseIrred.UpperBounds.Section4.BinaryDecision
import SparseIrred.UpperBounds.Section4.Conclusion

/-!
# Executable binary dispatch for the three validated stages

The driver keeps the original input in every running state and changes stage
only after receiving a returned scalar. The following generic composition is
instantiated by concrete address, field and input routines, not by an oracle for
the output of any stage.
-/

namespace SparseIrred.UpperBounds.Section4

open Complexity SparseDiv SparseDiv.StringArith

set_option backward.isDefEq.respectTransparency false

def binaryStackHalted (cfg : List Bool) : List Bool :=
  andBit cfg (notBit (pairSnd cfg.tail))

theorem binaryStackHalted_correct {A R : Type*} (ea : A → List Bool) (er : R → List Bool)
    (c : EntryConfig A R) : binaryStackHalted (c.framedEncode ea er) = [decide c.Halted] := by
  cases c with
  | eval a stack =>
      simp [binaryStackHalted, EntryConfig.framedEncode, andBit, caseBit₀, EntryConfig.Halted]
  | ret v stack => cases stack <;>
      simp [binaryStackHalted, EntryConfig.framedEncode, encodeFramedStack, andBit,
        notBit, caseBit₀, EntryConfig.Halted] <;>
      first | exact decide_eq_true trivial | exact decide_eq_false (fun h ↦ h)

theorem cobham_binaryStackHalted {n : ℕ} {c : (Fin n → List Bool) → List Bool}
    (hc : Cobham c) : Cobham fun u ↦ binaryStackHalted (c u) :=
  Cobham.andFn hc (Cobham.notFn (cobham_pairSnd_comp hc.tailFn))

def binaryDecisionAsBool (v : List Bool) : List Bool :=
  caseBit₀ v (caseBit₀ v.tail [false] (caseBit₀ v.tail.tail [true] [false])) [false]

theorem binaryDecisionAsBool_correct {K : Type*} (e : K → List Bool) (v : DecisionScalar K) :
    binaryDecisionAsBool (v.binaryCode e) = [v.asBool] := by
  cases v with
  | scalar a => rfl
  | nonzeroTag => rfl
  | flag b => cases b <;> rfl

theorem cobham_binaryDecisionAsBool {n : ℕ} {v : (Fin n → List Bool) → List Bool}
    (hv : Cobham v) : Cobham fun u ↦ binaryDecisionAsBool (v u) :=
  Cobham.iteFn hv (Cobham.iteFn hv.tailFn (.const _)
    (Cobham.iteFn hv.tailFn.tailFn (.const _) (.const _))) (.const _)

/-- Binary routines for one stage, including polynomial-time proofs on all strings. -/
structure BinaryStageRoutines where
  initial : List Bool → List Bool
  advance : List Bool → List Bool → List Bool
  accept : List Bool → List Bool → List Bool
  initial_cobham : Cobham fun u : Fin 1 → List Bool ↦ initial (u 0)
  advance_cobham : Cobham fun u : Fin 2 → List Bool ↦ advance (u 0) (u 1)
  accept_cobham : Cobham fun u : Fin 2 → List Bool ↦ accept (u 0) (u 1)

def binaryRunningCode (phase : List Bool) (s cfg : List Bool) : List Bool :=
  [false, false] ++ pair s (phase ++ cfg)

def binaryDoneCode (flag : List Bool) : List Bool := true :: caseBit₀ flag [true] [false]

def binaryFirstAdvance (first second : BinaryStageRoutines) (s cfg : List Bool) : List Bool :=
  caseBit₀ (binaryStackHalted cfg)
    (caseBit₀ (first.accept s (pairFst cfg.tail))
      (binaryRunningCode [false, true] s (second.initial s)) (binaryDoneCode [false]))
    (binaryRunningCode [false, false] s (first.advance s cfg))

def binarySecondAdvance (second third : BinaryStageRoutines) (s cfg : List Bool) : List Bool :=
  caseBit₀ (binaryStackHalted cfg)
    (caseBit₀ (second.accept s (pairFst cfg.tail))
      (binaryRunningCode [true, false] s (third.initial s)) (binaryDoneCode [false]))
    (binaryRunningCode [false, true] s (second.advance s cfg))

def binaryThirdAdvance (third : BinaryStageRoutines) (s cfg : List Bool) : List Bool :=
  caseBit₀ (binaryStackHalted cfg)
    (binaryDoneCode (third.accept s (pairFst cfg.tail)))
    (binaryRunningCode [true, false] s (third.advance s cfg))

/-- Raw-string stage dispatch; no semantic validity test occurs here. -/
def uniformBinaryStep (first second third : BinaryStageRoutines) (state : List Bool) : List Bool :=
  let s := pairFst state.tail.tail
  let tagged := pairSnd state.tail.tail
  let cfg := tagged.tail.tail
  caseBit₀ state state.tail
    (caseBit₀ state.tail
      (binaryRunningCode [false, false] state.tail.tail (first.initial state.tail.tail))
      (caseBit₀ tagged (binaryThirdAdvance third s cfg)
        (caseBit₀ tagged.tail (binarySecondAdvance second third s cfg)
          (binaryFirstAdvance first second s cfg))))

theorem BinaryStageRoutines.cobham_initial (B : BinaryStageRoutines) {n : ℕ}
    {s : (Fin n → List Bool) → List Bool} (hs : Cobham s) :
    Cobham fun u ↦ B.initial (s u) :=
  (Cobham.comp B.initial_cobham (fun _ ↦ hs)).of_eq (fun _ ↦ rfl)

theorem BinaryStageRoutines.cobham_advance (B : BinaryStageRoutines) {n : ℕ}
    {s c : (Fin n → List Bool) → List Bool} (hs : Cobham s) (hc : Cobham c) :
    Cobham fun u ↦ B.advance (s u) (c u) :=
  (Cobham.comp B.advance_cobham (gs := fun i u ↦ (![s u, c u] : Fin 2 → List Bool) i)
    (fun i ↦ by fin_cases i <;> assumption)).of_eq (fun _ ↦ rfl)

theorem BinaryStageRoutines.cobham_accept (B : BinaryStageRoutines) {n : ℕ}
    {s c : (Fin n → List Bool) → List Bool} (hs : Cobham s) (hc : Cobham c) :
    Cobham fun u ↦ B.accept (s u) (c u) :=
  (Cobham.comp B.accept_cobham (gs := fun i u ↦ (![s u, c u] : Fin 2 → List Bool) i)
    (fun i ↦ by fin_cases i <;> assumption)).of_eq (fun _ ↦ rfl)

theorem cobham_binaryRunningCode {n : ℕ} (phase : List Bool)
    {s c : (Fin n → List Bool) → List Bool} (hs : Cobham s) (hc : Cobham c) :
    Cobham fun u ↦ binaryRunningCode phase (s u) (c u) :=
  Cobham.appendFn (.const _) (cobham_pair_comp hs (Cobham.appendFn (.const phase) hc))

theorem cobham_binaryDoneCode {n : ℕ} {f : (Fin n → List Bool) → List Bool} (hf : Cobham f) :
    Cobham fun u ↦ binaryDoneCode (f u) :=
  cobham_cons true (Cobham.iteFn hf (.const _) (.const _))

theorem cobham_binaryFirstAdvance (B C : BinaryStageRoutines) {n : ℕ}
    {s c : (Fin n → List Bool) → List Bool} (hs : Cobham s) (hc : Cobham c) :
    Cobham fun u ↦ binaryFirstAdvance B C (s u) (c u) :=
  Cobham.iteFn (cobham_binaryStackHalted hc)
    (Cobham.iteFn (B.cobham_accept hs (cobham_pairFst_comp hc.tailFn))
      (cobham_binaryRunningCode _ hs (C.cobham_initial hs)) (.const _))
    (cobham_binaryRunningCode _ hs (B.cobham_advance hs hc))

theorem cobham_binarySecondAdvance (B C : BinaryStageRoutines) {n : ℕ}
    {s c : (Fin n → List Bool) → List Bool} (hs : Cobham s) (hc : Cobham c) :
    Cobham fun u ↦ binarySecondAdvance B C (s u) (c u) :=
  Cobham.iteFn (cobham_binaryStackHalted hc)
    (Cobham.iteFn (B.cobham_accept hs (cobham_pairFst_comp hc.tailFn))
      (cobham_binaryRunningCode _ hs (C.cobham_initial hs)) (.const _))
    (cobham_binaryRunningCode _ hs (B.cobham_advance hs hc))

theorem cobham_binaryThirdAdvance (B : BinaryStageRoutines) {n : ℕ}
    {s c : (Fin n → List Bool) → List Bool} (hs : Cobham s) (hc : Cobham c) :
    Cobham fun u ↦ binaryThirdAdvance B (s u) (c u) :=
  Cobham.iteFn (cobham_binaryStackHalted hc)
    (cobham_binaryDoneCode (B.cobham_accept hs (cobham_pairFst_comp hc.tailFn)))
    (cobham_binaryRunningCode _ hs (B.cobham_advance hs hc))

theorem uniformBinaryStep_mem_FP (B C D : BinaryStageRoutines) : uniformBinaryStep B C D ∈ FP := by
  apply CobhamFP_subset_FP
  have hraw := Cobham.proj (n := 1) 0
  have hs := cobham_pairFst_comp hraw.tailFn.tailFn
  have htag := cobham_pairSnd_comp hraw.tailFn.tailFn
  have hc := htag.tailFn.tailFn
  exact Cobham.iteFn hraw hraw.tailFn (Cobham.iteFn hraw.tailFn
    (cobham_binaryRunningCode _ hraw.tailFn.tailFn (B.cobham_initial hraw.tailFn.tailFn))
    (Cobham.iteFn htag (cobham_binaryThirdAdvance D hs hc)
      (Cobham.iteFn htag.tailFn (cobham_binarySecondAdvance C D hs hc)
        (cobham_binaryFirstAdvance B C hs hc))))

@[simp] theorem uniformBinaryStep_initial (B C D : BinaryStageRoutines) (s : List Bool) :
    uniformBinaryStep B C D (pair [] s) = binaryRunningCode [false, false] s (B.initial s) := rfl

@[simp] theorem uniformBinaryStep_done (B C D : BinaryStageRoutines) (s : List Bool) (b : Bool) :
    uniformBinaryStep B C D (uniformCode s (.done b)) = [b] := rfl

/-- Local refinement facts for a single stage. Concrete instances below are
proved from the binary instruction, arithmetic and stack implementations. -/
structure BinaryStageRealization (s : List Bool) (B : BinaryStageRoutines) (S : StageSpec)
    (code : S.ReachableCfg → List Bool) : Prop where
  initial : B.initial s = code S.initialCfg
  advance : ∀ c, B.advance s (code c) = code (S.advance c)
  halted : ∀ c, binaryStackHalted (code c) = [decide c.val.Halted]
  accept : ∀ c (hc : c.val.Halted), B.accept s (pairFst (code c).tail) =
    [S.output (S.returnedValue c.val hc)]

theorem binaryStageRealization_of_encoded (s : List Bool) (B : BinaryStageRoutines) (S : StageSpec)
    (ea : S.Addr → List Bool) (er : S.Scalar → List Bool)
    (hi : B.initial s = S.initialConfig.framedEncode ea er)
    (hs : ∀ c, B.advance s (c.framedEncode ea er) = (S.program.step c).framedEncode ea er)
    (ho : ∀ v, B.accept s (er v) = [S.output v]) :
    BinaryStageRealization s B S (fun c ↦ c.val.framedEncode ea er) where
  initial := hi
  advance c := hs c.val
  halted c := binaryStackHalted_correct ea er c.val
  accept c hc := by
    rcases c with ⟨c, hreach⟩
    cases c with
    | eval a stack => exact hc.elim
    | ret v stack =>
      cases stack with
      | nil =>
          change B.accept s (pairFst (pair (er v) (encodeFramedStack ea er []) )) = [S.output v]
          rw [pairFst_pair]
          exact ho v
      | cons f stack => exact hc.elim

theorem uniformBinaryStep_first (B C D : BinaryStageRoutines) (s : List Bool)
    (c : (primeStage s).ReachableCfg) :
    uniformBinaryStep B C D (uniformCode s (.first c)) = binaryFirstAdvance B C s (primeConfigCode s c) := by
  simp [uniformBinaryStep, uniformCode, caseBit₀]

theorem uniformBinaryStep_second (B C D : BinaryStageRoutines) (s : List Bool)
    (h : (primeStage s).answer = true) (c : (modulusStage s h).ReachableCfg) :
    uniformBinaryStep B C D (uniformCode s (.second h c)) =
      binarySecondAdvance C D s (modulusConfigCode s h c) := by
  simp [uniformBinaryStep, uniformCode, caseBit₀]

theorem uniformBinaryStep_third (B C D : BinaryStageRoutines) (s : List Bool)
    (h : (primeStage s).answer = true) (h' : (modulusStage s h).answer = true)
    (c : (sparseStage s h h').ReachableCfg) :
    uniformBinaryStep B C D (uniformCode s (.third h h' c)) =
      binaryThirdAdvance D s (sparseConfigCode s h h' c) := by
  simp [uniformBinaryStep, uniformCode, caseBit₀]

/-- Composition of three proved binary stage implementations eliminates the old
local-realization obligation. This theorem is used with concrete instances. -/
theorem uniformBinaryStep_realization (B C D : BinaryStageRoutines)
    (hB : ∀ s, BinaryStageRealization s B (primeStage s) (primeConfigCode s))
    (hC : ∀ s h, BinaryStageRealization s C (modulusStage s h) (modulusConfigCode s h))
    (hD : ∀ s h h', BinaryStageRealization s D (sparseStage s h h') (sparseConfigCode s h h')) :
    UniformLocalStepRealization (uniformBinaryStep B C D) where
  polynomial_time := uniformBinaryStep_mem_FP B C D
  initialize_state s := by
    rw [uniformBinaryStep_initial, (hB s).initial]
    rfl
  publish := uniformBinaryStep_done B C D
  step s c hc := by
    cases c with
    | done b => exact (hc trivial).elim
    | first c =>
      rw [uniformBinaryStep_first B C D s c, binaryFirstAdvance, (hB s).halted]
      by_cases hh : c.val.Halted
      · rw [decide_eq_true hh, caseBit₀_cons, Bool.cond_true, (hB s).accept c hh]
        by_cases hv : (primeStage s).output ((primeStage s).returnedValue c.val hh) = true
        · simp only [hv, caseBit₀_cons, Bool.cond_true]
          rw [(hC s ((primeStage s).answer_true_of_returned c hh hv)).initial]
          simp only [uniformStages, ThreeStages.step, hh, ↓reduceDIte, hv, uniformCode]
          rfl
        · have hf : (primeStage s).output ((primeStage s).returnedValue c.val hh) = false :=
            Bool.eq_false_iff.mpr hv
          simp [uniformStages, ThreeStages.step, hh, hv, hf, uniformCode, binaryDoneCode, caseBit₀]
      · rw [decide_eq_false hh, caseBit₀_cons, Bool.cond_false, (hB s).advance]
        simp [uniformStages, ThreeStages.step, hh, uniformCode, binaryRunningCode]
    | second h c =>
      rw [uniformBinaryStep_second B C D s h c, binarySecondAdvance, (hC s h).halted]
      by_cases hh : c.val.Halted
      · rw [decide_eq_true hh, caseBit₀_cons, Bool.cond_true, (hC s h).accept c hh]
        by_cases hv : (modulusStage s h).output ((modulusStage s h).returnedValue c.val hh) = true
        · simp only [hv, caseBit₀_cons, Bool.cond_true]
          rw [(hD s h ((modulusStage s h).answer_true_of_returned c hh hv)).initial]
          simp only [uniformStages, ThreeStages.step, hh, ↓reduceDIte, hv, uniformCode]
          rfl
        · have hf : (modulusStage s h).output ((modulusStage s h).returnedValue c.val hh) = false :=
            Bool.eq_false_iff.mpr hv
          simp [uniformStages, ThreeStages.step, hh, hv, hf, uniformCode, binaryDoneCode, caseBit₀]
      · rw [decide_eq_false hh, caseBit₀_cons, Bool.cond_false, (hC s h).advance]
        simp [uniformStages, ThreeStages.step, hh, uniformCode, binaryRunningCode]
    | third h h' c =>
      rw [uniformBinaryStep_third B C D s h h' c, binaryThirdAdvance, (hD s h h').halted]
      by_cases hh : c.val.Halted
      · rw [decide_eq_true hh, caseBit₀_cons, Bool.cond_true, (hD s h h').accept c hh]
        simp only [uniformStages, ThreeStages.step, hh, ↓reduceDIte, uniformCode, binaryDoneCode,
          caseBit₀_cons]
        cases (sparseStage s h h').output ((sparseStage s h h').returnedValue c.val hh) <;> rfl
      · rw [decide_eq_false hh, caseBit₀_cons, Bool.cond_false, (hD s h h').advance]
        simp [uniformStages, ThreeStages.step, hh, uniformCode, binaryRunningCode]

end SparseIrred.UpperBounds.Section4
