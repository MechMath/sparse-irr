import SparseIrred.UpperBounds.Section4.OracleMachineValueCompiler

/-! # Full scalar-output compilation of arbitrary-space entry-oracle coroutines -/

noncomputable section
namespace SparseIrred.UpperBounds.Section4

set_option backward.isDefEq.respectTransparency false

open Complexity Complexity.Cobham SparseIrred.UpperBounds.Machine

@[simp] theorem oracleLoop_publish_string {k : ℕ} (M : TM k) (F : OracleLoopOps)
    (value : List Bool) : oracleLoop M F (true :: value) = value := rfl

/-- Only local binary-controller equations are required; oracle simulation is supplied by the compiler. -/
structure OracleScalarCompilerLaws {k : ℕ} {M : TM k} (F : OracleLoopOps)
    (D : List Bool → OracleProgramInput M) : Prop where
  controller : ∀ x, OracleControllerLaws F.toOracleControllerOps (D x).program (D x).request
    (D x).source (D x).code
  setup : ∀ x, F.initializeState x = (D x).code (.eval (D x).initial [])
  completed : ∀ x c, F.completed ((D x).code c) = [decide c.Halted]
  verdict : ∀ x v, F.verdict ((D x).code (.ret v [])) = (D x).source.encode v

namespace OracleScalarCompilerLaws
variable {k : ℕ} {M : TM k} {F : OracleLoopOps} {D : List Bool → OracleProgramInput M}
    (H : OracleScalarCompilerLaws F D)

include H

private theorem done_code (x : List Bool) (c : (D x).Config) :
    oracleCoroutineDone F ((D x).encode c) = [decide c.Halted] := by
  cases c with
  | query a stack z => rfl
  | outer c =>
    cases c with
    | eval a stack => simp [OracleProgramInput.encode, oracleCoroutineCode,
        OracleCoroutineConfig.encode, oracleCoroutineDone, selectHead, H.completed,
        EntryConfig.Halted, OracleCoroutineConfig.Halted]
    | ret v stack => cases stack <;> simp [OracleProgramInput.encode, oracleCoroutineCode,
        OracleCoroutineConfig.encode, oracleCoroutineDone, selectHead, H.completed,
        EntryConfig.Halted, OracleCoroutineConfig.Halted]

private theorem iterate_running (x : List Bool) (t stop : ℕ)
    (hmin : ∀ u < stop, ¬((D x).step^[u] (D x).start).Halted) (ht : t ≤ stop) :
    (oracleLoop M F)^[t + 1] (pair [] x) =
      [false, false] ++ (D x).encode ((D x).step^[t] (D x).start) := by
  induction t with
  | zero =>
    change oracleLoop M F (pair [] x) = _
    rw [oracleLoop_setup, H.setup]
    rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih (by omega), oracleLoop_running]
    · simp only [OracleProgramInput.encode]
      rw [oracleDispatch_code F.toOracleControllerOps (D x).program (D x).request
        (D x).source (D x).code (H.controller x)]
      rw [Function.iterate_succ_apply']
      rfl
    · rw [H.done_code]
      rw [decide_eq_false (hmin t (by omega))]

private theorem iterate_done (x : List Bool) (e : ℕ)
    (he : ∀ i, oracleTimeExponent M ((D x).source.query i).length ((D x).source.space i) ≤ e) :
    (oracleLoop M F)^[(D x).firstHalt e he + 2] (pair [] x) = true :: (D x).source.encode ((D x).program.value (D x).initial) := by
  have hs := (D x).firstHalt_spec e he
  rw [show (D x).firstHalt e he + 2 = ((D x).firstHalt e he + 1) + 1 by omega,
    Function.iterate_succ_apply', H.iterate_running x _ _ hs.2.2 le_rfl, hs.2.1]
  change oracleLoop M F ([false, false, false] ++ (D x).code
    (.ret ((D x).program.value (D x).initial) [])) = _
  rw [oracleLoop_finished, H.verdict]
  simpa [EntryConfig.Halted] using H.completed x (.ret ((D x).program.value (D x).initial) [])

/-- The polynomial state bound includes initialization, dispatch tags and final publication. -/
def statePolynomial (B W V : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.X + Polynomial.C 10 + V + Polynomial.C 2 * B +
    Polynomial.C (2 * codeBlocks k + 2) * (W + Polynomial.C 1)

def clockPolynomial (d e : Polynomial ℕ) : Polynomial ℕ := d + e + Polynomial.C 7

/-- The complete trace is derived from local controller functions and a real oracle machine. -/
def trace (B W V d e : Polynomial ℕ)
    (hB : ∀ x t, ((D x).code ((D x).program.step^[t] (.eval (D x).initial []))).length ≤ B.eval x.length)
    (hW : ∀ x i, (D x).source.window i ≤ W.eval x.length)
    (hV : ∀ x, ((D x).source.encode ((D x).program.value (D x).initial)).length ≤ V.eval x.length)
    (hd : ∀ x, (D x).program.rank (D x).initial ≤ d.eval x.length)
    (he : ∀ x i, oracleTimeExponent M ((D x).source.query i).length ((D x).source.space i) ≤
      e.eval x.length) :
    StreamingValueTrace (oracleLoop M F)
      (fun x ↦ (D x).source.encode ((D x).program.value (D x).initial))
      (statePolynomial (k := k) B W V) (clockPolynomial d e) where
  state x t := (oracleLoop M F)^[t] (pair [] x)
  stop x := (D x).firstHalt (e.eval x.length) (he x) + 2
  start _ := rfl
  step _ _ := Function.iterate_succ_apply' _ _ _
  length_le x t ht := by
    have hmin := ((D x).firstHalt_spec _ (he x)).2.2
    have hstate := (D x).encode_iterate_length (B.eval x.length) (W.eval x.length) (hB x) (hW x)
    by_cases h0 : t = 0
    · subst t
      simp [statePolynomial, pair_length]
      omega
    by_cases hrun : t ≤ (D x).firstHalt _ (he x) + 1
    · obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
      rw [H.iterate_running x u _ hmin (by omega)]
      have hw := hstate u
      simp only [List.length_append, List.length_cons, List.length_nil]
      simp only [statePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X]
      omega
    by_cases hdone : t = (D x).firstHalt _ (he x) + 2
    · rw [hdone, H.iterate_done]
      have hv := hV x
      simp only [statePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, List.length_cons]
      omega
    · have hpub : t = ((D x).firstHalt _ (he x) + 2) + 1 := by omega
      rw [hpub, Function.iterate_succ_apply', H.iterate_done, oracleLoop_publish_string]
      have hv := hV x
      simp only [statePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, List.length_cons]
      omega
  stop_pos _ := by omega
  stop_le x := by
    have hb := ((D x).firstHalt_spec _ (he x)).1
    have hb' : (D x).firstHalt _ (he x) ≤ 2 ^ (d.eval x.length + e.eval x.length + 5) :=
      hb.trans (Nat.pow_le_pow_right (by omega) (by have := hd x; omega))
    have hpos : 1 ≤ 2 ^ (d.eval x.length + e.eval x.length + 5) := Nat.one_le_pow _ _ (by omega)
    simp only [clockPolynomial, Polynomial.eval_add, Polynomial.eval_C]
    have hp : 2 ^ (d.eval x.length + e.eval x.length + 7) =
        4 * 2 ^ (d.eval x.length + e.eval x.length + 5) := by
      rw [show d.eval x.length + e.eval x.length + 7 =
        (d.eval x.length + e.eval x.length + 5) + 2 by omega, pow_add]
      norm_num; omega
    rw [hp]
    omega
  running x t ht hs := by
    obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
    rw [H.iterate_running x u _ ((D x).firstHalt_spec _ (he x)).2.2 (by omega)]
    rfl
  done x := by rw [H.iterate_done]; rfl
  output x := by
    rw [Function.iterate_succ_apply', H.iterate_done, oracleLoop_publish_string]

/-- The compiler produces an actual deterministic multitape machine with every-prefix space bounds. -/
theorem machine_exists (B W V d e : Polynomial ℕ)
    (hB : ∀ x t, ((D x).code ((D x).program.step^[t] (.eval (D x).initial []))).length ≤ B.eval x.length)
    (hW : ∀ x i, (D x).source.window i ≤ W.eval x.length)
    (hV : ∀ x, ((D x).source.encode ((D x).program.value (D x).initial)).length ≤ V.eval x.length)
    (hd : ∀ x, (D x).program.rank (D x).initial ≤ d.eval x.length)
    (he : ∀ x i, oracleTimeExponent M ((D x).source.query i).length ((D x).source.space i) ≤
      e.eval x.length) :
    ∃ (tapes : ℕ) (tm : TM tapes) (p : Polynomial ℕ),
      (∀ x c, tm.reaches (tm.initCfg x) c → c.WithinDecisionSpace x.length (p.eval x.length)) ∧
      (∀ x, ∃ c, tm.reaches (tm.initCfg x) c ∧ tm.halted c ∧
        c.output.HasOutput ((D x).source.encode ((D x).program.value (D x).initial))) :=
  valueMachine_exists (oracleLoop_mem_FP M F) (H.trace B W V d e hB hW hV hd he)

/-- The first-halt exponent follows directly from the same polynomial spatial window. -/
def oracleClockFromWindow (M : TM k) (W : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (Fintype.card M.Q) + Polynomial.C 2 * W + Polynomial.C 2 +
    Polynomial.C (3 * k) * (W + Polynomial.C 1) + Polynomial.C 3 * (W + Polynomial.C 2)

/-- A compiler entry point with only spatial hypotheses for the oracle. -/
theorem machine_exists_of_window (B W V d : Polynomial ℕ)
    (hB : ∀ x t, ((D x).code ((D x).program.step^[t] (.eval (D x).initial []))).length ≤ B.eval x.length)
    (hW : ∀ x i, (D x).source.window i ≤ W.eval x.length)
    (hV : ∀ x, ((D x).source.encode ((D x).program.value (D x).initial)).length ≤ V.eval x.length)
    (hd : ∀ x, (D x).program.rank (D x).initial ≤ d.eval x.length) :
    ∃ (tapes : ℕ) (tm : TM tapes) (p : Polynomial ℕ),
      (∀ x c, tm.reaches (tm.initCfg x) c → c.WithinDecisionSpace x.length (p.eval x.length)) ∧
      (∀ x, ∃ c, tm.reaches (tm.initCfg x) c ∧ tm.halted c ∧
        c.output.HasOutput ((D x).source.encode ((D x).program.value (D x).initial))) := by
  apply H.machine_exists B W V d (oracleClockFromWindow M W) hB hW hV hd
  intro x i
  have h := (D x).source.window_space i
  have hw := hW x i
  simp only [oracleTimeExponent, oracleClockFromWindow, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C]
  have hs : (D x).source.space i ≤ W.eval x.length := by omega
  have hq : ((D x).source.query i).length ≤ W.eval x.length := by omega
  nlinarith

end OracleScalarCompilerLaws
end SparseIrred.UpperBounds.Section4
