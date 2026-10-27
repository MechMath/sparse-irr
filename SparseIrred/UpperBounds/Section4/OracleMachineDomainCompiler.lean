import SparseIrred.UpperBounds.Section4.OracleMachineValueDomain
import SparseIrred.UpperBounds.Section4.OracleMachineScalarCompiler

/-! # Scalar compilation on the valid-input domain of Lemma 17 -/

noncomputable section
namespace SparseIrred.UpperBounds.Section4

set_option backward.isDefEq.respectTransparency false

open Complexity Complexity.Cobham SparseIrred.UpperBounds.Machine

/-- Only local binary-controller equations are required; oracle simulation is supplied by the compiler. -/
structure OracleDomainCompilerLaws {k : ℕ} {M : TM k} (F : OracleLoopOps)
    (Valid : List Bool → Prop) (D : ∀ x, Valid x → OracleProgramInput M) : Prop where
  controller : ∀ x hx, OracleControllerLaws F.toOracleControllerOps (D x hx).program (D x hx).request
    (D x hx).source (D x hx).code
  setup : ∀ x hx, F.initializeState x = (D x hx).code (.eval (D x hx).initial [])
  completed : ∀ x hx c, F.completed ((D x hx).code c) = [decide c.Halted]
  verdict : ∀ x hx v, F.verdict ((D x hx).code (.ret v [])) = (D x hx).source.encode v

namespace OracleDomainCompilerLaws
variable {k : ℕ} {M : TM k} {F : OracleLoopOps} {Valid : List Bool → Prop} {D : ∀ x, Valid x → OracleProgramInput M}
    (H : OracleDomainCompilerLaws F Valid D)

include H

private theorem done_code (x : List Bool) (hx : Valid x) (c : (D x hx).Config) :
    oracleCoroutineDone F ((D x hx).encode c) = [decide c.Halted] := by
  cases c with
  | query a stack z => rfl
  | outer c =>
    cases c with
    | eval a stack => simp [OracleProgramInput.encode, oracleCoroutineCode,
        OracleCoroutineConfig.encode, oracleCoroutineDone, selectHead, H.completed x hx,
        EntryConfig.Halted, OracleCoroutineConfig.Halted]
    | ret v stack => cases stack <;> simp [OracleProgramInput.encode, oracleCoroutineCode,
        OracleCoroutineConfig.encode, oracleCoroutineDone, selectHead, H.completed x hx,
        EntryConfig.Halted, OracleCoroutineConfig.Halted]

private theorem iterate_running (x : List Bool) (hx : Valid x) (t stop : ℕ)
    (hmin : ∀ u < stop, ¬((D x hx).step^[u] (D x hx).start).Halted) (ht : t ≤ stop) :
    (oracleLoop M F)^[t + 1] (pair [] x) =
      [false, false] ++ (D x hx).encode ((D x hx).step^[t] (D x hx).start) := by
  induction t with
  | zero =>
    change oracleLoop M F (pair [] x) = _
    rw [oracleLoop_setup, H.setup x hx]
    rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih (by omega), oracleLoop_running]
    · simp only [OracleProgramInput.encode]
      rw [oracleDispatch_code F.toOracleControllerOps (D x hx).program (D x hx).request
        (D x hx).source (D x hx).code (H.controller x hx)]
      rw [Function.iterate_succ_apply']
      rfl
    · rw [H.done_code x hx]
      rw [decide_eq_false (hmin t (by omega))]

private theorem iterate_done (x : List Bool) (hx : Valid x) (e : ℕ)
    (he : ∀ i, oracleTimeExponent M ((D x hx).source.query i).length ((D x hx).source.space i) ≤ e) :
    (oracleLoop M F)^[(D x hx).firstHalt e he + 2] (pair [] x) = true :: (D x hx).source.encode ((D x hx).program.value (D x hx).initial) := by
  have hs := (D x hx).firstHalt_spec e he
  rw [show (D x hx).firstHalt e he + 2 = ((D x hx).firstHalt e he + 1) + 1 by omega,
    Function.iterate_succ_apply', H.iterate_running x hx _ _ hs.2.2 le_rfl, hs.2.1]
  change oracleLoop M F ([false, false, false] ++ (D x hx).code
    (.ret ((D x hx).program.value (D x hx).initial) [])) = _
  rw [oracleLoop_finished, H.verdict x hx]
  simpa [EntryConfig.Halted] using H.completed x hx (.ret ((D x hx).program.value (D x hx).initial) [])

/-- The polynomial state bound includes initialization, dispatch tags and final publication. -/
def statePolynomial (B W V : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.X + Polynomial.C 10 + V + Polynomial.C 2 * B +
    Polynomial.C (2 * codeBlocks k + 2) * (W + Polynomial.C 1)

def clockPolynomial (d e : Polynomial ℕ) : Polynomial ℕ := d + e + Polynomial.C 7

/-- The complete trace is derived from local controller functions and a real oracle machine. -/
def trace (B W V d e : Polynomial ℕ)
    (hB : ∀ x hx t, ((D x hx).code ((D x hx).program.step^[t] (.eval (D x hx).initial []))).length ≤ B.eval x.length)
    (hW : ∀ x hx i, (D x hx).source.window i ≤ W.eval x.length)
    (hV : ∀ x hx, ((D x hx).source.encode ((D x hx).program.value (D x hx).initial)).length ≤ V.eval x.length)
    (hd : ∀ x hx, (D x hx).program.rank (D x hx).initial ≤ d.eval x.length)
    (he : ∀ x hx i, oracleTimeExponent M ((D x hx).source.query i).length ((D x hx).source.space i) ≤
      e.eval x.length) :
    StreamingValueTraceOn Valid (oracleLoop M F)
      (fun x hx ↦ (D x hx).source.encode ((D x hx).program.value (D x hx).initial))
      (statePolynomial (k := k) B W V) (clockPolynomial d e) where
  state x hx t := (oracleLoop M F)^[t] (pair [] x)
  stop x hx := (D x hx).firstHalt (e.eval x.length) (he x hx) + 2
  start _ _ := rfl
  step _ _ _ := Function.iterate_succ_apply' _ _ _
  length_le x hx t ht := by
    have hmin := ((D x hx).firstHalt_spec _ (he x hx)).2.2
    have hstate := (D x hx).encode_iterate_length (B.eval x.length) (W.eval x.length) (hB x hx) (hW x hx)
    by_cases h0 : t = 0
    · subst t
      simp [statePolynomial, pair_length]
      omega
    by_cases hrun : t ≤ (D x hx).firstHalt _ (he x hx) + 1
    · obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
      rw [H.iterate_running x hx u _ hmin (by omega)]
      have hw := hstate u
      simp only [List.length_append, List.length_cons, List.length_nil]
      simp only [statePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X]
      omega
    by_cases hdone : t = (D x hx).firstHalt _ (he x hx) + 2
    · rw [hdone, H.iterate_done x hx]
      have hv := hV x hx
      simp only [statePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, List.length_cons]
      omega
    · have hpub : t = ((D x hx).firstHalt _ (he x hx) + 2) + 1 := by omega
      rw [hpub, Function.iterate_succ_apply', H.iterate_done x hx, oracleLoop_publish_string]
      have hv := hV x hx
      simp only [statePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, List.length_cons]
      omega
  stop_pos _ _ := by omega
  stop_le x hx := by
    have hb := ((D x hx).firstHalt_spec _ (he x hx)).1
    have hb' : (D x hx).firstHalt _ (he x hx) ≤ 2 ^ (d.eval x.length + e.eval x.length + 5) :=
      hb.trans (Nat.pow_le_pow_right (by omega) (by have := hd x hx; omega))
    have hpos : 1 ≤ 2 ^ (d.eval x.length + e.eval x.length + 5) := Nat.one_le_pow _ _ (by omega)
    simp only [clockPolynomial, Polynomial.eval_add, Polynomial.eval_C]
    have hp : 2 ^ (d.eval x.length + e.eval x.length + 7) =
        4 * 2 ^ (d.eval x.length + e.eval x.length + 5) := by
      rw [show d.eval x.length + e.eval x.length + 7 =
        (d.eval x.length + e.eval x.length + 5) + 2 by omega, pow_add]
      norm_num; omega
    rw [hp]
    omega
  running x hx t ht hs := by
    obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
    rw [H.iterate_running x hx u _ ((D x hx).firstHalt_spec _ (he x hx)).2.2 (by omega)]
    rfl
  done x hx := by rw [H.iterate_done x hx]; rfl
  output x hx := by
    rw [Function.iterate_succ_apply', H.iterate_done x hx, oracleLoop_publish_string]

/-- The compiler produces an actual deterministic multitape machine with every-prefix space bounds. -/
theorem machine_exists (B W V d e : Polynomial ℕ)
    (hB : ∀ x hx t, ((D x hx).code ((D x hx).program.step^[t] (.eval (D x hx).initial []))).length ≤ B.eval x.length)
    (hW : ∀ x hx i, (D x hx).source.window i ≤ W.eval x.length)
    (hV : ∀ x hx, ((D x hx).source.encode ((D x hx).program.value (D x hx).initial)).length ≤ V.eval x.length)
    (hd : ∀ x hx, (D x hx).program.rank (D x hx).initial ≤ d.eval x.length)
    (he : ∀ x hx i, oracleTimeExponent M ((D x hx).source.query i).length ((D x hx).source.space i) ≤
      e.eval x.length) :
    ∃ (tapes : ℕ) (tm : TM tapes) (p : Polynomial ℕ),
      (∀ x (hx : Valid x) c, tm.reaches (tm.initCfg x) c → c.WithinDecisionSpace x.length (p.eval x.length)) ∧
      (∀ x hx, ∃ c, tm.reaches (tm.initCfg x) c ∧ tm.halted c ∧
        c.output.HasOutput ((D x hx).source.encode ((D x hx).program.value (D x hx).initial))) :=
  valueMachine_exists_on (oracleLoop_mem_FP M F) (H.trace B W V d e hB hW hV hd he)

/-- The first-halt exponent follows directly from the same polynomial spatial window. -/
def oracleClockFromWindow (M : TM k) (W : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (Fintype.card M.Q) + Polynomial.C 2 * W + Polynomial.C 2 +
    Polynomial.C (3 * k) * (W + Polynomial.C 1) + Polynomial.C 3 * (W + Polynomial.C 2)

/-- A compiler entry point with only spatial hypotheses for the oracle. -/
theorem machine_exists_of_window (B W V d : Polynomial ℕ)
    (hB : ∀ x hx t, ((D x hx).code ((D x hx).program.step^[t] (.eval (D x hx).initial []))).length ≤ B.eval x.length)
    (hW : ∀ x hx i, (D x hx).source.window i ≤ W.eval x.length)
    (hV : ∀ x hx, ((D x hx).source.encode ((D x hx).program.value (D x hx).initial)).length ≤ V.eval x.length)
    (hd : ∀ x hx, (D x hx).program.rank (D x hx).initial ≤ d.eval x.length) :
    ∃ (tapes : ℕ) (tm : TM tapes) (p : Polynomial ℕ),
      (∀ x (hx : Valid x) c, tm.reaches (tm.initCfg x) c → c.WithinDecisionSpace x.length (p.eval x.length)) ∧
      (∀ x hx, ∃ c, tm.reaches (tm.initCfg x) c ∧ tm.halted c ∧
        c.output.HasOutput ((D x hx).source.encode ((D x hx).program.value (D x hx).initial))) := by
  apply H.machine_exists B W V d (oracleClockFromWindow M W) hB hW hV hd
  intro x hx i
  have h := (D x hx).source.window_space i
  have hw := hW x hx i
  simp only [oracleTimeExponent, oracleClockFromWindow, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C]
  have hs : (D x hx).source.space i ≤ W.eval x.length := by omega
  have hq : ((D x hx).source.query i).length ≤ W.eval x.length := by omega
  nlinarith

end OracleDomainCompilerLaws
end SparseIrred.UpperBounds.Section4
