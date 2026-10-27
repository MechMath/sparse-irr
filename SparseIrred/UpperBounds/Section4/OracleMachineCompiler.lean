import SparseIrred.UpperBounds.Section4.OracleMachineLoop
import SparseIrred.UpperBounds.Section4.StackMachine

/-!
# Compilation of a space-bounded oracle coroutine to a genuine deterministic TM

The compiler constructs the bitstring driver and proves its polynomial-time
single-step implementation. Its complete trace, termination and reusable tape
window then follow internally. No whole-coroutine implementation certificate is
an input. Entry machines themselves need only terminate in bounded space.
-/

noncomputable section
namespace SparseIrred.UpperBounds.Section4

set_option backward.isDefEq.respectTransparency false

open Complexity Complexity.Cobham SparseIrred.UpperBounds.Machine

/-- The mathematical controller and the actual entry machine for one input. -/
structure OracleProgramInput {k : ℕ} (M : TM k) where
  Addr : Type
  Scalar : Type
  Query : Type
  add : Add Scalar
  mul : Mul Scalar
  program : EntryProgram Addr Scalar
  request : Addr → Option Query
  answer : Query → Scalar
  source : EntryMachineSource M answer
  initial : Addr
  output : Scalar → Bool
  code : EntryConfig Addr Scalar → List Bool
  request_correct : ∀ a i, request a = some i → program.instruction a = .value (answer i)

attribute [instance] OracleProgramInput.add OracleProgramInput.mul

namespace OracleProgramInput
variable {k : ℕ} {M : TM k} (D : OracleProgramInput M)

abbrev Config := OracleCoroutineConfig D.Addr D.Scalar (List Bool)

def start : D.Config := .outer (.eval D.initial [])
def step : D.Config → D.Config := oracleCoroutineStep D.program D.request D.answer D.source.scalarOracle
def encode : D.Config → List Bool := oracleCoroutineCode D.code
def result : Bool := D.output (D.program.value D.initial)

/-- A polynomial bound on each actual oracle's space supplies an exponential return bound. -/
theorem firstHalt_exists (e : ℕ)
    (he : ∀ i, oracleTimeExponent M (D.source.query i).length (D.source.space i) ≤ e) :
    ∃ t, t ≤ 2 ^ (D.program.rank D.initial + e + 5) ∧
      D.step^[t] D.start = .outer (.ret (D.program.value D.initial) []) ∧
      ∀ u < t, ¬(D.step^[u] D.start).Halted := by
  apply oracleCoroutine_firstHalt D.program D.request D.answer D.source.scalarOracle
    D.request_correct D.initial e
  intro i
  exact (D.source.firstReturn_bound i).le.trans
    (Nat.pow_le_pow_right (by omega) (he i))

def firstHalt (e : ℕ)
    (he : ∀ i, oracleTimeExponent M (D.source.query i).length (D.source.space i) ≤ e) : ℕ :=
  Classical.choose (D.firstHalt_exists e he)

theorem firstHalt_spec (e : ℕ)
    (he : ∀ i, oracleTimeExponent M (D.source.query i).length (D.source.space i) ≤ e) :
    D.firstHalt e he ≤ 2 ^ (D.program.rank D.initial + e + 5) ∧
      D.step^[D.firstHalt e he] D.start = .outer (.ret (D.program.value D.initial) []) ∧
      ∀ u < D.firstHalt e he, ¬(D.step^[u] D.start).Halted :=
  Classical.choose_spec (D.firstHalt_exists e he)

/-- Controller and oracle memory add; oracle work tapes are reused for every query. -/
theorem encode_iterate_length (B W : ℕ)
    (hB : ∀ t, (D.code (D.program.step^[t] (.eval D.initial []))).length ≤ B)
    (hW : ∀ i, D.source.window i ≤ W) (t : ℕ) :
    (D.encode (D.step^[t] D.start)).length ≤
      2 * B + (2 * codeBlocks k + 2) * (W + 1) + 5 := by
  apply oracleCoroutine_space D.program D.request D.answer D.source.scalarOracle
    D.request_correct D.initial D.code id B ((2 * codeBlocks k + 2) * (W + 1) + 2)
  · exact hB
  · intro i u _
    change ((oracleStep M)^[u] (D.source.startCode i)).length ≤ _
    rw [D.source.iterate_length]
    gcongr
    exact hW i
end OracleProgramInput

/-- Only local binary-controller equations are required; oracle simulation is supplied by the compiler. -/
structure OracleCompilerLaws {k : ℕ} {M : TM k} (F : OracleLoopOps)
    (D : List Bool → OracleProgramInput M) : Prop where
  controller : ∀ x, OracleControllerLaws F.toOracleControllerOps (D x).program (D x).request
    (D x).source (D x).code
  setup : ∀ x, F.initializeState x = (D x).code (.eval (D x).initial [])
  completed : ∀ x c, F.completed ((D x).code c) = [decide c.Halted]
  verdict : ∀ x v, F.verdict ((D x).code (.ret v [])) = [(D x).output v]

namespace OracleCompilerLaws
variable {k : ℕ} {M : TM k} {F : OracleLoopOps} {D : List Bool → OracleProgramInput M}
    (H : OracleCompilerLaws F D)

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
    (oracleLoop M F)^[(D x).firstHalt e he + 2] (pair [] x) = [true, (D x).result] := by
  have hs := (D x).firstHalt_spec e he
  rw [show (D x).firstHalt e he + 2 = ((D x).firstHalt e he + 1) + 1 by omega,
    Function.iterate_succ_apply', H.iterate_running x _ _ hs.2.2 le_rfl, hs.2.1]
  change oracleLoop M F ([false, false, false] ++ (D x).code
    (.ret ((D x).program.value (D x).initial) [])) = _
  rw [oracleLoop_finished, H.verdict]
  rfl
  simpa [EntryConfig.Halted] using H.completed x (.ret ((D x).program.value (D x).initial) [])

/-- The polynomial state bound includes initialization, dispatch tags and final publication. -/
def statePolynomial (B W : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.X + Polynomial.C 10 + Polynomial.C 2 * B +
    Polynomial.C (2 * codeBlocks k + 2) * (W + Polynomial.C 1)

def clockPolynomial (d e : Polynomial ℕ) : Polynomial ℕ := d + e + Polynomial.C 7

/-- The complete trace is derived from local controller functions and a real oracle machine. -/
def trace (B W d e : Polynomial ℕ)
    (hB : ∀ x t, ((D x).code ((D x).program.step^[t] (.eval (D x).initial []))).length ≤ B.eval x.length)
    (hW : ∀ x i, (D x).source.window i ≤ W.eval x.length)
    (hd : ∀ x, (D x).program.rank (D x).initial ≤ d.eval x.length)
    (he : ∀ x i, oracleTimeExponent M ((D x).source.query i).length ((D x).source.space i) ≤
      e.eval x.length) :
    StreamingTrace (oracleLoop M F) (fun x ↦ (D x).result)
      (statePolynomial (k := k) B W) (clockPolynomial d e) where
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
      simp [statePolynomial]; omega
    · have hpub : t = ((D x).firstHalt _ (he x) + 2) + 1 := by omega
      rw [hpub, Function.iterate_succ_apply', H.iterate_done, oracleLoop_publish]
      simp [statePolynomial]; omega
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
  answer_nonempty x := by
    rw [Function.iterate_succ_apply', H.iterate_done, oracleLoop_publish]
    simp
  answer_eq x := by rw [Function.iterate_succ_apply', H.iterate_done, oracleLoop_publish]; rfl

/-- The compiler produces an actual deterministic multitape machine with every-prefix space bounds. -/
theorem machine_exists (B W d e : Polynomial ℕ)
    (hB : ∀ x t, ((D x).code ((D x).program.step^[t] (.eval (D x).initial []))).length ≤ B.eval x.length)
    (hW : ∀ x i, (D x).source.window i ≤ W.eval x.length)
    (hd : ∀ x, (D x).program.rank (D x).initial ≤ d.eval x.length)
    (he : ∀ x i, oracleTimeExponent M ((D x).source.query i).length ((D x).source.space i) ≤
      e.eval x.length) :
    ∃ (tapes : ℕ) (tm : TM tapes) (p : Polynomial ℕ),
      (∀ x c, tm.reaches (tm.initCfg x) c → c.WithinDecisionSpace x.length (p.eval x.length)) ∧
      (∀ x, ∃ c, tm.reaches (tm.initCfg x) c ∧ tm.halted c ∧
        c.output.cells 1 = Γ.ofBool ((D x).result)) :=
  streamingMachine_exists (oracleLoop_mem_FP M F) (H.trace B W d e hB hW hd he)

/-- The resulting language is in PSPACE; no full-oracle FP or full-coroutine certificate is assumed. -/
theorem language_mem_PSPACE (B W d e : Polynomial ℕ)
    (hB : ∀ x t, ((D x).code ((D x).program.step^[t] (.eval (D x).initial []))).length ≤ B.eval x.length)
    (hW : ∀ x i, (D x).source.window i ≤ W.eval x.length)
    (hd : ∀ x, (D x).program.rank (D x).initial ≤ d.eval x.length)
    (he : ∀ x i, oracleTimeExponent M ((D x).source.query i).length ((D x).source.space i) ≤
      e.eval x.length) : {x | (D x).result = true} ∈ PSPACE :=
  streamingLanguage_mem_PSPACE (oracleLoop_mem_FP M F) (H.trace B W d e hB hW hd he)
    (fun _ ↦ Iff.rfl)

end OracleCompilerLaws
end SparseIrred.UpperBounds.Section4
