import Complexitylib.Models.TuringMachine.Oracle
import Complexitylib.Models.TuringMachine.Lift
import Complexitylib.Models.TuringMachine.Frame
import Complexitylib.Models.TuringMachine.OutputBounds
import Complexitylib.Models.TuringMachine.Tape.Encoding
import Complexitylib.Models.TuringMachine.Combinators.Internal.Generic
import Complexitylib.Classes.P
import Complexitylib.Classes.P.Defs

/-!
# Query counting and polynomial-time one-query Turing reductions

complexitylib provides deterministic Boolean-oracle Turing machines (`OracleTM`: one step per
lookup, a dedicated query tape) but no query counting and no Turing reductions.  This file adds:

* `reachesInQ machine oracle t q start result` — the exact-time run of `OracleTM.reachesIn`,
  additionally counting in `q` the steps taken from a query state (every lookup of the **whole**
  run is counted);
* `OneQueryReducesPoly L L'` — a deterministic oracle TM with a polynomial time bound which, for
  every oracle deciding `L'`, decides `L` on every input with at most one oracle query in the
  whole run.

`oneQueryReducesPoly_of_neg` builds, from an FP map `f` with `x ∈ L ↔ f x ∉ L'`, the machine
"compute `f x` on the query tape, query once, output the negated answer" and proves correctness,
the time bound and that the run makes exactly one query (`exists_negQuery_machine`).

## The machine

`negQueryTM M` (for an FP machine `M : TM k`) has state space `M.Q ⊕ NegQuery.Phase`.  It runs
`M` with `M`'s output tape played by the query tape, then rewinds and scans the query tape so that
its head sits on the first blank after `f x` (the query is the content of cells `1 … head-1`),
asks the oracle once and writes the negated answer in output cell `1`.  The main run lemma is
`negQueryTM_run`: time `≤ 3 T(|x|) + 6`, exactly one query.
-/

open Complexity

namespace SparseIrred

/-- Exact-time oracle execution with query counting. -/
inductive reachesInQ {n : ℕ} (machine : OracleTM n) (oracle : BooleanOracle) :
    ℕ → ℕ → OracleCfg n machine.Q → OracleCfg n machine.Q → Prop where
  | zero {cfg} : reachesInQ machine oracle 0 0 cfg cfg
  | step {cfg middle result time queries} :
      machine.step oracle cfg = some middle →
      reachesInQ machine oracle time queries middle result →
      reachesInQ machine oracle (time + 1)
        (queries + if (machine.queryTransition cfg.state).isSome then 1 else 0) cfg result

/-- Forgetting the query count of a counted run. -/
theorem reachesInQ.toReachesIn {n : ℕ} {machine : OracleTM n} {oracle : BooleanOracle}
    {t q : ℕ} {c c' : OracleCfg n machine.Q} (h : reachesInQ machine oracle t q c c') :
    machine.reachesIn oracle t c c' := by
  induction h with
  | zero => exact .zero
  | step hs _ ih => exact .step hs ih

/-- The query count of a run is determined by its length and start: "the run makes exactly `q`
queries" is well defined. -/
theorem reachesInQ_functional {n : ℕ} {machine : OracleTM n} {oracle : BooleanOracle}
    {t q₁ q₂ : ℕ} {c c₁ c₂ : OracleCfg n machine.Q} (h₁ : reachesInQ machine oracle t q₁ c c₁)
    (h₂ : reachesInQ machine oracle t q₂ c c₂) : q₁ = q₂ ∧ c₁ = c₂ := by
  induction h₁ generalizing q₂ with
  | zero => cases h₂; exact ⟨rfl, rfl⟩
  | step hs _ ih =>
    cases h₂ with
    | step hs' hr' =>
      have hm := Option.some.inj (hs.symm.trans hs')
      subst hm
      obtain ⟨hq, hc⟩ := ih hr'
      exact ⟨by rw [hq], hc⟩

/-- Concatenation of counted runs: times and query counts add up. -/
theorem reachesInQ.trans {n : ℕ} {machine : OracleTM n} {oracle : BooleanOracle}
    {t₁ t₂ q₁ q₂ : ℕ} {c₁ c₂ c₃ : OracleCfg n machine.Q}
    (h₁ : reachesInQ machine oracle t₁ q₁ c₁ c₂) (h₂ : reachesInQ machine oracle t₂ q₂ c₂ c₃) :
    reachesInQ machine oracle (t₁ + t₂) (q₁ + q₂) c₁ c₃ := by
  induction h₁ with
  | zero => simpa using h₂
  | @step cfg middle result time queries hs _ ih =>
    have := reachesInQ.step hs (ih h₂)
    have e1 : time + t₂ + 1 = time + 1 + t₂ := by omega
    rw [e1] at this
    convert this using 1
    omega

/-- Prepending a step from a non-query state does not change the query count. -/
theorem reachesInQ.local_step {n : ℕ} {machine : OracleTM n} {oracle : BooleanOracle}
    {t q : ℕ} {c m c' : OracleCfg n machine.Q}
    (hq : machine.queryTransition c.state = none) (hs : machine.step oracle c = some m)
    (h : reachesInQ machine oracle t q m c') : reachesInQ machine oracle (t + 1) q c c' := by
  have := reachesInQ.step hs h
  simpa [hq] using this

/-- Prepending a step from a query state adds one to the query count. -/
theorem reachesInQ.query_step {n : ℕ} {machine : OracleTM n} {oracle : BooleanOracle}
    {t q : ℕ} {c m c' : OracleCfg n machine.Q} {a b : machine.Q}
    (hq : machine.queryTransition c.state = some (a, b)) (hs : machine.step oracle c = some m)
    (h : reachesInQ machine oracle t q m c') : reachesInQ machine oracle (t + 1) (q + 1) c c' := by
  have := reachesInQ.step hs h
  simpa [hq] using this

/-- Polynomial-time Turing reduction making at most one oracle query in the whole run. -/
def OneQueryReducesPoly (L L' : Language) : Prop :=
  ∃ (k d : ℕ) (machine : OracleTM k) (T : ℕ → ℕ), T =O (· ^ d) ∧
    ∀ oracle : BooleanOracle, oracle.Decides L' →
      ∀ x, ∃ cfg time queries, time ≤ T x.length ∧ queries ≤ 1 ∧
        reachesInQ machine oracle time queries (machine.initCfg x) cfg ∧ machine.halted cfg ∧
        (x ∈ L → cfg.output.cells 1 = Γ.one) ∧ (x ∉ L → cfg.output.cells 1 = Γ.zero)

/-! ### The negating one-query machine -/

namespace NegQuery

/-- Control phases of `negQueryTM` after the simulated FP machine has halted. -/
inductive Phase where
  | rewind | scan | ask | yes | no | done
  deriving DecidableEq

instance : Fintype Phase where
  elems := {.rewind, .scan, .ask, .yes, .no, .done}
  complete := fun x => by cases x <;> simp

variable {k : ℕ}

/-- Content-preserving idle local transition. -/
def idleLocal {Q : Type} (next : Q) (iH qH : Γ) (wH : Fin k → Γ) (oH : Γ) :
    OracleLocalTransition k Q where
  nextState := next
  queryWrite := TM.readBackWrite qH
  workWrites := fun i => TM.readBackWrite (wH i)
  outputWrite := TM.readBackWrite oH
  inputDir := TM.idleDir iH
  queryDir := TM.idleDir qH
  workDirs := fun i => TM.idleDir (wH i)
  outputDir := TM.idleDir oH

/-- Simulate `M.δ`, with `M`'s output actions redirected to the query tape and the real output
tape idled. -/
def simLocal (M : TM k) (q : M.Q) (iH qH : Γ) (wH : Fin k → Γ) (oH : Γ) :
    OracleLocalTransition k (M.Q ⊕ Phase) :=
  let r := M.δ q iH wH qH
  { nextState := Sum.inl r.1
    queryWrite := r.2.2.1
    workWrites := r.2.1
    outputWrite := TM.readBackWrite oH
    inputDir := r.2.2.2.1
    queryDir := r.2.2.2.2.2
    workDirs := r.2.2.2.2.1
    outputDir := TM.idleDir oH }

/-- Local transition of `negQueryTM M`. -/
def localTransition (M : TM k) :
    M.Q ⊕ Phase → Γ → Γ → (Fin k → Γ) → Γ → OracleLocalTransition k (M.Q ⊕ Phase)
  | Sum.inl q, iH, qH, wH, oH =>
      if q = M.qhalt then idleLocal (Sum.inr .rewind) iH qH wH oH
      else simLocal M q iH qH wH oH
  | Sum.inr .rewind, iH, qH, wH, oH =>
      if qH = Γ.start then { idleLocal (Sum.inr .scan) iH qH wH oH with queryDir := Dir3.right }
      else { idleLocal (Sum.inr .rewind) iH qH wH oH with queryDir := Dir3.left }
  | Sum.inr .scan, iH, qH, wH, oH =>
      if qH = Γ.blank then idleLocal (Sum.inr .ask) iH qH wH oH
      else { idleLocal (Sum.inr .scan) iH qH wH oH with queryDir := Dir3.right }
  | Sum.inr .ask, iH, qH, wH, oH => idleLocal (Sum.inr .ask) iH qH wH oH
  | Sum.inr .yes, iH, qH, wH, oH =>
      { idleLocal (Sum.inr .done) iH qH wH oH with outputWrite := Γw.zero }
  | Sum.inr .no, iH, qH, wH, oH =>
      { idleLocal (Sum.inr .done) iH qH wH oH with outputWrite := Γw.one }
  | Sum.inr .done, iH, qH, wH, oH => idleLocal (Sum.inr .done) iH qH wH oH

/-- Query transition of `negQueryTM M`: only the `ask` phase queries. -/
def queryTransition (M : TM k) : M.Q ⊕ Phase → Option ((M.Q ⊕ Phase) × (M.Q ⊕ Phase))
  | Sum.inr .ask => some (Sum.inr .yes, Sum.inr .no)
  | _ => none

/-- `idleLocal` moves every head that reads the start marker `▷` to the right. -/
theorem idleLocal_right {Q : Type} (next : Q) (iH qH : Γ) (wH : Fin k → Γ) (oH : Γ) :
    (iH = Γ.start → (idleLocal next iH qH wH oH).inputDir = Dir3.right) ∧
    (qH = Γ.start → (idleLocal next iH qH wH oH).queryDir = Dir3.right) ∧
    (∀ i, wH i = Γ.start → (idleLocal next iH qH wH oH).workDirs i = Dir3.right) ∧
    (oH = Γ.start → (idleLocal next iH qH wH oH).outputDir = Dir3.right) :=
  ⟨TM.idleDir_right_of_start, TM.idleDir_right_of_start,
    fun _ => TM.idleDir_right_of_start, TM.idleDir_right_of_start⟩

end NegQuery

open NegQuery in
/-- The negating one-query oracle machine built from an FP machine `M : TM k` (same `k` work
tapes).  On input `x` it runs through the following phases:

1. **simulate** (`Sum.inl q`): run `M` step by step with `M`'s output tape played by the query
   tape (reads, writes and moves of `M`'s output head go to the query head); the real output
   tape and nothing else is touched.  When `M` computes `f x`, the query tape ends up holding
   `f x` (followed by a blank) in cells `1, 2, …`;
2. on reaching `M.qhalt`, do one idle step and enter **rewind**: move the query head left until
   it reads the start marker `▷` in cell `0`, then step right to cell `1`;
3. **scan**: move the query head right to the first blank cell, which is cell `|f x| + 1`, so the
   query `Tape.oracleQuery` read by the oracle is exactly `f x`;
4. **ask**: the unique query state; the oracle answers and moves to `yes` or `no`;
5. **answer**: write the negated answer (`0` after `yes`, `1` after `no`) in output cell `1`
   and halt in `done`. -/
def negQueryTM {k : ℕ} (M : TM k) : OracleTM k where
  Q := M.Q ⊕ Phase
  qstart := Sum.inl M.qstart
  qhalt := Sum.inr .done
  queryTransition := NegQuery.queryTransition M
  localTransition := NegQuery.localTransition M
  localTransition_right_of_start := by
    intro q iH qH wH oH
    rcases q with q | ph
    · by_cases hq : q = M.qhalt
      · simp only [NegQuery.localTransition, hq, ite_true]
        exact idleLocal_right _ iH qH wH oH
      · simp only [NegQuery.localTransition, hq, ite_false, simLocal]
        have h := M.δ_right_of_start q iH wH qH
        generalize M.δ q iH wH qH = r at h ⊢
        obtain ⟨q', wW, oW, iD, wD, oD⟩ := r
        exact ⟨h.1, h.2.2, h.2.1, TM.idleDir_right_of_start⟩
    · have hi := idleLocal_right (k := k) (Q := M.Q ⊕ Phase)
      cases ph with
      | rewind =>
        simp only [NegQuery.localTransition]
        split
        · have h := hi (Sum.inr .scan) iH qH wH oH
          exact ⟨h.1, fun _ => rfl, h.2.2.1, h.2.2.2⟩
        · next hne =>
          have h := hi (Sum.inr .rewind) iH qH wH oH
          exact ⟨h.1, fun h' => absurd h' hne, h.2.2.1, h.2.2.2⟩
      | scan =>
        simp only [NegQuery.localTransition]
        split
        · exact hi _ iH qH wH oH
        · have h := hi (Sum.inr .scan) iH qH wH oH
          exact ⟨h.1, fun _ => rfl, h.2.2.1, h.2.2.2⟩
      | ask => exact hi _ iH qH wH oH
      | yes =>
        have h := hi (Sum.inr .done) iH qH wH oH
        exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
      | no =>
        have h := hi (Sum.inr .done) iH qH wH oH
        exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
      | done => exact hi _ iH qH wH oH

namespace NegQuery

variable {k : ℕ}

/-! #### Phase 1: simulation -/

/-- The configuration of `negQueryTM M` simulating the configuration `c` of `M`, with real output
tape `out`. -/
def simCfg (M : TM k) (out : Tape) (c : Cfg k M.Q) : OracleCfg k (negQueryTM M).Q where
  state := Sum.inl c.state
  input := c.input
  query := c.output
  work := c.work
  output := out

private theorem idle_out (out : Tape) (hc : out.cells = (Tape.init []).cells) (hh : out.head ≤ 1) :
    out.writeAndMove (TM.readBackWrite out.read).toΓ (TM.idleDir out.read) = TM.parkedBlank := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hh with h0 | h1
  · have hw : out = Tape.init [] := by
      calc out = ⟨out.head, out.cells⟩ := rfl
        _ = Tape.init [] := by rw [h0, hc]; rfl
    subst hw
    rfl
  · have hns : ∀ j, j ≥ 1 → out.cells j ≠ Γ.start := by
      intro j hj; rw [hc]; exact Tape.init_nil_cells_ne_start j hj
    rw [TM.tape_writeAndMove_stable out (by omega) hns]
    show out = (Tape.init []).move Dir3.right
    calc out = ⟨out.head, out.cells⟩ := rfl
      _ = (Tape.init []).move Dir3.right := by rw [h1, hc]; rfl

private theorem sim_step (M : TM k) (oracle : BooleanOracle) {c c' : Cfg k M.Q} (out : Tape)
    (hc : out.cells = (Tape.init []).cells) (hh : out.head ≤ 1)
    (hstep : M.step c = some c') :
    (negQueryTM M).step oracle (simCfg M out c) = some (simCfg M TM.parkedBlank c') := by
  have hne : c.state ≠ M.qhalt := TM.state_ne_qhalt_of_step hstep
  simp only [TM.step, hne, ite_false, Option.some.injEq] at hstep
  subst hstep
  have hout := idle_out out hc hh
  simp only [OracleTM.step, negQueryTM, simCfg, NegQuery.queryTransition,
    NegQuery.localTransition, hne, ite_false, simLocal, reduceCtorEq]
  rw [hout]

private theorem sim_reachesInQ (M : TM k) (oracle : BooleanOracle) {t : ℕ} {c c' : Cfg k M.Q}
    (h : M.reachesIn t c c') (out : Tape)
    (hc : out.cells = (Tape.init []).cells) (hh : out.head ≤ 1) :
    ∃ out', out'.cells = (Tape.init []).cells ∧ out'.head ≤ 1 ∧
      reachesInQ (negQueryTM M) oracle t 0 (simCfg M out c) (simCfg M out' c') := by
  induction h generalizing out with
  | zero => exact ⟨out, hc, hh, .zero⟩
  | step hs _ ih =>
    obtain ⟨out', hc', hh', hr⟩ := ih TM.parkedBlank rfl le_rfl
    exact ⟨out', hc', hh', reachesInQ.local_step rfl (sim_step M oracle out hc hh hs) hr⟩

/-! #### Transition at the simulated halt -/

private theorem halt_step (M : TM k) (oracle : BooleanOracle) (c : Cfg k M.Q)
    (hhalt : c.state = M.qhalt) (out : Tape)
    (hc : out.cells = (Tape.init []).cells) (hh : out.head ≤ 1) :
    ∃ cfg', (negQueryTM M).step oracle (simCfg M out c) = some cfg' ∧
      cfg'.state = Sum.inr .rewind ∧
      cfg'.query = TM.transitionTape c.output ∧
      cfg'.output = TM.parkedBlank := by
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · simp [negQueryTM, simCfg, NegQuery.localTransition, hhalt, idleLocal]
  · simp [negQueryTM, simCfg, NegQuery.localTransition, hhalt, idleLocal, TM.transitionTape]
  · have hout := idle_out out hc hh
    simp only [negQueryTM, simCfg, NegQuery.localTransition, hhalt, ite_true, idleLocal]
    exact hout

/-! #### Rewind loop on the query tape -/

private theorem parkedBlank_idle :
    TM.parkedBlank.writeAndMove (TM.readBackWrite TM.parkedBlank.read).toΓ
      (TM.idleDir TM.parkedBlank.read) = TM.parkedBlank :=
  idle_out _ rfl (by simp [TM.parkedBlank, Tape.move])

private theorem rewind_loop (M : TM k) (oracle : BooleanOracle) :
    ∀ (p : ℕ) (cfg : OracleCfg k (negQueryTM M).Q),
      cfg.state = Sum.inr .rewind → cfg.query.StartInvariant → cfg.query.head = p →
      cfg.output = TM.parkedBlank →
      ∃ cfg', reachesInQ (negQueryTM M) oracle (p + 1) 0 cfg cfg' ∧
        cfg'.state = Sum.inr .scan ∧ cfg'.query.head = 1 ∧
        cfg'.query.cells = cfg.query.cells ∧ cfg'.output = TM.parkedBlank := by
  intro p
  induction p with
  | zero =>
    intro cfg hs hinv hp hout
    have hread : cfg.query.read = Γ.start := by simp [Tape.read, hp, hinv.1]
    set nxt : OracleCfg k (negQueryTM M).Q :=
      { state := Sum.inr .scan, input := cfg.input.move (TM.idleDir cfg.input.read),
        query := cfg.query.move Dir3.right,
        work := fun i => (cfg.work i).writeAndMove (TM.readBackWrite (cfg.work i).read)
          (TM.idleDir (cfg.work i).read),
        output := TM.parkedBlank } with hnxt
    have hstep : (negQueryTM M).step oracle cfg = some nxt := by
      simp only [OracleTM.step, negQueryTM, NegQuery.queryTransition,
        NegQuery.localTransition, hs, hread, ite_true, idleLocal, hnxt]
      rw [hout, parkedBlank_idle]
      simp [Tape.writeAndMove, Tape.write, hp]
    refine ⟨nxt, reachesInQ.local_step (by rw [hs]; rfl) hstep .zero, rfl, ?_, ?_, rfl⟩
    · simp [hnxt, Tape.move, hp]
    · simp [hnxt, Tape.move_cells]
  | succ p ih =>
    intro cfg hs hinv hp hout
    have hread : cfg.query.read ≠ Γ.start := hinv.read_ne_start (by omega)
    set nxt : OracleCfg k (negQueryTM M).Q :=
      { state := Sum.inr .rewind, input := cfg.input.move (TM.idleDir cfg.input.read),
        query := cfg.query.move Dir3.left,
        work := fun i => (cfg.work i).writeAndMove (TM.readBackWrite (cfg.work i).read)
          (TM.idleDir (cfg.work i).read),
        output := TM.parkedBlank } with hnxt
    have hstep : (negQueryTM M).step oracle cfg = some nxt := by
      simp only [OracleTM.step, negQueryTM, NegQuery.queryTransition,
        NegQuery.localTransition, hs, hread, ite_false, idleLocal, hnxt]
      rw [hout, parkedBlank_idle, TM.writeAndMove_readBack _ hread]
      simp
    have hinv' : nxt.query.StartInvariant := by
      show (cfg.query.move Dir3.left).StartInvariant
      exact hinv.move _
    obtain ⟨cfg', hr, hs', hh', hc', ho'⟩ :=
      ih nxt rfl hinv' (by simp [hnxt, Tape.move, hp]) rfl
    exact ⟨cfg', reachesInQ.local_step (by rw [hs]; rfl) hstep hr, hs', hh',
      by rw [hc']; simp [hnxt, Tape.move_cells], ho'⟩

/-! #### Scan loop on the query tape -/

private theorem scan_loop (M : TM k) (oracle : BooleanOracle) :
    ∀ (bits : List Bool) (cfg : OracleCfg k (negQueryTM M).Q),
      cfg.state = Sum.inr .scan → cfg.query.HasBinarySuffix bits →
      cfg.output = TM.parkedBlank →
      ∃ cfg', reachesInQ (negQueryTM M) oracle (bits.length + 1) 0 cfg cfg' ∧
        cfg'.state = Sum.inr .ask ∧ cfg'.query.head = cfg.query.head + bits.length ∧
        cfg'.query.cells = cfg.query.cells ∧ cfg'.output = TM.parkedBlank := by
  intro bits
  induction bits with
  | nil =>
    intro cfg hs hsuf hout
    have hread : cfg.query.read = Γ.blank := hsuf.read_nil
    have hns : cfg.query.read ≠ Γ.start := hsuf.read_ne_start
    set nxt : OracleCfg k (negQueryTM M).Q :=
      { state := Sum.inr .ask, input := cfg.input.move (TM.idleDir cfg.input.read),
        query := cfg.query,
        work := fun i => (cfg.work i).writeAndMove (TM.readBackWrite (cfg.work i).read)
          (TM.idleDir (cfg.work i).read),
        output := TM.parkedBlank } with hnxt
    have hstep : (negQueryTM M).step oracle cfg = some nxt := by
      have hq : cfg.query.writeAndMove (TM.readBackWrite Γ.blank).toΓ (TM.idleDir Γ.blank)
          = cfg.query := by
        rw [← hread, TM.writeAndMove_readBack _ hns, hread]; rfl
      simp only [OracleTM.step, negQueryTM, NegQuery.queryTransition,
        NegQuery.localTransition, hs, hread, ite_true, idleLocal, hnxt, hout]
      rw [hq, parkedBlank_idle]
      simp
    exact ⟨nxt, reachesInQ.local_step (by rw [hs]; rfl) hstep .zero, rfl, by simp [hnxt],
      rfl, rfl⟩
  | cons b bs ih =>
    intro cfg hs hsuf hout
    have hread : cfg.query.read = Γ.ofBool b := hsuf.read_cons
    have hnb : cfg.query.read ≠ Γ.blank := by rw [hread]; exact Γ.ofBool_ne_blank b
    have hns : cfg.query.read ≠ Γ.start := hsuf.read_ne_start
    set nxt : OracleCfg k (negQueryTM M).Q :=
      { state := Sum.inr .scan, input := cfg.input.move (TM.idleDir cfg.input.read),
        query := cfg.query.move Dir3.right,
        work := fun i => (cfg.work i).writeAndMove (TM.readBackWrite (cfg.work i).read)
          (TM.idleDir (cfg.work i).read),
        output := TM.parkedBlank } with hnxt
    have hstep : (negQueryTM M).step oracle cfg = some nxt := by
      simp only [OracleTM.step, negQueryTM, NegQuery.queryTransition,
        NegQuery.localTransition, hs, hnb, ite_false, idleLocal, hnxt]
      rw [hout, parkedBlank_idle, TM.writeAndMove_readBack _ hns]
      simp
    obtain ⟨cfg', hr, hs', hh', hc', ho'⟩ := ih nxt rfl hsuf.move_right_cons rfl
    refine ⟨cfg', ?_, hs', ?_, ?_, ho'⟩
    · have := reachesInQ.local_step (by rw [hs]; rfl) hstep hr
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
    · rw [hh']; simp [hnxt, Tape.move]; omega
    · rw [hc']; simp [hnxt, Tape.move_cells]

/-! #### Reading the query back -/

private theorem oracleQuery_eq_of_cells (t : Tape) (y : List Bool) (hhead : t.head = y.length + 1)
    (hcells : ∀ i (h : i < y.length), t.cells (i + 1) = Γ.ofBool (y[i]'h)) :
    t.oracleQuery = y := by
  apply List.ext_getElem
  · simp [hhead]
  · intro i h1 h2
    simp only [Tape.oracleQuery, List.getElem_ofFn]
    rw [hcells i h2]
    cases y[i] <;> rfl

/-! #### Answer phase -/

/-- A non-halted, non-query oracle step is the local transition. -/
private theorem oracleStep_of_local {n : ℕ} {machine : OracleTM n} {oracle : BooleanOracle}
    {cfg : OracleCfg n machine.Q}
    (hh : cfg.state ≠ machine.qhalt) (hq : machine.queryTransition cfg.state = none) :
    machine.step oracle cfg =
      some (let tr := machine.localTransition cfg.state cfg.input.read cfg.query.read
              (fun i => (cfg.work i).read) cfg.output.read
            { state := tr.nextState
              input := cfg.input.move tr.inputDir
              query := cfg.query.writeAndMove tr.queryWrite tr.queryDir
              work := fun i => (cfg.work i).writeAndMove (tr.workWrites i) (tr.workDirs i)
              output := cfg.output.writeAndMove tr.outputWrite tr.outputDir }) := by
  simp [OracleTM.step, hh, hq]

private theorem answer_step (M : TM k) (oracle : BooleanOracle)
    (cfg : OracleCfg k (negQueryTM M).Q)
    (b : Bool) (hs : cfg.state = (if b then Sum.inr .yes else Sum.inr .no))
    (hout : cfg.output = TM.parkedBlank) :
    ∃ cfg', (negQueryTM M).step oracle cfg = some cfg' ∧ cfg'.state = Sum.inr .done ∧
      cfg'.output.cells 1 = Γ.ofBool (!b) := by
  have hh : cfg.state ≠ (negQueryTM M).qhalt := by
    rw [hs]; cases b <;> simp [negQueryTM]
  have hq : (negQueryTM M).queryTransition cfg.state = none := by
    rw [hs]; cases b <;> rfl
  rw [oracleStep_of_local hh hq]
  refine ⟨_, rfl, ?_, ?_⟩
  · rw [hs]; cases b <;> rfl
  · rw [hs, hout]
    cases b <;> simp [negQueryTM, NegQuery.localTransition, idleLocal, Tape.writeAndMove,
      Tape.write, Tape.move, TM.parkedBlank, Tape.read, TM.idleDir, Γ.ofBool]

end NegQuery

open NegQuery in
/-- Main run lemma for `negQueryTM`: if `M` computes `f` in time `T`, then for every oracle and
input `x` the machine halts within `3 T(|x|) + 6` steps after **exactly one** query and leaves the
negated oracle answer on `f x` in output cell `1`. -/
theorem negQueryTM_run {k : ℕ} (M : TM k) {f : List Bool → List Bool} {T : ℕ → ℕ}
    (hM : M.ComputesInTime f T) (oracle : BooleanOracle) (x : List Bool) :
    ∃ cfg time, time ≤ 3 * T x.length + 6 ∧
      reachesInQ (negQueryTM M) oracle time 1 ((negQueryTM M).initCfg x) cfg ∧
      (negQueryTM M).halted cfg ∧
      cfg.output.cells 1 = Γ.ofBool (!oracle (f x)) := by
  obtain ⟨c', t, ht, hreach, hhalt, hout⟩ := hM x
  have hlen : (f x).length ≤ T x.length := hM.output_length_le x
  have hhead : c'.output.head ≤ t := (TM.head_le_of_reachesIn M hreach).2.1
  have hinv : c'.output.StartInvariant :=
    (TM.reachesIn_startInvariant hreach (Tape.StartInvariant.init_ofBool x)
      (fun _ => Tape.StartInvariant.init_nil) Tape.StartInvariant.init_nil).2.2
  -- phase 1: simulation
  obtain ⟨out₁, hc₁, hh₁, hr₁⟩ := sim_reachesInQ M oracle hreach (Tape.init []) rfl (by simp)
  -- transition at simulated halt
  obtain ⟨cfg₁, hs₁, hst₁, hq₁, ho₁⟩ := halt_step M oracle c' hhalt out₁ hc₁ hh₁
  have hq₁cells : cfg₁.query.cells = c'.output.cells := by
    rw [hq₁]; exact TM.transitionTape_cells _ hinv.2
  have hq₁head : cfg₁.query.head ≤ t + 1 := by
    rw [hq₁]; exact TM.head_transitionTape_le hinv.1 hhead
  have hq₁inv : cfg₁.query.StartInvariant := by
    refine ⟨?_, fun j hj => ?_⟩ <;> rw [hq₁cells]
    · exact hinv.1
    · exact hinv.2 j hj
  -- phase 2: rewind
  obtain ⟨cfg₂, hr₂, hst₂, hh₂, hc₂, ho₂⟩ :=
    rewind_loop M oracle cfg₁.query.head cfg₁ hst₁ hq₁inv rfl ho₁
  have hc₂' : cfg₂.query.cells = c'.output.cells := hc₂.trans hq₁cells
  have hout₂ : cfg₂.query.HasOutput (f x) := (Tape.hasOutput_congr hc₂' (f x)).mpr hout
  have hinv₂ : cfg₂.query.StartInvariant := by
    refine ⟨?_, fun j hj => ?_⟩ <;> rw [hc₂']
    · exact hinv.1
    · exact hinv.2 j hj
  -- phase 3: scan
  obtain ⟨cfg₃, hr₃, hst₃, hh₃, hc₃, ho₃⟩ :=
    scan_loop M oracle (f x) cfg₂ hst₂ (hout₂.hasBinarySuffix hh₂ hinv₂) ho₂
  have hquery : cfg₃.query.oracleQuery = f x := by
    apply oracleQuery_eq_of_cells
    · rw [hh₃, hh₂]; omega
    · intro i hi; rw [hc₃]; exact hout₂.1 i hi
  -- phase 4: the single query
  have hqt : (negQueryTM M).queryTransition cfg₃.state = some (Sum.inr .yes, Sum.inr .no) := by
    rw [hst₃]; rfl
  have hnh : cfg₃.state ≠ (negQueryTM M).qhalt := by rw [hst₃]; simp [negQueryTM]
  have hans : oracle cfg₃.query.oracleQuery = oracle (f x) := by rw [hquery]
  generalize hb : oracle (f x) = b at hans ⊢
  -- phase 5: write the negated answer
  have hr₄₅ : ∃ cfg₅, reachesInQ (negQueryTM M) oracle 2 1 cfg₃ cfg₅ ∧
      cfg₅.state = Sum.inr .done ∧ cfg₅.output.cells 1 = Γ.ofBool (!b) := by
    cases b
    · have hs₄ := OracleTM.step_query_false (oracle := oracle) hnh hqt hans
      obtain ⟨cfg₅, hs₅, hst₅, hcell₅⟩ :=
        answer_step M oracle { cfg₃ with state := Sum.inr .no } false rfl ho₃
      exact ⟨cfg₅, reachesInQ.query_step hqt hs₄ (reachesInQ.local_step rfl hs₅ .zero),
        hst₅, hcell₅⟩
    · have hs₄ := OracleTM.step_query_true (oracle := oracle) hnh hqt hans
      obtain ⟨cfg₅, hs₅, hst₅, hcell₅⟩ :=
        answer_step M oracle { cfg₃ with state := Sum.inr .yes } true rfl ho₃
      exact ⟨cfg₅, reachesInQ.query_step hqt hs₄ (reachesInQ.local_step rfl hs₅ .zero),
        hst₅, hcell₅⟩
  obtain ⟨cfg₅, hr₄₅, hst₅, hcell₅⟩ := hr₄₅
  have hr₀₁ : reachesInQ (negQueryTM M) oracle 1 0 (simCfg M out₁ c') cfg₁ :=
    reachesInQ.local_step rfl hs₁ .zero
  have hall := ((((hr₁.trans hr₀₁).trans hr₂).trans hr₃).trans hr₄₅)
  refine ⟨cfg₅, _, ?_, hall, hst₅, hcell₅⟩
  omega

/-- The negating one-query machine: for every oracle and input it halts in polynomial time after
exactly one query and outputs the negation of the oracle's answer on `f x`. -/
theorem exists_negQuery_machine {f : List Bool → List Bool} (hf : f ∈ FP) :
    ∃ (k d : ℕ) (machine : OracleTM k) (T : ℕ → ℕ), T =O (· ^ d) ∧
      ∀ (oracle : BooleanOracle) (x : List Bool), ∃ cfg time, time ≤ T x.length ∧
        reachesInQ machine oracle time 1 (machine.initCfg x) cfg ∧ machine.halted cfg ∧
        cfg.output.cells 1 = Γ.ofBool (!oracle (f x)) := by
  obtain ⟨d, k, M, T, hM, hT⟩ := hf
  exact ⟨k, d, negQueryTM M, fun m => 3 * T m + 6,
    BigO.add (BigO.const_mul_left 3 hT) (BigO.const_le_pow 6 d),
    fun oracle x => negQueryTM_run M hM oracle x⟩

/-- An FP map `f` with `x ∈ L ↔ f x ∉ L'` gives a polynomial-time one-query reduction from `L`
to `L'`. -/
theorem oneQueryReducesPoly_of_neg {L L' : Language} {f : List Bool → List Bool} (hf : f ∈ FP)
    (hred : ∀ x, x ∈ L ↔ f x ∉ L') : OneQueryReducesPoly L L' := by
  obtain ⟨k, d, machine, T, hT, hrun⟩ := exists_negQuery_machine hf
  refine ⟨k, d, machine, T, hT, ?_⟩
  intro oracle horacle x
  obtain ⟨cfg, time, ht, hr, hh, hcell⟩ := hrun oracle x
  refine ⟨cfg, time, 1, ht, le_rfl, hr, hh, fun hx => ?_, fun hx => ?_⟩
  · have : oracle (f x) = false := by
      cases h : oracle (f x)
      · rfl
      · exact absurd ((horacle (f x)).mp h) ((hred x).mp hx)
    rw [hcell, this]; rfl
  · have : oracle (f x) = true := by
      cases h : oracle (f x)
      · exact absurd ((hred x).mpr (fun hm => by
          have := (horacle (f x)).mpr hm; rw [h] at this; exact Bool.false_ne_true this)) hx
      · rfl
    rw [hcell, this]; rfl

end SparseIrred
