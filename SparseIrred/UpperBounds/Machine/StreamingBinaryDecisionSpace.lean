import SparseIrred.UpperBounds.Machine.StreamingMachineLinear
import Complexitylib.Models.TuringMachine.Internal

/-! # Honest decision-space bounds for one-bit binary routines

The binary-routine library bounds every work/input head, while its transducer
contract makes the output head monotone. A terminating one-bit output therefore
bounds that head by two on every prefix, closing the decider-space obligation.
-/
namespace SparseIrred.UpperBounds.Machine
open Complexity BinaryRoutine

/-- One transducer step cannot move the output head backwards. -/
theorem transducer_output_head_step {k : ℕ} (tm : TM k) (ht : tm.IsTransducer)
    {c d : Cfg k tm.Q} (hs : tm.step c = some d) : c.output.head ≤ d.output.head := by
  have hne := TM.state_ne_qhalt_of_step hs
  simp only [TM.step, hne, ↓reduceIte] at hs
  rcases hδ : tm.δ c.state c.input.read (fun i ↦ (c.work i).read) c.output.read with
    ⟨q, writes, ow, idir, wdirs, odir⟩
  have hd : odir ≠ Dir3.left := by
    simpa only [hδ] using ht c.state c.input.read (fun i ↦ (c.work i).read) c.output.read
  simp only [hδ] at hs
  rw [← Option.some.inj hs]
  cases odir <;> by_cases hz : c.output.head = 0 <;>
    simp_all [Tape.writeAndMove, Tape.move, Tape.write]

/-- Output monotonicity holds along every actual machine execution. -/
theorem transducer_output_head_reaches {k : ℕ} (tm : TM k) (ht : tm.IsTransducer)
    {c d : Cfg k tm.Q} (h : tm.reaches c d) : c.output.head ≤ d.output.head := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hs _ ih => exact (transducer_output_head_step tm ht hs).trans ih

/-- Determinism and halting force every other finite reachable run to be a prefix. -/
theorem reachesIn_suffix_of_halted {k : ℕ} (tm : TM k) {t T : ℕ}
    {start mid finish : Cfg k tm.Q} (hp : tm.reachesIn t start mid)
    (hf : tm.reachesIn T start finish) (hh : tm.halted finish) : tm.reaches mid finish := by
  induction hp generalizing T finish with
  | zero => exact TM.reaches_of_reachesIn hf
  | @step a next n last hs hp ih =>
    cases hf with
    | zero => simp [TM.step, hh] at hs
    | @step a next' n' finish hs' hf =>
      have he : next = next' := Option.some.inj (hs.symm.trans hs')
      subst next'
      exact ih hf hh

theorem reaches_suffix_of_halted {k : ℕ} (tm : TM k) {T : ℕ}
    {start mid finish : Cfg k tm.Q} (hp : tm.reaches start mid)
    (hf : tm.reachesIn T start finish) (hh : tm.halted finish) : tm.reaches mid finish := by
  obtain ⟨t, ht⟩ := tm.reaches_to_reachesIn hp
  exact reachesIn_suffix_of_halted tm ht hf hh

/-- A terminating transducer with a bounded final output head has the same bound
on every reachable prefix, including executions described without a clock. -/
theorem transducer_output_head_le_final {k : ℕ} (tm : TM k) (ht : tm.IsTransducer)
    {T : ℕ} {start mid finish : Cfg k tm.Q} (hp : tm.reaches start mid)
    (hf : tm.reachesIn T start finish) (hh : tm.halted finish) :
    mid.output.head ≤ finish.output.head :=
  transducer_output_head_reaches tm ht (reaches_suffix_of_halted tm hp hf hh)

/-- Upgrade a time/auxiliary-space Hoare contract to honest decision space whenever
its terminal output head is bounded. -/
theorem hoareTimeSpace_decisionSpace {k : ℕ} (tm : TM k) (ht : tm.IsTransducer)
    {pre post : TapePred k} {time L S B : ℕ}
    (h : tm.HoareTimeSpace pre post time L S)
    (houtput : ∀ inp work out, post inp work out → out.head ≤ B + 1)
    (inp : Tape) (work : Fin k → Tape) (out : Tape) (hpre : pre inp work out) :
    (∀ d, tm.reaches { state := tm.qstart, input := inp, work := work, output := out } d →
      d.WithinDecisionSpace L (max S B)) ∧
    ∃ finish t, t ≤ time ∧
      tm.reachesIn t { state := tm.qstart, input := inp, work := work, output := out } finish ∧
      tm.halted finish ∧ post finish.input finish.work finish.output := by
  obtain ⟨finish, t, htime, hreach, hhalt, hpost⟩ := h.1 inp work out hpre
  refine ⟨?_, finish, t, htime, hreach, hhalt, hpost⟩
  intro d hd
  refine ⟨(h.2 inp work out hpre d hd).mono le_rfl (le_max_left _ _), ?_⟩
  have hhead := transducer_output_head_le_final tm ht hd hreach hhalt
  have hb := houtput _ _ _ hpost
  have := le_max_right S B
  omega

/-- A sound binary routine emitting at most one bit has a genuine decider-space
contract. The result includes exact final registers/output and a terminating run. -/
theorem binaryRoutine_oneBit_decisionSpace {k : ℕ} (R : BinaryRoutine k) (hs : R.Sound)
    (v : BinaryValues k) (inp out : Tape) (L S : ℕ)
    (hreq : R.requires v) (hpark : TM.Parked inp) (hS : 1 ≤ S)
    (hhead : inp.head ≤ L + S + 1) (hout : TM.OutAcc [] out)
    (hword : (R.emitted v).length ≤ 1) :
    (∀ d, R.machine.reaches
      { state := R.machine.qstart, input := inp, work := workTapes v, output := out } d →
      d.WithinDecisionSpace L (max (R.spaceBound S v) 1)) ∧
    ∃ finish t, t ≤ R.timeBound v ∧
      R.machine.reachesIn t
        { state := R.machine.qstart, input := inp, work := workTapes v, output := out } finish ∧
      R.machine.halted finish ∧
      CanonicalPred inp (R.effect v) (R.emitted v) finish.input finish.work finish.output := by
  have h := hs.hoareTimeSpace v inp [] L S hreq hpark hS hhead
  simp only [List.nil_append] at h
  apply hoareTimeSpace_decisionSpace R.machine hs.isTransducer h
  · intro inp' work' out' hp
    have hh := hp.2.2.head_eq
    omega
  · exact ⟨rfl, rfl, hout⟩

/-- In the singleton-output case, the termination certificate identifies the literal
verdict cell, while every reachable configuration obeys full decision space. -/
theorem binaryRoutine_bit_decisionSpace {k : ℕ} (R : BinaryRoutine k) (hs : R.Sound)
    (v : BinaryValues k) (inp out : Tape) (L S : ℕ) (b : Bool)
    (hreq : R.requires v) (hpark : TM.Parked inp) (hS : 1 ≤ S)
    (hhead : inp.head ≤ L + S + 1) (hout : TM.OutAcc [] out) (hword : R.emitted v = [b]) :
    (∀ d, R.machine.reaches
      { state := R.machine.qstart, input := inp, work := workTapes v, output := out } d →
      d.WithinDecisionSpace L (max (R.spaceBound S v) 1)) ∧
    ∃ finish t, t ≤ R.timeBound v ∧
      R.machine.reachesIn t
        { state := R.machine.qstart, input := inp, work := workTapes v, output := out } finish ∧
      R.machine.halted finish ∧ finish.output.cells 1 = Γ.ofBool b := by
  obtain ⟨hspace, finish, t, ht, hr, hh, hp⟩ := binaryRoutine_oneBit_decisionSpace R hs v inp out L S
    hreq hpark hS hhead hout (by simp [hword])
  refine ⟨hspace, finish, t, ht, hr, hh, ?_⟩
  have ho := hp.2.2
  rw [hword] at ho
  exact ho.2.2.1 0 (by simp)

end SparseIrred.UpperBounds.Machine
