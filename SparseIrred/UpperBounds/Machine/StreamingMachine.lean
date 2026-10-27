import Complexitylib.Classes.Containments.Internal.SpaceIterate

/-!
# A concrete deterministic machine for bounded-state enumeration

This module compiles a verified streaming trace into a deterministic multitape
machine. The trace may have exponentially many steps. The compiled machine
reuses its work tapes after each step, and its space theorem covers every
reachable configuration, including the subroutine executions between trace
states.
-/

namespace SparseIrred.UpperBounds.Machine

open Complexity
open Complexity.TM
open Complexity.SpaceIter

/-- A complete bounded-state trace, including the halt flag and final answer.
The first application initializes the state from `pair [] x`. -/
structure StreamingTrace (G : List Bool → List Bool) (answer : List Bool → Bool)
    (r w : Polynomial ℕ) where
  state : List Bool → ℕ → List Bool
  stop : List Bool → ℕ
  start : ∀ x, state x 0 = pair [] x
  step : ∀ x i, state x (i + 1) = G (state x i)
  length_le : ∀ x i, i ≤ stop x + 1 → (state x i).length ≤ r.eval x.length
  stop_pos : ∀ x, 1 ≤ stop x
  stop_le : ∀ x, stop x ≤ 2 ^ w.eval x.length
  running : ∀ x i, 0 < i → i < stop x → (state x i).headD false = false
  done : ∀ x, (state x (stop x)).headD false = true
  answer_nonempty : ∀ x, state x (stop x + 1) ≠ []
  answer_eq : ∀ x, (state x (stop x + 1)).headD false = answer x

/-- A padding polynomial supplies enough reusable space for one step and its
cleanup. Its degree is independent of the number of iterations. -/
noncomputable def streamingPadding (tp r : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.X + Polynomial.C 4 + r + Polynomial.C 1 + tp.comp r + Polynomial.C 1

theorem streamingPadding_eval (tp r : Polynomial ℕ) (n : ℕ) :
    (streamingPadding tp r).eval n = n + 4 + r.eval n + 1 + tp.eval (r.eval n) + 1 := by
  simp [streamingPadding, Polynomial.eval_comp]

/-- The actual machine consists of a reusable application machine, a binary
iteration counter, a completion test, and a one-bit output epilogue. -/
noncomputable def streamingIterationMachine {k : ℕ} (M : TM k) (tp r : Polynomial ℕ) :
    TM (3 + (k + 2) + 0) :=
  spaceIterTM M (streamingPadding tp r)

private theorem streamingTrace_bounds {G : List Bool → List Bool}
    {answer : List Bool → Bool} {r w : Polynomial ℕ}
    (trace : StreamingTrace G answer r w) (k : ℕ) (tp : Polynomial ℕ) (x : List Bool) :
    (∀ i, i ≤ trace.stop x + 1 →
      (trace.state x i).length + 1 ≤ (streamingPadding tp r).eval x.length) ∧
    (∀ i, i ≤ trace.stop x →
      1 + tp.eval (trace.state x i).length ≤ (streamingPadding tp r).eval x.length) ∧
    (∀ j, j ≤ trace.stop x →
      1 + 1 + (tp.eval (trace.state x j).length + 1 +
        tailBound k ((streamingPadding tp r).eval x.length)
          (trace.state x (j + 1)).length) + 1 +
        binarySuccTime (startCount x.length + j) + 1 + 5 ≤
        passBound k tp (streamingPadding tp r) r w x.length) := by
  have hmono : ∀ i, i ≤ trace.stop x + 1 →
      tp.eval (trace.state x i).length ≤ tp.eval (r.eval x.length) := fun i hi ↦
    polynomial_eval_mono_nat tp (trace.length_le x i hi)
  refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_, fun j hj ↦ ?_⟩
  · have := trace.length_le x i hi
    rw [streamingPadding_eval]
    omega
  · have := hmono i (by omega)
    rw [streamingPadding_eval]
    omega
  · have h1 := hmono j (by omega)
    have h2 := tailBound_mono k ((streamingPadding tp r).eval x.length)
      (trace.length_le x (j + 1) (by omega))
    have h3 : binarySuccTime (startCount x.length + j) ≤
        2 * (x.length + w.eval x.length + 1) + 2 := by
      have h4 := binarySuccTime_le (startCount x.length + j)
      have h5 := startCount_add_size_le x.length j (w.eval x.length)
        (le_trans hj (trace.stop_le x))
      omega
    rw [passBound]
    omega

/-- Every configuration of the complete deterministic machine stays in the
same polynomial window; the exponential number of passes does not accumulate
work tapes or intermediate results. -/
theorem streamingIterationMachine_allPrefixes {k : ℕ} (M : TM k)
    {G : List Bool → List Bool} {answer : List Bool → Bool} (tp r w : Polynomial ℕ)
    (hM : M.ComputesInTime G (fun n ↦ tp.eval n)) (trace : StreamingTrace G answer r w)
    (x : List Bool) (c : Cfg (3 + (k + 2) + 0) (streamingIterationMachine M tp r).Q)
    (hreach : (streamingIterationMachine M tp r).reaches
      ((streamingIterationMachine M tp r).initCfg x) c) :
    c.WithinDecisionSpace x.length
      (windowBound k tp (streamingPadding tp r) r w x.length) := by
  obtain ⟨hHy, hHT, hb⟩ := streamingTrace_bounds trace k tp x
  exact spaceIterTM_keepsWindow M hM (streamingPadding tp r) x
    ((streamingPadding tp r).eval x.length) rfl
    (by rw [streamingPadding_eval]; omega) (trace.state x) (trace.start x)
    (trace.step x) (trace.stop x) (trace.stop_pos x) hHy hHT (trace.running x)
    (trace.done x) (passBound k tp (streamingPadding tp r) r w x.length) hb
    (windowBound k tp (streamingPadding tp r) r w x.length) le_rfl c hreach

/-- The actual machine halts and publishes exactly the trace's answer. -/
theorem streamingIterationMachine_halts {k : ℕ} (M : TM k)
    {G : List Bool → List Bool} {answer : List Bool → Bool} (tp r w : Polynomial ℕ)
    (hM : M.ComputesInTime G (fun n ↦ tp.eval n)) (trace : StreamingTrace G answer r w)
    (x : List Bool) :
    ∃ c, (streamingIterationMachine M tp r).reaches
      ((streamingIterationMachine M tp r).initCfg x) c ∧
      (streamingIterationMachine M tp r).halted c ∧
      c.output.cells 1 = Γ.ofBool (answer x) := by
  obtain ⟨hHy, hHT, hb⟩ := streamingTrace_bounds trace k tp x
  obtain ⟨c, t, -, hreach, hhalt, hpost⟩ :=
    spaceIterTM_hoareTime M hM (streamingPadding tp r) x
      ((streamingPadding tp r).eval x.length) rfl
      (by rw [streamingPadding_eval]; omega) (trace.state x) (trace.start x)
      (trace.step x) (trace.stop x) (trace.stop_pos x) hHy hHT (trace.running x)
      (trace.done x) (passBound k tp (streamingPadding tp r) r w x.length) hb
      (Tape.init (x.map Γ.ofBool)) (fun _ ↦ Tape.init []) (Tape.init []) ⟨rfl, rfl, rfl⟩
  refine ⟨c, reaches_of_reachesIn hreach, hhalt, ?_⟩
  rw [hpost, slotOf_cells_one]
  have hne := trace.answer_nonempty x
  have hans := trace.answer_eq x
  cases hs : trace.state x (trace.stop x + 1) with
  | nil => exact (hne hs).elim
  | cons b bs =>
    simp only [hs, List.headD_cons] at hans
    cases b <;> simp [headSym, ← hans, readBackWrite, Γ.ofBool, Γw.toΓ]

/-- Instantiate the deterministic machine from an internally proved
polynomial-time step implementation. This theorem is a construction, not an
implementation certificate left as a premise of a final result. -/
theorem streamingMachine_exists {G : List Bool → List Bool}
    {answer : List Bool → Bool} {r w : Polynomial ℕ} (hG : G ∈ FP)
    (trace : StreamingTrace G answer r w) :
    ∃ (k : ℕ) (M : TM k) (q : Polynomial ℕ),
      (∀ x c, M.reaches (M.initCfg x) c →
        c.WithinDecisionSpace x.length (q.eval x.length)) ∧
      (∀ x, ∃ c, M.reaches (M.initCfg x) c ∧ M.halted c ∧
        c.output.cells 1 = Γ.ofBool (answer x)) := by
  obtain ⟨k, M, tp, hM⟩ := mem_FP_iff_computesInTime_polynomial.mp hG
  obtain ⟨q, hq⟩ := polyBound_windowBound k tp (streamingPadding tp r) r w
  refine ⟨_, streamingIterationMachine M tp r, q, ?_,
    streamingIterationMachine_halts M tp r w hM trace⟩
  intro x c hc
  have hb := streamingIterationMachine_allPrefixes M tp r w hM trace x c hc
  have hle := hq x.length
  exact ⟨⟨fun i ↦ (hb.1.1 i).trans hle, by have := hb.1.2; omega⟩,
    by have := hb.2; omega⟩

/-- The language decided by the constructed streaming machine is in PSPACE. -/
theorem streamingLanguage_mem_PSPACE {L : Language} {G : List Bool → List Bool}
    {answer : List Bool → Bool} {r w : Polynomial ℕ} (hG : G ∈ FP)
    (trace : StreamingTrace G answer r w) (hans : ∀ x, x ∈ L ↔ answer x = true) :
    L ∈ PSPACE := by
  obtain ⟨k, M, q, hwindow, hhalt⟩ := streamingMachine_exists hG trace
  refine mem_PSPACE_of_polyWindow M q hwindow (fun x ↦ ?_)
  obtain ⟨c, hreach, hhalted, hout⟩ := hhalt x
  refine ⟨c, hreach, hhalted, fun hx ↦ ?_, fun hx ↦ ?_⟩
  · rw [hout, (hans x).mp hx]; rfl
  · have hb : answer x = false := by
      cases h : answer x with
      | false => rfl
      | true => exact (hx ((hans x).mpr h)).elim
    rw [hout, hb]; rfl

end SparseIrred.UpperBounds.Machine
