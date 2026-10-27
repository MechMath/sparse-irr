import SparseIrred.UpperBounds.Section4.OracleMachineValueSpace

/-! # A single actual machine computes scalar values on every valid input -/

noncomputable section
namespace SparseIrred.UpperBounds.Section4

open Complexity Complexity.TM Complexity.Cobham Complexity.SpaceIter
open SparseIrred.UpperBounds.Machine

/-- A scalar-valued terminating trace; an empty output is permitted. -/
structure StreamingValueTraceOn (Valid : List Bool → Prop) (G : List Bool → List Bool)
    (f : ∀ x, Valid x → List Bool) (r w : Polynomial ℕ) where
  state : ∀ x, Valid x → ℕ → List Bool
  stop : ∀ x, Valid x → ℕ
  start : ∀ x hx, state x hx 0 = pair [] x
  step : ∀ x hx i, state x hx (i + 1) = G (state x hx i)
  length_le : ∀ x hx i, i ≤ stop x hx + 1 → (state x hx i).length ≤ r.eval x.length
  stop_pos : ∀ x hx, 1 ≤ stop x hx
  stop_le : ∀ x hx, stop x hx ≤ 2 ^ w.eval x.length
  running : ∀ x hx i, 0 < i → i < stop x hx → (state x hx i).headD false = false
  done : ∀ x hx, (state x hx (stop x hx)).headD false = true
  output : ∀ x hx, state x hx (stop x hx + 1) = f x hx

private theorem valueTraceOn_bounds {Valid : List Bool → Prop} {G : List Bool → List Bool}
    {f : ∀ x, Valid x → List Bool} {r w : Polynomial ℕ}
    (trace : StreamingValueTraceOn Valid G f r w) (k : ℕ) (tp : Polynomial ℕ) (x : List Bool) (hx : Valid x) :
    (∀ i, i ≤ trace.stop x hx + 1 →
      (trace.state x hx i).length + 1 ≤ (streamingPadding tp r).eval x.length) ∧
    (∀ i, i ≤ trace.stop x hx →
      1 + tp.eval (trace.state x hx i).length ≤ (streamingPadding tp r).eval x.length) ∧
    (∀ j, j ≤ trace.stop x hx →
      1 + 1 + (tp.eval (trace.state x hx j).length + 1 +
        tailBound k ((streamingPadding tp r).eval x.length)
          (trace.state x hx (j + 1)).length) + 1 +
        binarySuccTime (startCount x.length + j) + 1 + 5 ≤
        passBound k tp (streamingPadding tp r) r w x.length) := by
  have hmono : ∀ i, i ≤ trace.stop x hx + 1 →
      tp.eval (trace.state x hx i).length ≤ tp.eval (r.eval x.length) := fun i hi ↦
    polynomial_eval_mono_nat tp (trace.length_le x hx i hi)
  refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_, fun j hj ↦ ?_⟩
  · have := trace.length_le x hx i hi
    rw [streamingPadding_eval]
    omega
  · have := hmono i (by omega)
    rw [streamingPadding_eval]
    omega
  · have h1 := hmono j (by omega)
    have h2 := tailBound_mono k ((streamingPadding tp r).eval x.length)
      (trace.length_le x hx (j + 1) (by omega))
    have h3 : binarySuccTime (startCount x.length + j) ≤
        2 * (x.length + w.eval x.length + 1) + 2 := by
      have h4 := binarySuccTime_le (startCount x.length + j)
      have h5 := startCount_add_size_le x.length j (w.eval x.length)
        (le_trans hj (trace.stop_le x hx))
      omega
    rw [passBound]
    omega

/-- Full scalar-output compilation, including all intermediate tape configurations. -/
theorem valueMachine_exists_on {Valid : List Bool → Prop} {G : List Bool → List Bool}
    {f : ∀ x, Valid x → List Bool} {r w : Polynomial ℕ}
    (hG : G ∈ FP) (trace : StreamingValueTraceOn Valid G f r w) :
    ∃ (k : ℕ) (M : TM k) (q : Polynomial ℕ),
      (∀ x (hx : Valid x) c, M.reaches (M.initCfg x) c →
        c.WithinDecisionSpace x.length (q.eval x.length)) ∧
      (∀ x hx, ∃ c, M.reaches (M.initCfg x) c ∧ M.halted c ∧ c.output.HasOutput (f x hx)) := by
  obtain ⟨k, M, tp, hM⟩ := mem_FP_iff_computesInTime_polynomial.mp hG
  obtain ⟨q, hq⟩ := polyBound_windowBound k tp (streamingPadding tp r) r w
  refine ⟨_, oracleValueTM M (streamingPadding tp r), q + r + Polynomial.C 4, ?_, ?_⟩
  · intro x hx c hc
    obtain ⟨hHy, hHT, hb⟩ := valueTraceOn_bounds trace k tp x hx
    have hw := oracleValueTM_keepsWindow M hM (streamingPadding tp r) x
      ((streamingPadding tp r).eval x.length) rfl (by rw [streamingPadding_eval]; omega)
      (trace.state x hx) (trace.start x hx) (trace.step x hx) (trace.stop x hx) (trace.stop_pos x hx)
      hHy hHT (trace.running x hx) (trace.done x hx)
      (passBound k tp (streamingPadding tp r) r w x.length) hb
      (windowBound k tp (streamingPadding tp r) r w x.length) le_rfl c hc
    apply hw.mono
    have hq' := hq x.length
    have hf := trace.length_le x hx (trace.stop x hx + 1) le_rfl
    simp only [Polynomial.eval_add, Polynomial.eval_C]
    omega
  · intro x hx
    obtain ⟨hHy, hHT, hb⟩ := valueTraceOn_bounds trace k tp x hx
    obtain ⟨c, t, _, hr, hh, ho⟩ := oracleValueTM_hoareTime M hM (streamingPadding tp r) x
      ((streamingPadding tp r).eval x.length) rfl (by rw [streamingPadding_eval]; omega)
      (trace.state x hx) (trace.start x hx) (trace.step x hx) (trace.stop x hx) (trace.stop_pos x hx)
      hHy hHT (trace.running x hx) (trace.done x hx)
      (passBound k tp (streamingPadding tp r) r w x.length) hb
      (Tape.init (x.map Γ.ofBool)) (fun _ ↦ Tape.init []) (Tape.init []) ⟨rfl, rfl, rfl⟩
    exact ⟨c, reaches_of_reachesIn hr, hh, by rw [trace.output x hx] at ho; exact ho⟩

end SparseIrred.UpperBounds.Section4
