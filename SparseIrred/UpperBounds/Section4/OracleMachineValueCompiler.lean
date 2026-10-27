import SparseIrred.UpperBounds.Section4.OracleMachineValueSpace

/-! # A bounded-state FP iteration produces its complete value on an actual TM -/

noncomputable section
namespace SparseIrred.UpperBounds.Section4

open Complexity Complexity.TM Complexity.Cobham Complexity.SpaceIter
open SparseIrred.UpperBounds.Machine

/-- A scalar-valued terminating trace; an empty output is permitted. -/
structure StreamingValueTrace (G f : List Bool → List Bool) (r w : Polynomial ℕ) where
  state : List Bool → ℕ → List Bool
  stop : List Bool → ℕ
  start : ∀ x, state x 0 = pair [] x
  step : ∀ x i, state x (i + 1) = G (state x i)
  length_le : ∀ x i, i ≤ stop x + 1 → (state x i).length ≤ r.eval x.length
  stop_pos : ∀ x, 1 ≤ stop x
  stop_le : ∀ x, stop x ≤ 2 ^ w.eval x.length
  running : ∀ x i, 0 < i → i < stop x → (state x i).headD false = false
  done : ∀ x, (state x (stop x)).headD false = true
  output : ∀ x, state x (stop x + 1) = f x

private theorem valueTrace_bounds {G f : List Bool → List Bool} {r w : Polynomial ℕ}
    (trace : StreamingValueTrace G f r w) (k : ℕ) (tp : Polynomial ℕ) (x : List Bool) :
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

/-- Full scalar-output compilation, including all intermediate tape configurations. -/
theorem valueMachine_exists {G f : List Bool → List Bool} {r w : Polynomial ℕ}
    (hG : G ∈ FP) (trace : StreamingValueTrace G f r w) :
    ∃ (k : ℕ) (M : TM k) (q : Polynomial ℕ),
      (∀ x c, M.reaches (M.initCfg x) c →
        c.WithinDecisionSpace x.length (q.eval x.length)) ∧
      (∀ x, ∃ c, M.reaches (M.initCfg x) c ∧ M.halted c ∧ c.output.HasOutput (f x)) := by
  obtain ⟨k, M, tp, hM⟩ := mem_FP_iff_computesInTime_polynomial.mp hG
  obtain ⟨q, hq⟩ := polyBound_windowBound k tp (streamingPadding tp r) r w
  refine ⟨_, oracleValueTM M (streamingPadding tp r), q + r + Polynomial.C 4, ?_, ?_⟩
  · intro x c hc
    obtain ⟨hHy, hHT, hb⟩ := valueTrace_bounds trace k tp x
    have hw := oracleValueTM_keepsWindow M hM (streamingPadding tp r) x
      ((streamingPadding tp r).eval x.length) rfl (by rw [streamingPadding_eval]; omega)
      (trace.state x) (trace.start x) (trace.step x) (trace.stop x) (trace.stop_pos x)
      hHy hHT (trace.running x) (trace.done x)
      (passBound k tp (streamingPadding tp r) r w x.length) hb
      (windowBound k tp (streamingPadding tp r) r w x.length) le_rfl c hc
    apply hw.mono
    have hq' := hq x.length
    have hf := trace.length_le x (trace.stop x + 1) le_rfl
    simp only [Polynomial.eval_add, Polynomial.eval_C]
    omega
  · intro x
    obtain ⟨hHy, hHT, hb⟩ := valueTrace_bounds trace k tp x
    obtain ⟨c, t, _, hr, hh, ho⟩ := oracleValueTM_hoareTime M hM (streamingPadding tp r) x
      ((streamingPadding tp r).eval x.length) rfl (by rw [streamingPadding_eval]; omega)
      (trace.state x) (trace.start x) (trace.step x) (trace.stop x) (trace.stop_pos x)
      hHy hHT (trace.running x) (trace.done x)
      (passBound k tp (streamingPadding tp r) r w x.length) hb
      (Tape.init (x.map Γ.ofBool)) (fun _ ↦ Tape.init []) (Tape.init []) ⟨rfl, rfl, rfl⟩
    exact ⟨c, reaches_of_reachesIn hr, hh, by rw [trace.output] at ho; exact ho⟩

end SparseIrred.UpperBounds.Section4
