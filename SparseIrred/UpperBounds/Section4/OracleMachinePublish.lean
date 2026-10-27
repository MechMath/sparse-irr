import SparseIrred.UpperBounds.Section4.OracleMachineValueState

/-! # An actual work-tape-to-output copier for complete scalar results -/

namespace SparseIrred.UpperBounds.Section4

open Complexity Complexity.TM

variable {n : ℕ}

def publishWorkTM (src : Fin n) : TM n where
  Q := CopyPhase
  qstart := .copying
  qhalt := .done
  δ q i w o := match q with
    | .copying => if w src = Γ.blank then
        (.done, fun j ↦ readBackWrite (w j), readBackWrite o,
          idleDir i, fun j ↦ idleDir (w j), idleDir o)
      else (.copying, fun j ↦ readBackWrite (w j), readBackWrite (w src), idleDir i,
        fun j ↦ if j = src then .right else idleDir (w j), .right)
    | .done => allIdle .done i w o
  δ_right_of_start := by
    intro q i w o
    cases q with
    | copying =>
      dsimp only
      split
      · exact rightOfStart_allIdle i w o
      · refine ⟨idleDir_right_of_start, ?_, fun _ ↦ rfl⟩
        intro j hj
        dsimp only
        split <;> first | rfl | exact idleDir_right_of_start hj
    | done => exact rightOfStart_allIdle i w o

theorem publishWorkTM_isTransducer (src : Fin n) : (publishWorkTM src).IsTransducer := by
  intro q i w o
  cases q <;> simp only [publishWorkTM, allIdle]
  · split <;> cases o <;> simp [idleDir]
  · cases o <;> simp [idleDir]

private theorem publishWork_loop (src : Fin n) (x : List Bool) :
    ∀ rem k (c : Cfg n (publishWorkTM src).Q), rem = x.length - k →
      c.state = .copying → (c.work src).cells = (Tape.init (x.map Γ.ofBool)).cells →
      (c.work src).head = k + 1 → c.output.HasBinaryPrefix (x.take k) → k ≤ x.length →
      ∃ d, (publishWorkTM src).reachesIn (rem + 1) c d ∧
        (publishWorkTM src).halted d ∧ d.output.HasOutput x := by
  intro rem
  induction rem with
  | zero =>
    intro k c hr hs hcells hh hp hk
    have hk' : k = x.length := by omega
    subst k
    have hread : (c.work src).read = Γ.blank := by
      simp [Tape.read, hh, hcells, Tape.init_ofBool_cells_ge x x.length le_rfl]
    have hpf : c.output.HasBinaryPrefix x := by simpa using hp
    have hout : c.output.read = Γ.blank := by
      simp [Tape.read, hpf.1, hpf.2.2 x.length le_rfl]
    let d : Cfg n (publishWorkTM src).Q :=
      ⟨.done, c.input.move (idleDir c.input.read),
        fun j ↦ (c.work j).writeAndMove (readBackWrite (c.work j).read) (idleDir (c.work j).read),
        c.output.writeAndMove (readBackWrite c.output.read) (idleDir c.output.read)⟩
    have hstep : (publishWorkTM src).step c = some d := by
      simp [TM.step, hs, publishWorkTM, hread, d]
    refine ⟨d, .step hstep .zero, rfl, ?_⟩
    have he : d.output = c.output := transitionTape_eq_self (by simp [hout])
    rw [he]
    exact ⟨hpf.2.1, hpf.2.2 x.length le_rfl⟩
  | succ rem ih =>
    intro k c hr hs hcells hh hp hk
    have hk' : k < x.length := by omega
    have hread : (c.work src).read = Γ.ofBool (x[k]'hk') := by
      simp [Tape.read, hh, hcells, Tape.init_ofBool_cells_lt x k hk']
    have hne : (c.work src).read ≠ Γ.start := by rw [hread]; cases x[k]'hk' <;> decide
    have hp' : (c.output.writeAndMove (Γ.ofBool (x[k]'hk')) .right).HasBinaryPrefix
        (x.take (k + 1)) := by
      have hwrite := Tape.hasBinaryPrefix_write_bit (x[k]'hk') hp
      simpa [List.take_concat_get' x k hk'] using hwrite
    let d : Cfg n (publishWorkTM src).Q :=
      ⟨.copying, c.input.move (idleDir c.input.read),
        fun j ↦ (c.work j).writeAndMove (readBackWrite (c.work j).read)
          (if j = src then .right else idleDir (c.work j).read),
        c.output.writeAndMove (Γ.ofBool (x[k]'hk')) .right⟩
    have hstep : (publishWorkTM src).step c = some d := by
      cases hb : x[k]'hk' <;>
        simp [TM.step, hs, publishWorkTM, hread, hb, d, Γ.ofBool, readBackWrite]
    have hsrc : d.work src = (c.work src).move .right := by
      simp only [d, ↓reduceIte]
      exact writeAndMove_readBack _ hne _
    obtain ⟨e, he, heh, heout⟩ := ih (k + 1) d (by omega) rfl
      (by rw [hsrc, Tape.move_cells]; exact hcells)
      (by rw [hsrc]; simp [Tape.move, hh]) hp' (by omega)
    exact ⟨e, .step hstep he, heh, heout⟩

/-- A complete scalar string is copied, including the empty string, with no truncation to a bit. -/
theorem publishWorkTM_hoareTime (src : Fin n) (x : List Bool) :
    (publishWorkTM src).HoareTime
      (fun _ work out ↦ work src = (Tape.init (x.map Γ.ofBool)).move .right ∧ out = parkedBlank)
      (fun _ _ out ↦ out.HasOutput x) (x.length + 1) := by
  intro inp work out hpre
  obtain ⟨d, hr, hh, ho⟩ := publishWork_loop src x x.length 0
    ⟨(publishWorkTM src).qstart, inp, work, out⟩ (by simp) rfl
    (by change (work src).cells = _; rw [hpre.1]; rfl)
    (by change (work src).head = _; rw [hpre.1]; rfl)
    (by change out.HasBinaryPrefix _; rw [hpre.2]; exact Tape.init_nil_move_right_hasBinaryPrefix_nil) (Nat.zero_le _)
  exact ⟨d, x.length + 1, le_rfl, hr, hh, ho⟩

end SparseIrred.UpperBounds.Section4
