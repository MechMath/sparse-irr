import SparseIrred.UpperBounds.Section4.OracleMachineValueEpilogue

/-! # Every-prefix tape space for the complete scalar-output iteration machine -/

noncomputable section
namespace SparseIrred.UpperBounds.Section4

open Complexity Complexity.TM Complexity.Cobham Complexity.SpaceIter

variable {k : ℕ}

theorem oracleValueTM_keepsWindow (M : TM k) {G : List Bool → List Bool} {T : ℕ → ℕ}
    (hcomp : M.ComputesInTime G T) (p : Polynomial ℕ) (x : List Bool) (H : ℕ)
    (hH : H = p.eval x.length) (hHx : x.length + 4 ≤ H)
    (Y : ℕ → List Bool) (hY0 : Y 0 = pair [] x) (hY : ∀ i, Y (i + 1) = G (Y i))
    (N : ℕ) (hN : 1 ≤ N)
    (hHy : ∀ i, i ≤ N + 1 → (Y i).length + 1 ≤ H)
    (hHT : ∀ i, i ≤ N → 1 + T (Y i).length ≤ H)
    (hcont : ∀ i, 0 < i → i < N → (Y i).headD false = false)
    (hdone : (Y N).headD false = true) (b : ℕ)
    (hb : ∀ j, j ≤ N →
      1 + 1 + (T (Y j).length + 1 + tailBound k H (Y (j + 1)).length) + 1 +
        binarySuccTime (startCount x.length + j) + 1 + 5 ≤ b)
    (W : ℕ) (hW : proBound k p H x.length + 1 + b ≤ W) :
    ∀ c, (oracleValueTM M p).reaches ((oracleValueTM M p).initCfg x) c →
      c.WithinDecisionSpace x.length (W + (Y (N + 1)).length + 4) := by
  let U := W + (Y (N + 1)).length + 4
  have hU : 1 ≤ U := by dsimp [U]; omega
  let post : TM.TapePred (3 + (k + 2) + 0) := fun inp work out ↦
    Parked inp ∧ Tape.StartInvariant inp ∧ inp.head ≤ x.length + W + 1 ∧
      work = iterBank M (Y (N + 1)) inp (regTape H) H (startCount x.length + N + 1) ∧
      out = slotOf (readBackWrite (headSym (Y (N + 1)))).toΓ
  have hbase := spaceIterTM_keepsWindow M hcomp p x H hH hHx Y hY0 hY N hN hHy hHT
    hcont hdone b hb W hW
  have hpost : ∀ c, c = (spaceIterTM M p).initCfg x → ∃ e,
      (spaceIterTM M p).reaches c e ∧ (spaceIterTM M p).halted e ∧ post e.input e.work e.output := by
    intro c hc
    subst c
    obtain ⟨e, t, ht, hr, hh, hp⟩ := oracle_spaceIterTM_hoareTime_finalState M hcomp p x H hH hHx
      Y hY0 hY N hN hHy hHT hcont hdone b hb
      (Tape.init (x.map Γ.ofBool)) (fun _ ↦ Tape.init []) (Tape.init []) ⟨rfl, rfl, rfl⟩
    have hre : (spaceIterTM M p).reaches ((spaceIterTM M p).initCfg x) e := reaches_of_reachesIn hr
    have hw := hbase e hre
    exact ⟨e, hre, hh, hp.1, hp.2.1, hw.1.2, hp.2.2⟩
  have hepi : (valueEpilogueTM k).HoareTime post
      (fun _ _ out ↦ out.HasOutput (Y (N + 1))) ((Y (N + 1)).length + 3) := by
    intro inp work out hp
    obtain ⟨hi, hsi, hhead, hw, ho⟩ := hp
    simpa only [show 1 + 1 + ((Y (N + 1)).length + 1) = (Y (N + 1)).length + 3 by omega] using
      valueEpilogueTM_hoareTime M (Y (N + 1)) inp (regTape H) hi (parked_regTape H) H
        (startCount x.length + N + 1) (readBackWrite (headSym (Y (N + 1)))).toΓ
        (toΓ_readBackWrite_ne_start _) inp work out ⟨rfl, hw, ho⟩
  have hepiSpace : (valueEpilogueTM k).KeepsWindowOn
      (fun c ↦ c.state = (valueEpilogueTM k).qstart ∧ post c.input c.work c.output) x.length U := by
    have hh := keepsWindowOn_of_hoareTime hepi (inputLength := x.length) (h₀ := W + 1)
      (by
        intro inp work out hp i
        rw [hp.2.2.2.1]
        exact (iterBank_head M _ _ _ (by rw [regT_head]) _ _ i).trans (by omega))
      (by intro inp work out hp; exact hp.2.2.1.trans (by omega))
      (by intro inp work out hp; rw [hp.2.2.2.2, slotOf_head]; omega)
    exact hh.mono_space (by dsimp [U]; omega)
  have hall := seqTM_keepsWindowOn (spaceIterTM M p) (valueEpilogueTM k) hU
    (pre₁ := fun c ↦ c = (spaceIterTM M p).initCfg x)
    (pre₂ := fun c ↦ c.state = (valueEpilogueTM k).qstart ∧ post c.input c.work c.output)
    (mid := post)
    (by
      intro c hc
      subst c
      refine ⟨rfl, ⟨⟨fun i ↦ ?_, ?_⟩, ?_⟩, ?_, ?_, ?_⟩
      · change 0 ≤ U; omega
      · change 0 ≤ x.length + U + 1; omega
      · change 0 ≤ U + 1; omega
      · exact Tape.StartInvariant.init_ofBool x
      · intro i; exact Tape.StartInvariant.init_nil
      · exact Tape.StartInvariant.init_nil)
    (by intro c hc e he; subst c; exact (hbase e he).mono (by dsimp [U]; omega))
    hpost hepiSpace
    (by
      intro inp work out hp
      obtain ⟨hi, hsi, hhead, hw, ho⟩ := hp
      rw [transitionInput_eq_self hi.read_ne_start]
      refine ⟨rfl, hi, hsi, hhead, ?_, ?_⟩
      · rw [hw]
        exact iterBank_trans M _ _ _ (parked_regTape H) _ _
      · rw [ho]
        exact transitionTape_eq_self (slotOf_parked _ (toΓ_readBackWrite_ne_start _)).read_ne_start)
  intro c hc
  exact hall _ ⟨(spaceIterTM M p).initCfg x, rfl, rfl⟩ c hc

end SparseIrred.UpperBounds.Section4
