import SparseIrred.UpperBounds.Section4.OracleMachinePublish

/-! # Publishing the whole value left by the actual iteration machine -/

noncomputable section
namespace SparseIrred.UpperBounds.Section4

open Complexity Complexity.TM Complexity.Cobham Complexity.SpaceIter

variable {k : ℕ}

theorem iterBank_valueTape (M : TM k) (y : List Bool) (inp junk : Tape) (H c : ℕ) :
    iterBank M y inp junk H c vinIdx = (Tape.init (y.map Γ.ofBool)).move .right := by
  rw [vinIdx, iterBank_app, applyPre, Fin.snoc_castSucc]
  exact retargetInputStartedCfg_work_last M y inp

/-- Clear the temporary verdict cell, then copy the complete final state to real output. -/
def valueEpilogueTM (k : ℕ) : TM (3 + (k + 2) + 0) :=
  seqTM (writeOutputBitTM resIdx) (publishWorkTM vinIdx)

theorem valueEpilogueTM_hoareTime (M : TM k) (y : List Bool) (inp junk : Tape)
    (hi : Parked inp) (hj : Parked junk) (H c : ℕ) (s : Γ) (hs : s ≠ .start) :
    (valueEpilogueTM k).HoareTime
      (fun inp' work out ↦ inp' = inp ∧ work = iterBank M y inp junk H c ∧ out = slotOf s)
      (fun _ _ out ↦ out.HasOutput y) (1 + 1 + (y.length + 1)) := by
  refine seqTM_hoareTime _ _ (clear_hoareTime M y inp junk hi hj H c s hs)
    ?_ (publishWorkTM_hoareTime vinIdx y)
  intro inp' work out hp
  obtain ⟨hinput, hwork, hout⟩ := hp
  constructor
  · rw [hwork]
    dsimp only
    rw [iterBank_valueTape]
    exact transitionTape_eq_self (parked_init_input y).read_ne_start
  · rw [hout]
    exact transitionTape_eq_self parked_parkedBlank.read_ne_start

/-- The scalar-producing iteration machine has an actual output copier after its loop. -/
def oracleValueTM (M : TM k) (p : Polynomial ℕ) : TM (3 + (k + 2) + 0) :=
  seqTM (spaceIterTM M p) (valueEpilogueTM k)

/-- Full scalar output, rather than just its first bit, from the same bounded-state trace. -/
theorem oracleValueTM_hoareTime (M : TM k) {G : List Bool → List Bool} {T : ℕ → ℕ}
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
        binarySuccTime (startCount x.length + j) + 1 + 5 ≤ b) :
    (oracleValueTM M p).HoareTime
      (fun inp work out ↦ inp = Tape.init (x.map Γ.ofBool) ∧
        work = (fun _ ↦ Tape.init []) ∧ out = Tape.init [])
      (fun _ _ out ↦ out.HasOutput (Y (N + 1)))
      ((proBound k p H x.length + 1 + (N - 1 + 1) * b + 1 + b) + 1 +
        (1 + 1 + ((Y (N + 1)).length + 1))) := by
  have hs := oracle_spaceIterTM_hoareTime_finalState M hcomp p x H hH hHx
    Y hY0 hY N hN hHy hHT hcont hdone b hb
  have hepi : (valueEpilogueTM k).HoareTime
      (fun inp work out ↦ Parked inp ∧ Tape.StartInvariant inp ∧
        work = iterBank M (Y (N + 1)) inp (regTape H) H (startCount x.length + N + 1) ∧
        out = slotOf (readBackWrite (headSym (Y (N + 1)))).toΓ)
      (fun _ _ out ↦ out.HasOutput (Y (N + 1))) (1 + 1 + ((Y (N + 1)).length + 1)) := by
    intro inp work out hp
    obtain ⟨hi, hsi, hw, ho⟩ := hp
    exact valueEpilogueTM_hoareTime M (Y (N + 1)) inp (regTape H) hi (parked_regTape H) H
      (startCount x.length + N + 1) (readBackWrite (headSym (Y (N + 1)))).toΓ
      (toΓ_readBackWrite_ne_start _) inp work out ⟨rfl, hw, ho⟩
  refine seqTM_hoareTime _ _ hs ?_ hepi
  intro inp work out hp
  obtain ⟨hi, hsi, hw, ho⟩ := hp
  rw [transitionInput_eq_self hi.read_ne_start]
  refine ⟨hi, hsi, ?_, ?_⟩
  · rw [hw]
    exact iterBank_trans M _ _ _ (parked_regTape H) _ _
  · rw [ho]
    exact transitionTape_eq_self (slotOf_parked _ (toΓ_readBackWrite_ne_start _)).read_ne_start

end SparseIrred.UpperBounds.Section4
