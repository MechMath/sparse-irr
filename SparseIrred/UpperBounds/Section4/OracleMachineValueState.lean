import SparseIrred.UpperBounds.Section4.OracleMachineCompiler

/-! # Retaining the complete final state of the actual iteration machine -/

noncomputable section
namespace SparseIrred.UpperBounds.Section4
open Complexity Complexity.TM Complexity.Cobham Complexity.SpaceIter
variable {k : ℕ}

theorem oracle_spaceIterTM_hoareTime_finalState (M : TM k) {G : List Bool → List Bool} {T : ℕ → ℕ}
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
    (spaceIterTM M p).HoareTime
      (fun inp work out => inp = Tape.init (x.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (fun inp work out => Parked inp ∧ Tape.StartInvariant inp ∧
        work = iterBank M (Y (N + 1)) inp (regTape H) H (startCount x.length + N + 1) ∧
        out = slotOf (readBackWrite (headSym (Y (N + 1)))).toΓ)
      (proBound k p H x.length + 1 + (N - 1 + 1) * b + 1 + b) := by
  set start := startCount x.length with hstart
  set junkT : Tape := regTape H with hjunkT
  have hjunkP : Parked junkT := parked_regTape H
  have hjunkSI : Tape.StartInvariant junkT := startInvariant_regTape H
  -- the loop, with the input tape read off the configuration
  have hloop : (loopTM (bodyTM M) (testTM k)).HoareTime
      (fun inp work out => Parked inp ∧ Tape.StartInvariant inp ∧
        work = iterBank M (Y 0) inp junkT H start ∧ out = parkedBlank)
      (fun inp work out => Parked inp ∧ Tape.StartInvariant inp ∧
        work = iterBank M (Y N) inp junkT H (start + N) ∧
        out = slotOf (slotSym Y N)) ((N - 1 + 1) * b) := by
    rintro inp work out ⟨hP, hSI, hw, ho⟩
    obtain ⟨c', t, ht, hreach, hhalt, hi', hw', ho'⟩ :=
      loop_hoareTime M hcomp Y hY inp junkT hP hSI hjunkP hjunkSI H start N hN
        (fun i hi => hHy i (by omega)) (fun i hi => hHT i (by omega)) hcont hdone b
        (fun j hj => hb j (by omega)) inp work out
        ⟨rfl, by rw [hw, show start + 0 = start from rfl],
          by rw [ho, slotSym, ite_eq_left rfl, slotOf_blank]⟩
    exact ⟨c', t, ht, hreach, hhalt, by rw [hi']; exact hP, by rw [hi']; exact hSI,
      by rw [hw', hi'], ho'⟩
  -- the epilogue, likewise
  have hepi : (epilogueTM M).HoareTime
      (fun inp work out => Parked inp ∧ Tape.StartInvariant inp ∧
        work = iterBank M (Y N) inp junkT H (start + N) ∧
        out = slotOf (slotSym Y N))
      (fun inp work out => Parked inp ∧ Tape.StartInvariant inp ∧
        work = iterBank M (Y (N + 1)) inp (regTape H) H (startCount x.length + N + 1) ∧
        out = slotOf (readBackWrite (headSym (Y (N + 1)))).toΓ) b := by
    rintro inp work out ⟨hP, hSI, hw, ho⟩
    obtain ⟨c', t, ht, hreach, hhalt, hi', hw', ho'⟩ :=
      epilogueTM_hoareTime M hcomp (Y N) inp junkT hP hSI hjunkP hjunkSI H (start + N)
        (by have := hHy N (by omega); omega) (hHT N le_rfl)
        (by rw [← hY N]; exact hHy (N + 1) le_rfl) (slotSym Y N) (slotSym_ne_start Y N)
        inp work out ⟨rfl, hw, ho⟩
    refine ⟨c', t, le_trans ht ?_, hreach, hhalt, ?_⟩
    · have := hb N le_rfl
      rw [← hY N]
      omega
    · refine ⟨hi' ▸ hP, hi' ▸ hSI, ?_, ?_⟩
      · rw [hw', hi', hY N]
      · rw [ho', hY N]
  -- the two seams
  have hseam1 : ∀ inp work out,
      (Parked inp ∧ Tape.StartInvariant inp ∧
        work = iterBank M (pair [] x) inp junkT H start ∧ out = parkedBlank) →
      (Parked (transitionInput inp) ∧ Tape.StartInvariant (transitionInput inp) ∧
        (fun i => transitionTape (work i)) =
          iterBank M (Y 0) (transitionInput inp) junkT H start ∧
        transitionTape out = parkedBlank) := by
    rintro inp work out ⟨hP, hSI, hw, ho⟩
    rw [transitionInput_eq_self hP.read_ne_start]
    refine ⟨hP, hSI, ?_, ?_⟩
    · rw [hw, hY0, iterBank_trans M (pair [] x) inp junkT hjunkP H start]
    · rw [ho]
      exact transitionTape_eq_self parked_parkedBlank.read_ne_start
  have hseam2 : ∀ inp work out,
      (Parked inp ∧ Tape.StartInvariant inp ∧
        work = iterBank M (Y N) inp junkT H (start + N) ∧ out = slotOf (slotSym Y N)) →
      (Parked (transitionInput inp) ∧ Tape.StartInvariant (transitionInput inp) ∧
        (fun i => transitionTape (work i)) =
          iterBank M (Y N) (transitionInput inp) junkT H (start + N) ∧
        transitionTape out = slotOf (slotSym Y N)) := by
    rintro inp work out ⟨hP, hSI, hw, ho⟩
    rw [transitionInput_eq_self hP.read_ne_start]
    refine ⟨hP, hSI, ?_, ?_⟩
    · rw [hw, iterBank_trans M (Y N) inp junkT hjunkP H (start + N)]
    · rw [ho]
      exact transitionTape_eq_self
        (slotOf_parked _ (slotSym_ne_start Y N)).read_ne_start
  exact seqTM_hoareTime _ _
    (seqTM_hoareTime _ _ (prologueTM_hoareTime M p x H hH hHx) hseam1 hloop) hseam2 hepi


end SparseIrred.UpperBounds.Section4
