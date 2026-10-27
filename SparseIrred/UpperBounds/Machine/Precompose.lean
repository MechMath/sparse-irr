import SparseIrred.UpperBounds.Machine.GuessVerify
import Complexitylib.Models.TuringMachine.Composition.Nondeterministic.Decides
import Complexitylib.Classes.P.Internal.NormalForm

/-!
# Exact probabilistic composition with deterministic preprocessing

The constructed composition machine computes an `FP` map and then runs an actual
probabilistic machine on its output. Its deterministic prefix consumes irrelevant
choice bits. Distinct fixed positions select the subsequent random choices, so the
composition preserves exact acceptance probability, including strict majority gaps.
-/

namespace SparseIrred.UpperBounds.Machine

open Complexity Complexity.NTM

set_option backward.isDefEq.respectTransparency false

/-- All-path termination transfers through the concrete deterministic-preprocessing
machine, without any assumption about a language being decided. -/
theorem precompose_allPathsHaltIn {nf ng : ℕ} {tmF : TM nf} {N : NTM ng}
    {g : List Bool → List Bool} {TF TG : ℕ → ℕ}
    (hF : tmF.ComputesInTime g TF) (hN : N.AllPathsHaltIn TG)
    (hmono : Monotone TG) (hne : N.qstart ≠ N.qhalt) :
    (compositionNTM tmF N).AllPathsHaltIn
      (fun n ↦ 4 * TF n + 11 + TG (TF n)) := by
  let L : Language := {z | N.AcceptsInTime z (TG z.length)}
  exact (compositionNTM_decidesInTime hF (show N.DecidesInTime L TG from
    ⟨hN, fun _ ↦ Iff.rfl⟩) hmono hne).1

/-- The concrete composition machine has exactly the acceptance probability of
the second machine on the preprocessed input. -/
theorem precompose_acceptProb {nf ng : ℕ} {tmF : TM nf} {N : NTM ng}
    {g : List Bool → List Bool} {TF TG : ℕ → ℕ}
    (hF : tmF.ComputesInTime g TF) (hN : N.AllPathsHaltIn TG)
    (hmono : Monotone TG) (hne : N.qstart ≠ N.qhalt) (x : List Bool) :
    (compositionNTM tmF N).acceptProb x (4 * TF x.length + 11 + TG (TF x.length)) =
      N.acceptProb (g x) (TG (g x).length) := by
  classical
  obtain ⟨E, t, ht, _hboundary, hrun⟩ := compositionNTM_trace_run tmF N hF x hne
  let K := 4 * TF x.length + 11 + TG (TF x.length)
  let m := TG (g x).length
  let s := K - t - 1
  have hlength := hF.output_length_le x
  have hm : m ≤ s + 1 := by
    have := hmono hlength
    dsimp [m, s, K]
    omega
  have htime : K = (s + 1) + t := by dsimp [K, s]; omega
  let schedule : Fin m ↪ Fin ((s + 1) + t) :=
    { toFun := fun i ↦ ⟨i.val + t, by omega⟩
      inj' := by intro i j h; apply Fin.ext; have := Fin.ext_iff.mp h; dsimp at this; omega }
  let verifier : (Fin m → Bool) → Bool := fun seed ↦
    decide (N.halted (N.trace m seed (N.initCfg (g x))) ∧
      (N.trace m seed (N.initCfg (g x))).output.cells 1 = Γ.one)
  have htrace : ∀ choices : Fin ((s + 1) + t) → Bool,
      let result := (compositionNTM tmF N).trace ((s + 1) + t) choices
        ((compositionNTM tmF N).initCfg x)
      result.state = (compositionNTM tmF N).qhalt ∧
        (result.output.cells 1 = Γ.one ↔ verifier (scheduledSeed schedule choices) = true) := by
    intro choices
    dsimp only
    rw [hrun s choices]
    have hfreeze := N.trace_mono hm
      (choices := scheduledSeed schedule choices)
      (choices' := fun i : Fin (s + 1) ↦ choices ⟨i.val + t, by omega⟩)
      (c := N.initCfg (g x)) (fun _ ↦ rfl) (hN (g x) _)
    rw [hfreeze]
    constructor
    · exact (placedCfg_halted_iff tmF N E.work E.input _).mpr (hN (g x) _)
    · change (N.trace m (scheduledSeed schedule choices) (N.initCfg (g x))).output.cells 1 =
          Γ.one ↔ decide (_ ∧ _) = true
      rw [decide_eq_true_eq]
      exact (and_iff_right (hN (g x) _)).symm
  change (compositionNTM tmF N).acceptProb x K = _
  rw [htime, acceptProb_eq_verifier_fraction _ x schedule verifier htrace]
  unfold NTM.acceptProb NTM.acceptCount
  congr 2
  congr 1
  apply Finset.filter_congr
  intro seed _
  simp only [verifier, decide_eq_true_eq]
  rfl

/-- Polynomial deterministic preprocessing preserves exact probabilistic behavior.
The returned machine and its polynomial time bound are constructed from the two
input machines; no implementation or target-language certificate is assumed. -/
theorem exists_polynomial_precompose {g : List Bool → List Bool} (hg : g ∈ FP)
    {ng : ℕ} (N : NTM ng) {TG : ℕ → ℕ} {d : ℕ}
    (hN : N.AllPathsHaltIn TG) (hTG : TG =O (· ^ d)) (hne : N.qstart ≠ N.qhalt) :
    ∃ (k : ℕ) (tm : NTM k) (time : ℕ → ℕ) (e : ℕ),
      tm.AllPathsHaltIn time ∧ time =O (· ^ e) ∧
        ∀ x, tm.acceptProb x (time x.length) = N.acceptProb (g x) (TG (g x).length) := by
  obtain ⟨nf, tmF, p, hF⟩ := mem_FP_iff_computesInTime_polynomial_internal.mp hg
  obtain ⟨q, hq⟩ := BigO.pow_polynomial_bound hTG
  let time : ℕ → ℕ := fun n ↦ 4 * p.eval n + 11 + q.eval (p.eval n)
  let bound : Polynomial ℕ := Polynomial.C 4 * p + Polynomial.C 11 + q.comp p
  have htime : ∀ n, time n = bound.eval n := by simp [time, bound, Polynomial.eval_comp]
  refine ⟨_, compositionNTM tmF N, time, bound.natDegree, ?_, ?_, ?_⟩
  · exact precompose_allPathsHaltIn hF (hN.mono hq) (polynomial_eval_mono_nat q) hne
  · exact BigO.of_polynomial_bound bound (fun n ↦ le_of_eq (htime n))
  · intro x
    calc
      _ = N.acceptProb (g x) (q.eval (g x).length) :=
        precompose_acceptProb hF (hN.mono hq) (polynomial_eval_mono_nat q) hne x
      _ = N.acceptProb (g x) (TG (g x).length) :=
        N.acceptProb_eq_of_le_of_allPathsHaltIn hq hN (g x)

end SparseIrred.UpperBounds.Machine
