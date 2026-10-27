import Complexitylib.Classes.EventProb
import Mathlib.Logic.Equiv.Set

/-!
# Exact probability for scheduled random bits

A Turing-machine trace consumes a choice bit at every step, including deterministic
administrative steps. A finite randomized verifier only uses its designated random
bits. This module proves that selecting distinct fixed trace positions preserves the
uniform distribution, and transfers a pointwise trace specification to the exact
acceptance probability of an actual `NTM`.

The results do not construct the deterministic verifier or prove its running time.
Those remain separate machine-level obligations. In particular, no theorem here
assumes irreducibility or the final complexity-class conclusion.
-/

namespace SparseIrred.UpperBounds.Machine

open Complexity

/-- The random seed obtained by reading a fixed collection of distinct trace positions. -/
def scheduledSeed {m T : ℕ} (schedule : Fin m ↪ Fin T) (choices : Fin T → Bool) :
    Fin m → Bool := choices ∘ schedule

private noncomputable def scheduleSplit {m T : ℕ} (schedule : Fin m ↪ Fin T) :
    (Fin T → Bool) ≃
      (Fin m → Bool) × ({j : Fin T // j ∉ Set.range schedule} → Bool) := by
  classical
  let indexSplit : Fin m ⊕ {j : Fin T // j ∉ Set.range schedule} ≃ Fin T :=
    (Equiv.sumCongr (Equiv.ofInjective schedule schedule.injective)
      (Equiv.refl _)).trans (Equiv.Set.sumCompl (Set.range schedule))
  exact (Equiv.arrowCongr indexSplit (Equiv.refl Bool)).symm.trans
    (Equiv.sumArrowEquivProdArrow _ _ Bool)

private theorem scheduleSplit_fst {m T : ℕ} (schedule : Fin m ↪ Fin T)
    (choices : Fin T → Bool) :
    (scheduleSplit schedule choices).1 = scheduledSeed schedule choices := by
  ext i
  rfl

/-- Every compact seed has equally many full trace-choice extensions. -/
theorem card_scheduledSeed_fiber {m T : ℕ} (schedule : Fin m ↪ Fin T)
    (seed : Fin m → Bool) :
    (Finset.univ.filter fun choices : Fin T → Bool =>
      scheduledSeed schedule choices = seed).card = 2 ^ (T - m) := by
  classical
  let Unused := {j : Fin T // j ∉ Set.range schedule}
  have hcardUnused : Fintype.card Unused = T - m := by
    have hsplit := Fintype.card_congr (Equiv.Set.sumCompl (Set.range schedule))
    have hrange := Fintype.card_congr (Equiv.ofInjective schedule schedule.injective)
    simp only [Fintype.card_sum, Fintype.card_fin] at hsplit hrange
    change Fintype.card (Set.range schedule) + Fintype.card Unused = T at hsplit
    omega
  calc
    _ = (({seed} : Finset (Fin m → Bool)) ×ˢ
        (Finset.univ : Finset (Unused → Bool))).card := by
      apply Finset.card_bij'
        (fun choices _ ↦ scheduleSplit schedule choices)
        (fun pair _ ↦ (scheduleSplit schedule).symm pair)
      · intro choices hchoices
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hchoices
        simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_univ, and_true]
        exact (scheduleSplit_fst schedule choices).trans hchoices
      · intro pair hpair
        simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_univ, and_true]
          at hpair
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← scheduleSplit_fst, Equiv.apply_symm_apply]
        exact hpair
      · intro choices _
        exact Equiv.symm_apply_apply _ _
      · intro pair _
        exact Equiv.apply_symm_apply _ _
    _ = 2 ^ (T - m) := by simp [hcardUnused]

/-- Administrative choice bits cancel from the probability of a verifier event. -/
theorem eventProb_scheduledSeed {m T : ℕ} (schedule : Fin m ↪ Fin T)
    (verifier : (Fin m → Bool) → Bool) :
    eventProb (Finset.univ.filter fun choices : Fin T → Bool =>
      verifier (scheduledSeed schedule choices) = true) =
        eventProb (Finset.univ.filter fun seed => verifier seed = true) := by
  have hle : m ≤ T := by simpa using Fintype.card_le_of_embedding schedule
  exact eventProb_filter_of_constant_fibers (by omega)
    (scheduledSeed schedule) _ _ (fun _ ↦ Iff.rfl)
    (card_scheduledSeed_fiber schedule)

/-- A pointwise specification of an actual machine trace gives its exact finite
acceptance probability. Only the designated random steps enter the denominator. -/
theorem acceptProb_eq_verifier_fraction {k m T : ℕ} (tm : NTM k) (x : List Bool)
    (schedule : Fin m ↪ Fin T) (verifier : (Fin m → Bool) → Bool)
    (htrace : ∀ choices : Fin T → Bool,
      let result := tm.trace T choices (tm.initCfg x)
      result.state = tm.qhalt ∧
        (result.output.cells 1 = Γ.one ↔ verifier (scheduledSeed schedule choices) = true)) :
    tm.acceptProb x T =
      ((Finset.univ.filter fun seed => verifier seed = true).card : ℚ) / 2 ^ m := by
  rw [NTM.acceptProb_eq_eventProb]
  have hevent :
      (Finset.univ.filter fun choices : Fin T → Bool =>
        let result := tm.trace T choices (tm.initCfg x)
        result.state = tm.qhalt ∧ result.output.cells 1 = Γ.one) =
      Finset.univ.filter (fun choices =>
        verifier (scheduledSeed schedule choices) = true) := by
    ext choices
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_iff_right (htrace choices).1 |>.trans (htrace choices).2
  rw [hevent, eventProb_scheduledSeed]
  rfl

end SparseIrred.UpperBounds.Machine
