import SparseIrred.UpperBounds.Section4.StageMachine

/-!
# Compiling staged local transitions to a deterministic PSPACE machine

The realization interface describes only local transitions, initialization, and
publication. Complete staged correctness and termination are proved from the
mathematical machine, and binary state bounds are supplied separately.
-/

namespace SparseIrred.UpperBounds.Section4

open Complexity SparseIrred.UpperBounds.Machine

/-- Local implementation laws for stage dispatch and one stack step. In particular,
no law presupposes acceptance, a determinant result, or the final language. -/
structure LocalControlStepFP (T : List Bool → ThreeStages) where
  code : ∀ x, (T x).State → List Bool
  transition : List Bool → List Bool
  transition_FP : transition ∈ FP
  setup : ∀ x, transition (pair [] x) = code x (T x).initial
  local_step : ∀ x s, ¬s.Halted → transition (code x s) = code x ((T x).step s)
  publish : ∀ x b, transition (code x (.done b)) = [b]
  flag : ∀ x s, (code x s).headD false = decide s.Halted

namespace LocalControlStepFP

variable {T : List Bool → ThreeStages}

theorem iterate_code (I : LocalControlStepFP T) (B : List Bool → ℕ)
    (hB : ∀ x, (T x).WorkBound (B x)) (x : List Bool) (t : ℕ)
    (ht : t ≤ (T x).stop (B x) (hB x)) :
    I.transition^[t + 1] (pair [] x) =
      I.code x ((T x).step^[t] (T x).initial) := by
  induction t with
  | zero => simpa using I.setup x
  | succ t ih =>
      rw [Function.iterate_succ_apply', ih (by omega),
        I.local_step x _ ((T x).not_halted_before (B x) (hB x) t (by omega)),
        Function.iterate_succ_apply']

theorem iterate_publish (I : LocalControlStepFP T) (B : List Bool → ℕ)
    (hB : ∀ x, (T x).WorkBound (B x)) (x : List Bool) :
    I.transition^[((T x).stop (B x) (hB x) + 1) + 1] (pair [] x) =
      [(T x).answer] := by
  rw [Function.iterate_succ_apply', I.iterate_code B hB x _ le_rfl,
    ThreeStages.stop_result, I.publish]

/-- A complete bounded binary trace, derived from the local implementation laws. -/
noncomputable def trace (I : LocalControlStepFP T) (B : List Bool → ℕ)
    (hB : ∀ x, (T x).WorkBound (B x)) (r w : Polynomial ℕ)
    (hinput : ∀ x : List Bool, (pair [] x).length ≤ r.eval x.length)
    (hcode : ∀ x s, (I.code x s).length ≤ r.eval x.length)
    (hone : ∀ n, 1 ≤ r.eval n)
    (hbudget : ∀ x, 3 * (B x + 1) + 1 ≤ 2 ^ w.eval x.length) :
    StreamingTrace I.transition (fun x ↦ (T x).answer) r w where
  state x t := I.transition^[t] (pair [] x)
  stop x := (T x).stop (B x) (hB x) + 1
  start _ := rfl
  step _ _ := Function.iterate_succ_apply' _ _ _
  length_le x t ht := by
    by_cases h0 : t = 0
    · subst t
      exact hinput x
    by_cases hs : t ≤ (T x).stop (B x) (hB x) + 1
    · obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
      rw [I.iterate_code B hB x u (by omega)]
      exact hcode x _
    · have he : t = ((T x).stop (B x) (hB x) + 1) + 1 := by omega
      rw [he, I.iterate_publish B hB]
      exact hone x.length
  stop_pos _ := by omega
  stop_le x := by
    have h := (T x).stop_bound (B x) (hB x)
    exact (Nat.add_le_add_right h 1).trans (hbudget x)
  running x t ht hs := by
    obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
    rw [I.iterate_code B hB x u (by omega), I.flag]
    exact decide_eq_false ((T x).not_halted_before (B x) (hB x) u (by omega))
  done x := by
    rw [I.iterate_code B hB x _ le_rfl, I.flag,
      decide_eq_true ((T x).halted_stop _ _)]
  answer_nonempty x := by rw [I.iterate_publish B hB]; simp
  answer_eq x := by rw [I.iterate_publish B hB]; rfl

/-- The actual deterministic iteration machine decides the staged answer in
polynomial space, given only local realizations and explicitly stated bounds. -/
theorem language_mem_PSPACE (I : LocalControlStepFP T) (B : List Bool → ℕ)
    (hB : ∀ x, (T x).WorkBound (B x)) (r w : Polynomial ℕ)
    (hinput : ∀ x : List Bool, (pair [] x).length ≤ r.eval x.length)
    (hcode : ∀ x s, (I.code x s).length ≤ r.eval x.length)
    (hone : ∀ n, 1 ≤ r.eval n)
    (hbudget : ∀ x, 3 * (B x + 1) + 1 ≤ 2 ^ w.eval x.length) :
    {x | (T x).answer = true} ∈ PSPACE :=
  streamingLanguage_mem_PSPACE I.transition_FP
    (I.trace B hB r w hinput hcode hone hbudget) (fun _ ↦ Iff.rfl)

end LocalControlStepFP

end SparseIrred.UpperBounds.Section4
