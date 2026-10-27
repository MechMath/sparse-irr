import SparseIrred.UpperBounds.Section4.StackEncoding
import SparseIrred.UpperBounds.Machine.StreamingMachine

/-!
# Compiling the verified address-stack evaluator to a PSPACE machine

The only implementation input is a polynomial-time implementation of one local
stack transition, initialization and final output. Termination, the result of
the full computation and its resource bound are proved here, not assumed by the
implementation interface.
-/

namespace SparseIrred.UpperBounds.Section4

open Complexity
open SparseIrred.UpperBounds.Machine

variable {A R : Type*} [Add R] [Mul R]

instance (c : EntryConfig A R) : Decidable c.Halted := by
  cases c with
  | eval a stack => exact isFalse id
  | ret v stack => cases stack with
    | nil => exact isTrue trivial
    | cons f stack => exact isFalse id

/-- The first terminating configuration; this is a proof index, not a runtime register. -/
noncomputable def EntryProgram.stop (P : EntryProgram A R) (a : A) : ℕ :=
  Nat.find (show ∃ t, (P.step^[t] (.eval a [])).Halted from by
    obtain ⟨t, v, ht⟩ := P.terminates (.eval a [])
    exact ⟨t, by rw [ht]; trivial⟩)

theorem EntryProgram.halted_stop (P : EntryProgram A R) (a : A) :
    (P.step^[P.stop a] (.eval a [])).Halted := by
  unfold stop
  exact Nat.find_spec (p := fun t ↦ (P.step^[t] (.eval a [])).Halted) _

theorem EntryProgram.not_halted_before (P : EntryProgram A R) (a : A) (t : ℕ)
    (ht : t < P.stop a) : ¬(P.step^[t] (.eval a [])).Halted := Nat.find_min _ ht

theorem EntryProgram.stop_result (P : EntryProgram A R) (a : A) :
    P.step^[P.stop a] (.eval a []) = .ret (P.value a) [] := by
  have hh := P.halted_stop a
  have hv := P.meaning_iterate (.eval a []) (P.stop a)
  cases he : P.step^[P.stop a] (.eval a []) with
  | eval b stack => simp only [he, EntryConfig.Halted] at hh
  | ret v stack =>
    cases stack with
    | nil =>
      rw [he] at hv
      change v = P.value a at hv
      exact congrArg (fun v ↦ EntryConfig.ret v []) hv
    | cons f stack => simp only [he, EntryConfig.Halted] at hh

theorem EntryProgram.stop_bound (P : EntryProgram A R) (a : A) :
    P.stop a + 1 ≤ 2 ^ (P.rank a + 3) := by
  obtain ⟨t, v, ht, he⟩ := P.terminates_bounded (.eval a [])
  have hfind : P.stop a ≤ t := Nat.find_min' _ (by rw [he]; trivial)
  have hs := P.treeSize_le a
  simp only [work, List.map_nil, List.sum_nil, add_zero] at ht
  have hp : 2 ^ (P.rank a + 3) = 4 * 2 ^ (P.rank a + 1) := by
    rw [show P.rank a + 3 = (P.rank a + 1) + 2 by omega, pow_add]
    norm_num
    omega
  rw [hp]
  omega

variable {Addr Scalar : List Bool → Type*} [∀ x, Add (Scalar x)] [∀ x, Mul (Scalar x)]

/-- A local machine interface. Its equations concern only one push/pop, one
instruction decoding, initialization, or publication of an already returned
scalar. It contains no theorem about full evaluation, determinants or languages. -/
structure LocalStackStepFP
    (P : ∀ x, EntryProgram (Addr x) (Scalar x)) (initial : ∀ x, Addr x)
    (output : ∀ x, Scalar x → Bool) where
  code : ∀ x, EntryConfig (Addr x) (Scalar x) → List Bool
  transition : List Bool → List Bool
  transition_FP : transition ∈ FP
  setup : ∀ x, transition (pair [] x) = code x (.eval (initial x) [])
  push_pop : ∀ x c, ¬c.Halted → transition (code x c) = code x ((P x).step c)
  publish : ∀ x v, transition (code x (.ret v [])) = [output x v]
  flag : ∀ x c, (code x c).headD false = decide c.Halted

variable {P : ∀ x, EntryProgram (Addr x) (Scalar x)} {initial : ∀ x, Addr x}
    {output : ∀ x, Scalar x → Bool}

/-- Before termination the compiled iteration is exactly the mathematical stack trace. -/
theorem LocalStackStepFP.iterate_code (I : LocalStackStepFP P initial output)
    (x : List Bool) (t : ℕ) (ht : t ≤ (P x).stop (initial x)) :
    I.transition^[t + 1] (pair [] x) = I.code x ((P x).step^[t] (.eval (initial x) [])) := by
  induction t with
  | zero => simpa using I.setup x
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih (by omega),
      I.push_pop x _ ((P x).not_halted_before _ t (by omega)), Function.iterate_succ_apply']

theorem LocalStackStepFP.iterate_publish (I : LocalStackStepFP P initial output) (x : List Bool) :
    I.transition^[((P x).stop (initial x) + 1) + 1] (pair [] x) =
      [output x ((P x).value (initial x))] := by
  rw [Function.iterate_succ_apply', I.iterate_code x _ le_rfl, EntryProgram.stop_result, I.publish]

/-- The complete, bounded trace is derived from the local implementation laws. -/
noncomputable def LocalStackStepFP.trace (I : LocalStackStepFP P initial output)
    (r w : Polynomial ℕ)
    (hinput : ∀ x : List Bool, (pair [] x).length ≤ r.eval x.length)
    (hcode : ∀ x t, (I.code x ((P x).step^[t] (.eval (initial x) []))).length ≤ r.eval x.length)
    (hone : ∀ n, 1 ≤ r.eval n)
    (hrank : ∀ x, (P x).rank (initial x) + 3 ≤ w.eval x.length) :
    StreamingTrace I.transition (fun x ↦ output x ((P x).value (initial x))) r w where
  state x t := I.transition^[t] (pair [] x)
  stop x := (P x).stop (initial x) + 1
  start _ := rfl
  step _ _ := Function.iterate_succ_apply' _ _ _
  length_le x t ht := by
    by_cases h0 : t = 0
    · subst t; exact hinput x
    by_cases hs : t ≤ (P x).stop (initial x) + 1
    · obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
      rw [I.iterate_code x u (by omega)]
      exact hcode x u
    · have he : t = ((P x).stop (initial x) + 1) + 1 := by omega
      rw [he, I.iterate_publish]
      exact hone x.length
  stop_pos _ := by omega
  stop_le x := (EntryProgram.stop_bound _ _).trans
    (Nat.pow_le_pow_right (by omega) (hrank x))
  running x t ht hs := by
    obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
    rw [I.iterate_code x u (by omega), I.flag]
    exact decide_eq_false ((P x).not_halted_before _ u (by omega))
  done x := by rw [I.iterate_code x _ le_rfl, I.flag, decide_eq_true (EntryProgram.halted_stop _ _)]
  answer_nonempty x := by rw [I.iterate_publish]; simp
  answer_eq x := by rw [I.iterate_publish]; rfl

/-- A PSPACE machine follows from local stack-step realization and internally
proved encoding/rank bounds. No correctness of full evaluation is an assumption. -/
theorem LocalStackStepFP.language_mem_PSPACE (I : LocalStackStepFP P initial output)
    (r w : Polynomial ℕ)
    (hinput : ∀ x : List Bool, (pair [] x).length ≤ r.eval x.length)
    (hcode : ∀ x t, (I.code x ((P x).step^[t] (.eval (initial x) []))).length ≤ r.eval x.length)
    (hone : ∀ n, 1 ≤ r.eval n)
    (hrank : ∀ x, (P x).rank (initial x) + 3 ≤ w.eval x.length) :
    {x | output x ((P x).value (initial x)) = true} ∈ PSPACE :=
  streamingLanguage_mem_PSPACE I.transition_FP (I.trace r w hinput hcode hone hrank)
    (fun _ ↦ Iff.rfl)

end SparseIrred.UpperBounds.Section4
