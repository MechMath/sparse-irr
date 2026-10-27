import SparseIrred.UpperBounds.Section4.EntryMachineUniformEncoding
import SparseIrred.UpperBounds.Section4.UniformStageBounds

/-!
# Theorem 18: the uniform encoded language is in PSPACE

All mathematical correctness, termination, and binary state bounds are internal
theorems. The sole parameter is the explicitly named low-level realization of
one local transition on the fixed, faithful binary encoding. It is an omitted
algorithm implementation, not a cited external theorem or the desired result.
-/

noncomputable section

namespace SparseIrred.UpperBounds.Section4

open Complexity Complexity.TM SparseIrred.UpperBounds.Machine

/-- The omitted low-level implementation obligation. This asks only for a local
binary step, not for a determinant/irreducibility oracle, a whole-run space bound,
or membership in PSPACE. The exact code is fixed by `uniformCode`.

The local operations are field arithmetic, binary counter/index arithmetic,
sparse coefficient queries, address decoding, stack push/pop, and phase dispatch.
Both primality and modulus irreducibility have already been expanded into the
internally verified staged computation; neither is a primitive of this interface. -/
structure UniformLocalStepRealization (G : List Bool → List Bool) : Prop where
  polynomial_time : G ∈ FP
  initialize_state : ∀ s, G (pair [] s) = uniformCode s (uniformStages s).initial
  step : ∀ s c, ¬c.Halted → G (uniformCode s c) = uniformCode s ((uniformStages s).step c)
  publish : ∀ s b, G (uniformCode s (.done b)) = [b]

/-- The local interface supplies no space or correctness claim about a full run. -/
def UniformLocalStepRealization.control {G : List Bool → List Bool}
    (h : UniformLocalStepRealization G) : LocalControlStepFP uniformStages where
  code := uniformCode
  transition := G
  transition_FP := h.polynomial_time
  setup := h.initialize_state
  local_step := h.step
  publish := h.publish
  flag := uniformCode_flag

def uniformStatePolynomial : Polynomial ℕ :=
  Polynomial.C 2000000 * (Polynomial.X + Polynomial.C 3) ^ 8

@[simp] theorem uniformStatePolynomial_eval (L : ℕ) :
    uniformStatePolynomial.eval L = 2000000 * (L + 3) ^ 8 := by
  simp [uniformStatePolynomial]

theorem uniformStatePolynomial_input (s : List Bool) :
    (pair [] s).length ≤ uniformStatePolynomial.eval s.length := by
  rw [uniformStatePolynomial_eval, pair_length]
  simp only [List.length_nil]
  have hp : s.length + 3 ≤ (s.length + 3) ^ 8 := le_self_pow₀ (by omega) (by decide)
  omega

theorem uniformStatePolynomial_pos (L : ℕ) : 1 ≤ uniformStatePolynomial.eval L := by
  rw [uniformStatePolynomial_eval]
  have hp : 0 < (L + 3) ^ 8 := by positivity
  omega

/-- A full bounded trace follows from the local step laws; no trace certificate is assumed. -/
def uniformStreamingTrace {G : List Bool → List Bool} (h : UniformLocalStepRealization G) :
    StreamingTrace G (fun s ↦ (uniformStages s).answer) uniformStatePolynomial uniformTimeExponent :=
  h.control.trace uniformStageWorkBound uniformStages_work_bound
    uniformStatePolynomial uniformTimeExponent uniformStatePolynomial_input
    (fun s c ↦ by
      change (uniformCode s c).length ≤ uniformStatePolynomial.eval s.length
      simpa only [uniformStatePolynomial_eval] using uniformCode_length s c)
    uniformStatePolynomial_pos uniformStages_time_budget

/-- Theorem 18 for the concrete uniform binary language. The remaining premise
is only the permitted low-level single-step realization, explicitly distinguished
from a literature theorem. There are no additional mathematical premises. -/
theorem section4_irreducibility_mem_PSPACE {G : List Bool → List Bool}
    (h : UniformLocalStepRealization G) : UniformIrredLang ∈ PSPACE :=
  streamingLanguage_mem_PSPACE h.polynomial_time (uniformStreamingTrace h)
    (fun s ↦ (uniformStages_correct s).symm)

/-- The PSPACE proof constructs a deterministic multitape machine. Its bound
covers every reachable configuration, including the low-level work used inside
each polynomial-time step, and its final bit is the specified uniform decision. -/
theorem section4_machine_exists {G : List Bool → List Bool} (h : UniformLocalStepRealization G) :
    ∃ (k : ℕ) (M : TM k) (q : Polynomial ℕ),
      (∀ s c, M.reaches (M.initCfg s) c → c.WithinDecisionSpace s.length (q.eval s.length)) ∧
      (∀ s, ∃ c, M.reaches (M.initCfg s) c ∧ M.halted c ∧
        c.output.cells 1 = Γ.ofBool (uniformDecision s)) := by
  obtain ⟨k, M, q, hspace, hhalt⟩ :=
    streamingMachine_exists h.polynomial_time (uniformStreamingTrace h)
  refine ⟨k, M, q, hspace, fun s ↦ ?_⟩
  simpa only [uniformStages_answer_eq] using hhalt s

end SparseIrred.UpperBounds.Section4
