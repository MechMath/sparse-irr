import SparseIrred.UpperBounds.Section4.Decision

/-!
# Counter-state execution of sequential searches

The local predicate call is left as a call to its verified evaluator. The search
control has two natural-number registers and one Boolean register. All prefixes,
including prefixes beyond termination, satisfy the same binary register bounds.
-/

namespace SparseIrred.UpperBounds.Section4

structure ScanState where
  next : ℕ
  remaining : ℕ
  found : Bool
  deriving DecidableEq

/-- One search-control step, with halting states made stationary. -/
def scanStep (test : ℕ → Bool) (s : ScanState) : ScanState :=
  if s.found then s
  else if s.remaining = 0 then s
  else if test s.next then ⟨s.next, 0, true⟩
  else ⟨s.next + 1, s.remaining - 1, false⟩

def ScanState.initial (start count : ℕ) : ScanState := ⟨start, count, false⟩

@[simp] theorem scanStep_found (test : ℕ → Bool) (s : ScanState) (h : s.found = true) :
    scanStep test s = s := by simp [scanStep, h]

@[simp] theorem scanStep_empty (test : ℕ → Bool) (s : ScanState) (h : s.remaining = 0) :
    scanStep test s = s := by simp [scanStep, h]

theorem scanStep_iterate_empty (test : ℕ → Bool) (s : ScanState)
    (h : s.remaining = 0) (t : ℕ) : (scanStep test)^[t] s = s := by
  exact Function.iterate_fixed (scanStep_empty test s h) t

/-- The concrete counter loop terminates within the declared number of candidates
and returns the same result as the tail-recursive search. -/
theorem scanStep_run (test : ℕ → Bool) (count start : ℕ) :
    ((scanStep test)^[count] (.initial start count)).remaining = 0 ∧
      ((scanStep test)^[count] (.initial start count)).found = scanAny test count start := by
  induction count generalizing start with
  | zero => simp [ScanState.initial, scanAny]
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      by_cases h : test start = true
      · have hs : scanStep test (.initial start (n + 1)) = ⟨start, 0, true⟩ := by
          simp [scanStep, ScanState.initial, h]
        rw [hs, scanStep_iterate_empty test _ rfl]
        simp [scanAny, h]
      · have hs : scanStep test (.initial start (n + 1)) = .initial (start + 1) n := by
          simp [scanStep, ScanState.initial, h]
        rw [hs]
        simpa [scanAny, h] using ih (start + 1)

/-- The two counters stay inside the original interval and original loop length. -/
def ScanState.Bounded (start count : ℕ) (s : ScanState) : Prop :=
  start ≤ s.next ∧ s.next + s.remaining ≤ start + count ∧ s.remaining ≤ count

theorem scanStep_bounded (test : ℕ → Bool) (start count : ℕ) (s : ScanState)
    (h : s.Bounded start count) : (scanStep test s).Bounded start count := by
  unfold scanStep
  split_ifs with hf he ht
  · exact h
  · exact h
  · rcases h with ⟨h₁, h₂, h₃⟩
    simp only [ScanState.Bounded]
    omega
  · rcases h with ⟨h₁, h₂, h₃⟩
    simp only [ScanState.Bounded]
    omega

/-- This invariant covers every execution prefix, not only the final state. -/
theorem scanStep_iterate_bounded (test : ℕ → Bool) (start count t : ℕ) :
    ((scanStep test)^[t] (.initial start count)).Bounded start count := by
  induction t with
  | zero => simp [ScanState.Bounded, ScanState.initial]
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact scanStep_bounded test start count _ ih

/-- Binary lengths of both loop counters are logarithmic in the search interval. -/
theorem scanStep_register_sizes (test : ℕ → Bool) (start count t : ℕ) :
    ((scanStep test)^[t] (.initial start count)).next.size ≤ (start + count).size ∧
      ((scanStep test)^[t] (.initial start count)).remaining.size ≤ count.size := by
  have h := scanStep_iterate_bounded test start count t
  exact ⟨Nat.size_le_size (by have := h.2.1; omega), Nat.size_le_size h.2.2⟩

/-- A completed bounded run answers the exact existential search question. -/
theorem scanStep_run_found_iff (test : ℕ → Bool) (start count : ℕ) :
    ((scanStep test)^[count] (.initial start count)).found = true ↔
      ∃ i, start ≤ i ∧ i < start + count ∧ test i = true := by
  rw [(scanStep_run test count start).2, scanAny_eq_true_iff]

end SparseIrred.UpperBounds.Section4
