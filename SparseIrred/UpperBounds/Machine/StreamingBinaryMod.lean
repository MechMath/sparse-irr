import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Arithmetic
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Control
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.SpaceBounds
import Mathlib.Tactic.FinCases

/-!
# A linear-space modular arithmetic machine

The six canonical binary registers contain dividend, modulus, remainder,
countdown, loop counter, and a reusable copy scratch register. The machine may
take exponential time in the binary input length; its work space is bounded
by the register widths independently of the number of iterations.
-/

namespace SparseIrred.UpperBounds.Machine

open Complexity BinaryRoutine

/-- Reset the remainder cycle after its countdown reaches zero. -/
def binaryModReset : BinaryRoutine 6 :=
  seq (seq (binaryCopy 1 3 5) (binaryPred 3)) (clear 2)

/-- Advance one dividend unit, maintaining a remainder and a countdown. -/
def binaryModBody : BinaryRoutine 6 :=
  branchZero 3 binaryModReset (seq (binaryPred 3) (binarySucc 2))

/-- A deterministic modular-reduction loop with binary controller tapes. -/
def binaryModLoop : BinaryRoutine 6 := binaryFor binaryModBody 4 0

theorem binaryModReset_sound : binaryModReset.Sound :=
  ((binaryCopy_sound 1 3 5).seq (binaryPred_sound 3)).seq (clear_sound 2)

theorem binaryModBody_sound : binaryModBody.Sound :=
  binaryModReset_sound.branchZero ((binaryPred_sound 3).seq (binarySucc_sound 2)) 3

theorem binaryModLoop_sound : binaryModLoop.Sound :=
  binaryModBody_sound.binaryFor 4 0

/-- Exact register values after processing `i` dividend units. -/
def binaryModValues (n m i : ℕ) : BinaryValues 6 :=
  ![n, m, i % m, m - 1 - i % m, i, 0]

private theorem binaryMod_successor (m i : ℕ) (hm : 0 < m) :
    (i + 1) % m = if m - 1 - i % m = 0 then 0 else i % m + 1 := by
  have hr := Nat.mod_lt i hm
  have hmod : (i + 1) % m = (i % m + 1) % m := by simp [Nat.add_mod]
  rw [hmod]
  split_ifs with h
  · have heq : i % m + 1 = m := by omega
    simp [heq]
  · exact Nat.mod_eq_of_lt (by omega)

theorem binaryModBody_requires (n m i : ℕ) (hm : 0 < m) :
    binaryModBody.requires (binaryModValues n m i) := by
  by_cases h : m - 1 - i % m = 0
  · simp [binaryModBody, branchZero, binaryModValues, h, binaryModReset, seq,
      binaryCopy, binaryPred, clear, hm]
  · simp [binaryModBody, branchZero, binaryModValues, h, seq, binaryPred, binarySucc]
    omega

theorem binaryModBody_step (n m i : ℕ) (hm : 0 < m) :
    binaryForStep binaryModBody 4 (binaryModValues n m i) =
      binaryModValues n m (i + 1) := by
  have hmod := binaryMod_successor m i hm
  have hr := Nat.mod_lt i hm
  by_cases h : m - 1 - i % m = 0
  · simp only [h, ite_true] at hmod
    funext j
    fin_cases j <;>
      simp [binaryForStep, binaryModBody, branchZero, binaryModValues, h,
        binaryModReset, seq, binaryCopy, binaryPred, clear, hmod]
  · simp only [h, ite_false] at hmod
    funext j
    fin_cases j <;>
      simp [binaryForStep, binaryModBody, branchZero, binaryModValues, h,
        seq, binaryPred, binarySucc, hmod]
    omega

theorem binaryModBody_preserves (n m i : ℕ) (_hm : 0 < m) :
    binaryModBody.effect (binaryModValues n m i) 4 = i ∧
      binaryModBody.effect (binaryModValues n m i) 0 = n := by
  by_cases h : m - 1 - i % m = 0 <;>
    simp [binaryModBody, branchZero, binaryModValues, h, binaryModReset, seq,
      binaryCopy, binaryPred, clear, binarySucc]

theorem binaryModLoop_values (n m i : ℕ) (hm : 0 < m) :
    binaryForValues binaryModBody 4 (binaryModValues n m 0) i =
      binaryModValues n m i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [binaryForValues, ih, binaryModBody_step n m i hm]

theorem binaryModLoop_requires (n m : ℕ) (hm : 0 < m) :
    binaryModLoop.requires (binaryModValues n m 0) := by
  refine ⟨by decide, by simp [binaryModValues], ?_⟩
  intro i hi
  rw [binaryModLoop_values n m i hm]
  exact ⟨binaryModBody_requires n m i hm, (binaryModBody_preserves n m i hm).1,
    (binaryModBody_preserves n m i hm).2⟩

/-- Correctness of the concrete modular-reduction loop. -/
theorem binaryModLoop_effect (n m : ℕ) (hm : 0 < m) :
    binaryModLoop.effect (binaryModValues n m 0) = binaryModValues n m n := by
  change binaryForValues binaryModBody 4 (binaryModValues n m 0)
    (binaryForCount 4 0 (binaryModValues n m 0)) = _
  simp only [binaryForCount, binaryModValues, Matrix.cons_val_zero,
    Matrix.cons_val_four]
  exact binaryModLoop_values n m n hm

/-- Every invocation of the modular update uses only a constant multiple of
the binary width of its registers. -/
theorem binaryModBody_space {S W : ℕ → ℕ} {v : ℕ → BinaryValues 6}
    (hW : ∀ j, 1 ≤ W j) (hv : ∀ j i, v j i ≤ W j) :
    SpaceBoundByWidthAt binaryModBody S v W := by
  apply SpaceBoundByWidthAt.branchZero
  · apply SpaceBoundByWidthAt.seq
    · apply SpaceBoundByWidthAt.seq
      · exact SpaceBoundByWidthAt.binaryCopy 1 3 5 (fun j ↦ hv j 1) (fun j ↦ hv j 3)
      · apply SpaceBoundByWidthAt.binaryPred
        intro j
        simp only [binaryCopy, Function.update_self]
        have := hv j 1
        have := hW j
        omega
    · apply SpaceBoundByWidthAt.clear
      intro j
      simpa [seq, binaryCopy, binaryPred] using hv j 2
  · apply SpaceBoundByWidthAt.seq
    · apply SpaceBoundByWidthAt.binaryPred
      intro j
      have := hv j 3
      have := hW j
      omega
    · apply SpaceBoundByWidthAt.binarySucc
      intro j
      simpa [binaryPred] using hv j 2

theorem binaryModValues_le (n m i : ℕ) (hm : 0 < m) (hi : i ≤ n) (j : Fin 6) :
    binaryModValues n m i j ≤ max n m + 1 := by
  have hr := Nat.mod_lt i hm
  have hn := le_max_left n m
  have hm' := le_max_right n m
  fin_cases j <;> simp [binaryModValues] <;> omega

/-- The complete loop has an all-prefix space bound linear in the binary
width of the dividend and modulus, with no factor for the iteration count. -/
theorem binaryModLoop_space (n m : ℕ → ℕ) (hm : ∀ j, 0 < m j) (S : ℕ → ℕ) :
    SpaceBoundByWidthAt binaryModLoop S
      (fun j ↦ binaryModValues (n j) (m j) 0) (fun j ↦ max (n j) (m j) + 1) := by
  apply SpaceBoundByWidthAt.binaryFor_of_clamped_body
  · intro j
    simp only [binaryModValues, Matrix.cons_val_zero]
    omega
  · intro j count hc
    rw [binaryModLoop_values _ _ _ (hm j)]
    apply binaryModValues_le _ _ _ (hm j) _ 4
    simpa [binaryForCount, binaryModValues] using Nat.le_of_lt hc
  · apply binaryModBody_space (fun _ ↦ by omega)
    intro code idx
    unfold binaryForClampedValues
    rw [binaryModLoop_values _ _ _ (hm _)]
    apply binaryModValues_le _ _ _ (hm _)
    simp [binaryForCount, binaryModValues]

end SparseIrred.UpperBounds.Machine
