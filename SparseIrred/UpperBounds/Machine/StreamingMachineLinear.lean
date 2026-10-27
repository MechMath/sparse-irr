import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.SpaceBounds
import Complexitylib.Models.TuringMachine.Hoare.Space
import Mathlib.Data.Nat.Size

/-! # From binary-register width certificates to linear machine space -/

namespace SparseIrred.UpperBounds.Machine

open Complexity BinaryRoutine

/-- A fixed affine enlargement of numeric values increases their binary
width by only a fixed additive constant. -/
theorem size_mul_add_le (K W : ℕ) : (K * W + K).size ≤ W.size + K.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  have hK := Nat.lt_size_self K
  have hW := Nat.lt_size_self W
  have hWp : 0 < 2 ^ W.size := Nat.two_pow_pos _
  nlinarith

/-- Fixed numeric slack in a binary-width certificate is absorbed in its
constant; it does not increase the asymptotic workspace. -/
theorem spaceWidth_mul_add {k : ℕ} {R : BinaryRoutine k} {S W : ℕ → ℕ}
    {v : ℕ → BinaryValues k} (K : ℕ)
    (h : SpaceBoundByWidthAt R S v (fun j ↦ K * W j + K)) :
    SpaceBoundByWidthAt R S v W := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C * (K.size + 1), fun j ↦ ?_⟩
  have hs := Nat.mul_le_mul_left C (size_mul_add_le K (W j))
  have hc := hC j
  dsimp only at hc
  nlinarith [Nat.zero_le (C * K.size * (W j).size)]

theorem spaceWidth_add_const {k : ℕ} {R : BinaryRoutine k} {S W : ℕ → ℕ}
    {v : ℕ → BinaryValues k} (K : ℕ)
    (h : SpaceBoundByWidthAt R S v (fun j ↦ W j + K)) :
    SpaceBoundByWidthAt R S v W := by
  apply spaceWidth_mul_add (K + 1)
  exact h.mono (fun j ↦ by nlinarith [Nat.zero_le (K * W j)])

/-- A fixed power of a natural bound still has linear binary width. -/
theorem size_pow_add_one_le (d W : ℕ) (hd : 0 < d) :
    ((W + 1) ^ d).size ≤ d * W.size + d := by
  have hpow : ((W + 1) ^ d).size ≤ (W + 1).size * d := by
    apply Nat.size_le.mpr
    have h := Nat.pow_lt_pow_left (Nat.lt_size_self (W + 1)) (Nat.ne_of_gt hd)
    simpa only [← pow_mul] using h
  have hsize : (W + 1).size ≤ W.size + 1 := by
    simpa using size_mul_add_le 1 W
  have hmul := Nat.mul_le_mul_right d hsize
  nlinarith

/-- Polynomial numeric envelopes are absorbed in the constant of a
binary-width space certificate. -/
theorem spaceWidth_pow_add_one {k : ℕ} {R : BinaryRoutine k} {S W : ℕ → ℕ}
    {v : ℕ → BinaryValues k} (d : ℕ) (hd : 0 < d)
    (h : SpaceBoundByWidthAt R S v (fun j ↦ (W j + 1) ^ d)) :
    SpaceBoundByWidthAt R S v W := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C * (d + 1), fun j ↦ ?_⟩
  have hs := Nat.mul_le_mul_left C (size_pow_add_one_le d (W j) hd)
  have hc := hC j
  dsimp only at hc
  nlinarith [Nat.zero_le (C * (W j).size)]

/-- Exponentially bounded register values require only linearly many bits. -/
theorem register_size_le_linear {W : ℕ → ℕ} (a b : ℕ)
    (hW : ∀ L, W L ≤ 2 ^ (a * L + b)) :
    ∀ L, (W L).size ≤ a * L + (b + 1) := by
  intro L
  have h := Nat.size_le_size (hW L)
  rw [Nat.size_pow] at h
  omega

/-- Convert a composed routine's binary-width certificate into an explicit
linear function of the original input length. -/
theorem binaryRoutine_space_le_linear {k : ℕ} {R : BinaryRoutine k}
    {S W : ℕ → ℕ} {v : ℕ → BinaryValues k}
    (hspace : SpaceBoundByWidthAt R S v W) (a b c d : ℕ)
    (hS : ∀ L, S L ≤ a * L + b) (hW : ∀ L, (W L).size ≤ c * L + d) :
    ∃ A B, ∀ L, R.spaceBound (S L) (v L) ≤ A * L + B := by
  obtain ⟨K, hK⟩ := hspace
  refine ⟨a + K * c, b + K * d + K, fun L ↦ ?_⟩
  have hmul := Nat.mul_le_mul_left K (hW L)
  have := hS L
  have := hK L
  nlinarith

/-- The linear bound holds for every actual machine configuration, not just
for the register states at iteration boundaries. -/
theorem binaryRoutine_linear_hoareSpace {k : ℕ} {R : BinaryRoutine k}
    {S W : ℕ → ℕ} {v : ℕ → BinaryValues k}
    (hsound : R.Sound) (hspace : SpaceBoundByWidthAt R S v W) (a b c d : ℕ)
    (hS : ∀ L, S L ≤ a * L + b) (hW : ∀ L, (W L).size ≤ c * L + d) :
    ∃ A B, ∀ L (inp : Tape) (ys : List Bool), R.requires (v L) →
      TM.Parked inp → 1 ≤ S L → inp.head ≤ L + S L + 1 →
      R.machine.HoareTimeSpace (CanonicalPred inp (v L) ys)
        (CanonicalPred inp (R.effect (v L)) (ys ++ R.emitted (v L)))
        (R.timeBound (v L)) L (A * L + B) := by
  obtain ⟨A, B, hbound⟩ := binaryRoutine_space_le_linear hspace a b c d hS hW
  refine ⟨A, B, fun L inp ys hreq hinp hSpos hinpBound ↦ ?_⟩
  have h := hsound.hoareTimeSpace (v L) inp ys L (S L) hreq hinp hSpos hinpBound
  exact ⟨h.1, h.2.mono le_rfl (hbound L)⟩

end SparseIrred.UpperBounds.Machine
