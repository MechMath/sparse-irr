import SparseIrred.UpperBounds.Machine.StreamingBinaryPow

/-! # A concrete linear-width sparse-term evaluation subroutine -/

namespace SparseIrred.UpperBounds.Machine

open Complexity BinaryRoutine

def termCoeffReg (k : ℕ) : Fin (6 + (3 + (1 + k))) :=
  (((0 : Fin 1).castAdd k).natAdd 3).natAdd 6

def termExtra {k : ℕ} (c : ℕ) (extra : Fin k → ℕ) : Fin (1 + k) → ℕ :=
  Fin.append ![c] extra

@[simp] theorem modReg_ne_termCoeffReg (k : ℕ) (i : Fin 6) :
    modReg (3 + (1 + k)) i ≠ termCoeffReg k := modReg_ne_extra _ _ _

@[simp] theorem termCoeffReg_ne_modReg (k : ℕ) (i : Fin 6) :
    termCoeffReg k ≠ modReg (3 + (1 + k)) i := (modReg_ne_termCoeffReg k i).symm

@[simp] theorem termCoeffReg_ne_powReg (k : ℕ) (i : Fin 3) :
    termCoeffReg k ≠ powReg (1 + k) i := by
  intro h
  have := congrArg Fin.val h
  simp [termCoeffReg, powReg] at this
  omega

@[simp] theorem powReg_ne_termCoeffReg (k : ℕ) (i : Fin 3) :
    powReg (1 + k) i ≠ termCoeffReg k := (termCoeffReg_ne_powReg k i).symm

@[simp] theorem framedModInput_coeff {k : ℕ} (n m r d z a e i c : ℕ)
    (extra : Fin k → ℕ) :
    framedModInput n m r d z (powExtra a e i (termExtra c extra)) (termCoeffReg k) = c := by
  simp [termCoeffReg, powExtra, termExtra]

/-- Following modular exponentiation, multiply by the coefficient magnitude
and reduce again, reusing exactly the same arithmetic work tapes. -/
def binaryTermFinish (k : ℕ) : BinaryRoutine (6 + (3 + (1 + k))) :=
  seq (seq (mulAdd (termCoeffReg k) (modReg (3 + (1 + k)) 2)
      (modReg (3 + (1 + k)) 0) (modReg (3 + (1 + k)) 3) (modReg (3 + (1 + k)) 4))
    (framedMod (3 + (1 + k)))) (binaryPowClean (1 + k))

/-- Evaluate a single sparse term without expanding its exponent. -/
def binaryTerm (k : ℕ) : BinaryRoutine (6 + (3 + (1 + k))) :=
  seq (binaryPow (1 + k)) (binaryTermFinish k)

theorem binaryTermFinish_sound (k : ℕ) : (binaryTermFinish k).Sound :=
  ((mulAdd_sound _ _ _ _ _).seq (framedMod_sound _)).seq (binaryPowClean_sound _)

theorem binaryTerm_sound (k : ℕ) : (binaryTerm k).Sound :=
  (binaryPow_sound _).seq (binaryTermFinish_sound _)

theorem binaryTermMul_effect {k : ℕ} (a m e c : ℕ) (extra : Fin k → ℕ) :
    (mulAdd (termCoeffReg k) (modReg (3 + (1 + k)) 2) (modReg (3 + (1 + k)) 0)
      (modReg (3 + (1 + k)) 3) (modReg (3 + (1 + k)) 4)).effect
        (binaryPowValues a m e e (termExtra c extra)) =
      framedModInput (c * (a ^ e % m)) m (a ^ e % m) 0 0
        (powExtra a e e (termExtra c extra)) := by
  funext j
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
  · change (mulAdd _ _ _ _ _).effect _ (modReg (3 + (1 + k)) j) =
      framedModInput _ _ _ _ _ _ (modReg (3 + (1 + k)) j)
    fin_cases j <;> simp [mulAdd, binaryPowValues]
  · simp [mulAdd, binaryPowValues]

theorem binaryTermFinish_requires {k : ℕ} (a m e c : ℕ) (extra : Fin k → ℕ) (hm : 0 < m) :
    (binaryTermFinish k).requires (binaryPowValues a m e e (termExtra c extra)) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine ⟨?_, by simp [binaryPowValues], by simp [binaryPowValues]⟩
    constructor <;> simp
  · rw [binaryTermMul_effect]
    exact framedMod_requires _ _ _ _ _ _ hm
  · simp [binaryPowClean, seq, clear]

theorem binaryTermFinish_effect {k : ℕ} (a m e c : ℕ) (extra : Fin k → ℕ) (hm : 0 < m) :
    (binaryTermFinish k).effect (binaryPowValues a m e e (termExtra c extra)) =
      framedModInput 0 m ((c * a ^ e) % m) 0 0 (powExtra a e e (termExtra c extra)) := by
  change (binaryPowClean (1 + k)).effect ((framedMod (3 + (1 + k))).effect (_)) = _
  rw [binaryTermMul_effect, framedMod_effect _ _ _ _ _ _ hm, binaryPowClean_effect]
  have heq : (c * (a ^ e % m)) % m = (c * a ^ e) % m := by simp [Nat.mul_mod]
  rw [heq]

theorem binaryTerm_requires {k : ℕ} (n m r d z a e i c : ℕ) (extra : Fin k → ℕ)
    (hm : 0 < m) :
    (binaryTerm k).requires
      (framedModInput n m r d z (powExtra a e i (termExtra c extra))) := by
  refine ⟨binaryPow_requires _ _ _ _ _ _ _ _ _ hm, ?_⟩
  rw [binaryPow_effect _ _ _ _ _ _ _ _ _ hm]
  exact binaryTermFinish_requires _ _ _ _ _ hm

/-- Exact modular evaluation of a sparse monomial. No exponential-size power
is ever materialized by the machine. -/
theorem binaryTerm_effect {k : ℕ} (n m r d z a e i c : ℕ) (extra : Fin k → ℕ)
    (hm : 0 < m) :
    (binaryTerm k).effect
      (framedModInput n m r d z (powExtra a e i (termExtra c extra))) =
      framedModInput 0 m ((c * a ^ e) % m) 0 0 (powExtra a e e (termExtra c extra)) := by
  change (binaryTermFinish k).effect ((binaryPow (1 + k)).effect _) = _
  rw [binaryPow_effect _ _ _ _ _ _ _ _ _ hm, binaryTermFinish_effect _ _ _ _ _ hm]

theorem binaryTermFinish_space {k : ℕ} (a m e c : ℕ → ℕ) (extra : ℕ → Fin k → ℕ)
    (hm : ∀ j, 0 < m j) (S W : ℕ → ℕ)
    (hcW : ∀ j, c j ≤ W j) (hmW : ∀ j, m j < W j)
    (hcmW : ∀ j, c j * m j < W j) :
    SpaceBoundByWidthAt (binaryTermFinish k) S
      (fun j ↦ binaryPowValues (a j) (m j) (e j) (e j) (termExtra (c j) (extra j))) W := by
  have hr : ∀ j, a j ^ e j % m j < m j := fun j ↦ Nat.mod_lt _ (hm j)
  have hp : ∀ j, c j * (a j ^ e j % m j) < W j := by
    intro j
    have := hcmW j
    have := hr j
    nlinarith
  apply SpaceBoundByWidthAt.seq
  · apply SpaceBoundByWidthAt.seq
    · apply SpaceBoundByWidthAt.mulAdd
      · intro j; simpa [binaryPowValues] using hcW j
      · intro j
        simpa [binaryPowValues] using Nat.le_of_lt ((hr j).trans (hmW j))
      · intro j
        have hle : c j * (a j ^ e j % m j) + c j ≤ W j := by
          have := hr j
          have := hcmW j
          nlinarith
        simpa [binaryPowValues] using hle
    · have heq : (fun j ↦
          (mulAdd (termCoeffReg k) (modReg (3 + (1 + k)) 2) (modReg (3 + (1 + k)) 0)
            (modReg (3 + (1 + k)) 3) (modReg (3 + (1 + k)) 4)).effect
            (binaryPowValues (a j) (m j) (e j) (e j) (termExtra (c j) (extra j)))) =
          (fun j ↦ framedModInput (c j * (a j ^ e j % m j)) (m j) (a j ^ e j % m j)
            0 0 (powExtra (a j) (e j) (e j) (termExtra (c j) (extra j)))) :=
        funext (fun j ↦ binaryTermMul_effect _ _ _ _ _)
      rw [heq]
      exact framedMod_space _ _ _ _ _ _ hm S W hp hmW
        (fun j ↦ Nat.le_of_lt ((hr j).trans (hmW j)))
        (fun _ ↦ Nat.zero_le _) (fun _ ↦ Nat.zero_le _)
  · have heq : (fun j ↦
        (seq (mulAdd (termCoeffReg k) (modReg (3 + (1 + k)) 2) (modReg (3 + (1 + k)) 0)
          (modReg (3 + (1 + k)) 3) (modReg (3 + (1 + k)) 4)) (framedMod (3 + (1 + k)))).effect
          (binaryPowValues (a j) (m j) (e j) (e j) (termExtra (c j) (extra j)))) =
        (fun j ↦ framedModValues (c j * (a j ^ e j % m j)) (m j)
          (c j * (a j ^ e j % m j)) (powExtra (a j) (e j) (e j) (termExtra (c j) (extra j)))) := by
      funext j
      change (framedMod (3 + (1 + k))).effect (_) = _
      rw [binaryTermMul_effect, framedMod_effect _ _ _ _ _ _ (hm j)]
    rw [heq]
    apply binaryPowClean_space
    · intro j; simpa [binaryModValues] using Nat.le_of_lt (hp j)
    · intro j
      simp only [framedModValues_reg, binaryModValues]
      simp
      have := hmW j
      omega
    · intro j; simpa [binaryModValues] using Nat.le_of_lt (hp j)

/-- A sparse term is evaluated using space linear in the widths of the input
registers and the products `a*m`, `c*m`; the exponent contributes only its
binary width. -/
theorem binaryTerm_space {k : ℕ} (n m r d z a e i c : ℕ → ℕ)
    (extra : ℕ → Fin k → ℕ) (hm : ∀ j, 0 < m j) (S W : ℕ → ℕ)
    (hn : ∀ j, n j ≤ W j) (hmW : ∀ j, m j < W j)
    (hr : ∀ j, r j ≤ W j) (hd : ∀ j, d j ≤ W j) (hz : ∀ j, z j ≤ W j)
    (hi : ∀ j, i j ≤ W j) (haW : ∀ j, a j ≤ W j)
    (hamW : ∀ j, a j * m j < W j) (heW : ∀ j, e j ≤ W j)
    (hcW : ∀ j, c j ≤ W j) (hcmW : ∀ j, c j * m j < W j) :
    SpaceBoundByWidthAt (binaryTerm k) S
      (fun j ↦ framedModInput (n j) (m j) (r j) (d j) (z j)
        (powExtra (a j) (e j) (i j) (termExtra (c j) (extra j)))) W := by
  apply SpaceBoundByWidthAt.seq
  · exact binaryPow_space _ _ _ _ _ _ _ _ _ hm S W hn hmW hr hd hz hi haW hamW heW
  · have heq : (fun j ↦ (binaryPow (1 + k)).effect
        (framedModInput (n j) (m j) (r j) (d j) (z j)
          (powExtra (a j) (e j) (i j) (termExtra (c j) (extra j))))) =
        (fun j ↦ binaryPowValues (a j) (m j) (e j) (e j) (termExtra (c j) (extra j))) :=
      funext (fun j ↦ binaryPow_effect _ _ _ _ _ _ _ _ _ (hm j))
    rw [heq]
    exact binaryTermFinish_space a m e c extra hm S W hcW hmW hcmW

end SparseIrred.UpperBounds.Machine
