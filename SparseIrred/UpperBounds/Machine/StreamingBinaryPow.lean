import SparseIrred.UpperBounds.Machine.StreamingBinaryFramed

/-! # Modular powers on reusable binary registers -/

namespace SparseIrred.UpperBounds.Machine

open Complexity BinaryRoutine

def powReg (k : ℕ) (i : Fin 3) : Fin (6 + (3 + k)) := (i.castAdd k).natAdd 6

@[simp] theorem powReg_inj (k : ℕ) (i j : Fin 3) : powReg k i = powReg k j ↔ i = j := by
  simp [powReg]

@[simp] theorem modReg_ne_powReg (k : ℕ) (i : Fin 6) (j : Fin 3) :
    modReg (3 + k) i ≠ powReg k j := modReg_ne_extra _ _ _

@[simp] theorem powReg_ne_modReg (k : ℕ) (i : Fin 6) (j : Fin 3) :
    powReg k j ≠ modReg (3 + k) i := (modReg_ne_powReg k i j).symm

def powExtra {k : ℕ} (a e i : ℕ) (extra : Fin k → ℕ) : Fin (3 + k) → ℕ :=
  Fin.append ![a, e, i] extra

@[simp] theorem powExtra_left {k : ℕ} (a e i : ℕ) (extra : Fin k → ℕ) (j : Fin 3) :
    powExtra a e i extra (j.castAdd k) = ![a, e, i] j := Fin.append_left _ _ _

def binaryPowValues {k : ℕ} (a m e i : ℕ) (extra : Fin k → ℕ) :
    BinaryValues (6 + (3 + k)) :=
  framedModInput 0 m (a ^ i % m) 0 0 (powExtra a e i extra)

@[simp] theorem framedModInput_powReg {k : ℕ} (n m r d c a e i : ℕ)
    (extra : Fin k → ℕ) (j : Fin 3) :
    framedModInput n m r d c (powExtra a e i extra) (powReg k j) = ![a, e, i] j := by
  simp [powReg]

@[simp] theorem framedModValues_powReg {k : ℕ} (n m t a e i : ℕ)
    (extra : Fin k → ℕ) (j : Fin 3) :
    framedModValues n m t (powExtra a e i extra) (powReg k j) = ![a, e, i] j := by
  simp [powReg]

/-- Clear modular-arithmetic scratch registers between calls. -/
def binaryPowClean (k : ℕ) : BinaryRoutine (6 + (3 + k)) :=
  seq (seq (clear (modReg (3 + k) 0)) (clear (modReg (3 + k) 3)))
    (clear (modReg (3 + k) 4))

/-- One multiplication followed by modular reduction; all scratch tapes are
reused and cleared before the next pass. -/
def binaryPowBody (k : ℕ) : BinaryRoutine (6 + (3 + k)) :=
  seq (seq (mulAdd (powReg k 0) (modReg (3 + k) 2) (modReg (3 + k) 0)
    (modReg (3 + k) 3) (modReg (3 + k) 4)) (framedMod (3 + k))) (binaryPowClean k)

def binaryPowLoop (k : ℕ) : BinaryRoutine (6 + (3 + k)) :=
  binaryFor (binaryPowBody k) (powReg k 2) (powReg k 1)

theorem binaryPowClean_sound (k : ℕ) : (binaryPowClean k).Sound :=
  ((clear_sound _).seq (clear_sound _)).seq (clear_sound _)

theorem binaryPowBody_sound (k : ℕ) : (binaryPowBody k).Sound :=
  ((mulAdd_sound _ _ _ _ _).seq (framedMod_sound _)).seq (binaryPowClean_sound _)

theorem binaryPowLoop_sound (k : ℕ) : (binaryPowLoop k).Sound :=
  (binaryPowBody_sound k).binaryFor _ _

theorem binaryPowClean_effect {k : ℕ} (n m i a e t : ℕ) (extra : Fin k → ℕ) :
    (binaryPowClean k).effect (framedModValues n m i (powExtra a e t extra)) =
      framedModInput 0 m (i % m) 0 0 (powExtra a e t extra) := by
  funext j
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
  · change (binaryPowClean k).effect _ (modReg (3 + k) j) =
      framedModInput 0 m (i % m) 0 0 (powExtra a e t extra) (modReg (3 + k) j)
    fin_cases j <;> simp [binaryPowClean, seq, clear, binaryModValues]
  · simp [binaryPowClean, seq, clear]

theorem binaryPowMul_effect {k : ℕ} (a m e i : ℕ) (extra : Fin k → ℕ) :
    (mulAdd (powReg k 0) (modReg (3 + k) 2) (modReg (3 + k) 0)
      (modReg (3 + k) 3) (modReg (3 + k) 4)).effect (binaryPowValues a m e i extra) =
      framedModInput (a * (a ^ i % m)) m (a ^ i % m) 0 0 (powExtra a e i extra) := by
  funext j
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
  · change (mulAdd (powReg k 0) (modReg (3 + k) 2) (modReg (3 + k) 0)
      (modReg (3 + k) 3) (modReg (3 + k) 4)).effect
        (binaryPowValues a m e i extra) (modReg (3 + k) j) =
          framedModInput _ _ _ _ _ _ (modReg (3 + k) j)
    fin_cases j <;> simp [mulAdd, binaryPowValues]
  · simp [mulAdd, binaryPowValues]

theorem binaryPowBody_requires {k : ℕ} (a m e i : ℕ) (extra : Fin k → ℕ) (hm : 0 < m) :
    (binaryPowBody k).requires (binaryPowValues a m e i extra) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine ⟨?_, by simp [binaryPowValues], by simp [binaryPowValues]⟩
    constructor <;> simp
  · rw [binaryPowMul_effect]
    exact framedMod_requires _ _ _ _ _ _ hm
  · simp [binaryPowClean, seq, clear]

theorem binaryPowBody_effect {k : ℕ} (a m e i : ℕ) (extra : Fin k → ℕ) (hm : 0 < m) :
    (binaryPowBody k).effect (binaryPowValues a m e i extra) =
      framedModInput 0 m (a ^ (i + 1) % m) 0 0 (powExtra a e i extra) := by
  change (binaryPowClean k).effect ((framedMod (3 + k)).effect (_)) = _
  rw [binaryPowMul_effect, framedMod_effect _ _ _ _ _ _ hm, binaryPowClean_effect]
  have hmod : (a * (a ^ i % m)) % m = a ^ (i + 1) % m := by
    simp [pow_succ, Nat.mul_mod, Nat.mul_comm]
  rw [hmod]

theorem binaryPowBody_step {k : ℕ} (a m e i : ℕ) (extra : Fin k → ℕ) (hm : 0 < m) :
    binaryForStep (binaryPowBody k) (powReg k 2) (binaryPowValues a m e i extra) =
      binaryPowValues a m e (i + 1) extra := by
  rw [binaryForStep, binaryPowBody_effect a m e i extra hm]
  simp only [binaryPowValues, framedModInput_powReg, Matrix.cons_val_two]
  funext j
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
  · change Function.update (framedModInput 0 m (a ^ (i + 1) % m) 0 0
        (powExtra a e i extra)) (powReg k 2) (i + 1) (modReg (3 + k) j) =
          framedModInput _ _ _ _ _ _ (modReg (3 + k) j)
    fin_cases j <;> simp
  · refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
    · change _ = framedModInput _ _ _ _ _ _ (powReg k j)
      fin_cases j <;> simp [powReg]
    · have hne : j.natAdd 3 ≠ (2 : Fin 3).castAdd k := by
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      simp [framedModInput, Fin.append, powExtra, powReg, hne]

theorem binaryPowBody_preserves {k : ℕ} (a m e i : ℕ) (extra : Fin k → ℕ) (hm : 0 < m) :
    (binaryPowBody k).effect (binaryPowValues a m e i extra) (powReg k 2) = i ∧
      (binaryPowBody k).effect (binaryPowValues a m e i extra) (powReg k 1) = e := by
  rw [binaryPowBody_effect a m e i extra hm]
  simp

theorem binaryPowLoop_values {k : ℕ} (a m e i : ℕ) (extra : Fin k → ℕ) (hm : 0 < m) :
    binaryForValues (binaryPowBody k) (powReg k 2) (binaryPowValues a m e 0 extra) i =
      binaryPowValues a m e i extra := by
  induction i with
  | zero => rfl
  | succ i ih => rw [binaryForValues, ih, binaryPowBody_step a m e i extra hm]

theorem binaryPowLoop_requires {k : ℕ} (a m e : ℕ) (extra : Fin k → ℕ) (hm : 0 < m) :
    (binaryPowLoop k).requires (binaryPowValues a m e 0 extra) := by
  refine ⟨by simp, by simp [binaryPowValues], ?_⟩
  intro i hi
  rw [binaryPowLoop_values a m e i extra hm]
  exact ⟨binaryPowBody_requires a m e i extra hm, (binaryPowBody_preserves a m e i extra hm).1,
    (binaryPowBody_preserves a m e i extra hm).2⟩

/-- Exact correctness of a deterministic modular exponentiation machine. -/
theorem binaryPowLoop_effect {k : ℕ} (a m e : ℕ) (extra : Fin k → ℕ) (hm : 0 < m) :
    (binaryPowLoop k).effect (binaryPowValues a m e 0 extra) = binaryPowValues a m e e extra := by
  change binaryForValues (binaryPowBody k) (powReg k 2) (binaryPowValues a m e 0 extra)
    (binaryForCount (powReg k 2) (powReg k 1) (binaryPowValues a m e 0 extra)) = _
  have hcount : binaryForCount (powReg k 2) (powReg k 1) (binaryPowValues a m e 0 extra) = e := by
    simp [binaryForCount, binaryPowValues]
  rw [hcount, binaryPowLoop_values a m e e extra hm]

theorem binaryPowClean_space {k : ℕ} {S W : ℕ → ℕ}
    {v : ℕ → BinaryValues (6 + (3 + k))}
    (h0 : ∀ j, v j (modReg (3 + k) 0) ≤ W j)
    (h3 : ∀ j, v j (modReg (3 + k) 3) ≤ W j)
    (h4 : ∀ j, v j (modReg (3 + k) 4) ≤ W j) :
    SpaceBoundByWidthAt (binaryPowClean k) S v W := by
  apply SpaceBoundByWidthAt.seq
  · apply SpaceBoundByWidthAt.seq
    · exact SpaceBoundByWidthAt.clear _ h0
    · apply SpaceBoundByWidthAt.clear
      intro j
      simpa [clear] using h3 j
  · apply SpaceBoundByWidthAt.clear
    intro j
    simpa [seq, clear] using h4 j

/-- A modular-power update has space proportional to the binary widths of
its modulus and one multiplication, rather than the unreduced power. -/
theorem binaryPowBody_space {k : ℕ} (a m e i : ℕ → ℕ) (extra : ℕ → Fin k → ℕ)
    (hm : ∀ j, 0 < m j) (S W : ℕ → ℕ)
    (haW : ∀ j, a j ≤ W j) (hmW : ∀ j, m j < W j)
    (hamW : ∀ j, a j * m j < W j) :
    SpaceBoundByWidthAt (binaryPowBody k) S
      (fun j ↦ binaryPowValues (a j) (m j) (e j) (i j) (extra j)) W := by
  have hr : ∀ j, a j ^ i j % m j < m j := fun j ↦ Nat.mod_lt _ (hm j)
  have hp : ∀ j, a j * (a j ^ i j % m j) < W j := by
    intro j
    have := hamW j
    have := hr j
    nlinarith
  have hmuleq : (fun j ↦
      (mulAdd (powReg k 0) (modReg (3 + k) 2) (modReg (3 + k) 0)
        (modReg (3 + k) 3) (modReg (3 + k) 4)).effect
        (binaryPowValues (a j) (m j) (e j) (i j) (extra j))) =
      (fun j ↦ framedModInput (a j * (a j ^ i j % m j)) (m j) (a j ^ i j % m j)
        0 0 (powExtra (a j) (e j) (i j) (extra j))) :=
    funext (fun j ↦ binaryPowMul_effect _ _ _ _ _)
  apply SpaceBoundByWidthAt.seq
  · apply SpaceBoundByWidthAt.seq
    · apply SpaceBoundByWidthAt.mulAdd
      · intro j; simpa [binaryPowValues] using haW j
      · intro j
        simpa [binaryPowValues] using (Nat.le_of_lt ((hr j).trans (hmW j)))
      · intro j
        have hle : a j * (a j ^ i j % m j) + a j ≤ W j := by
          have := hr j
          have := hamW j
          nlinarith
        simpa [binaryPowValues] using hle
    · rw [hmuleq]
      exact framedMod_space _ _ _ _ _ _ hm S W hp hmW
        (fun j ↦ Nat.le_of_lt ((hr j).trans (hmW j)))
        (fun _ ↦ Nat.zero_le _) (fun _ ↦ Nat.zero_le _)
  · have heq : (fun j ↦
        (seq (mulAdd (powReg k 0) (modReg (3 + k) 2) (modReg (3 + k) 0)
          (modReg (3 + k) 3) (modReg (3 + k) 4)) (framedMod (3 + k))).effect
          (binaryPowValues (a j) (m j) (e j) (i j) (extra j))) =
        (fun j ↦ framedModValues (a j * (a j ^ i j % m j)) (m j)
          (a j * (a j ^ i j % m j)) (powExtra (a j) (e j) (i j) (extra j))) := by
      funext j
      change (framedMod (3 + k)).effect (_) = _
      rw [binaryPowMul_effect, framedMod_effect _ _ _ _ _ _ (hm j)]
    rw [heq]
    apply binaryPowClean_space
    · intro j; simpa [binaryModValues] using Nat.le_of_lt (hp j)
    · intro j
      simp only [framedModValues_reg, binaryModValues]
      simp
      have := hmW j
      omega
    · intro j; simpa [binaryModValues] using Nat.le_of_lt (hp j)

/-- The entire exponent loop reuses the same linear-width binary workspace. -/
theorem binaryPowLoop_space {k : ℕ} (a m e : ℕ → ℕ) (extra : ℕ → Fin k → ℕ)
    (hm : ∀ j, 0 < m j) (S W : ℕ → ℕ)
    (haW : ∀ j, a j ≤ W j) (hmW : ∀ j, m j < W j)
    (hamW : ∀ j, a j * m j < W j) (heW : ∀ j, e j ≤ W j) :
    SpaceBoundByWidthAt (binaryPowLoop k) S
      (fun j ↦ binaryPowValues (a j) (m j) (e j) 0 (extra j)) W := by
  apply SpaceBoundByWidthAt.binaryFor_of_clamped_body
  · intro j; simpa [binaryPowValues] using heW j
  · intro j count hc
    rw [binaryPowLoop_values _ _ _ _ _ (hm j)]
    simp only [binaryPowValues, framedModInput_powReg]
    simp
    have hc' : count < e j := by simpa [binaryForCount, binaryPowValues] using hc
    exact (Nat.le_of_lt hc').trans (heW j)
  · have heq : binaryForClampedValues (binaryPowBody k) (powReg k 2) (powReg k 1)
        (fun j ↦ binaryPowValues (a j) (m j) (e j) 0 (extra j)) =
        (fun code ↦ binaryPowValues (a (Nat.unpair code).1) (m (Nat.unpair code).1)
          (e (Nat.unpair code).1)
          (min (Nat.unpair code).2 (e (Nat.unpair code).1 - 1)) (extra (Nat.unpair code).1)) := by
      funext code
      unfold binaryForClampedValues
      rw [binaryPowLoop_values _ _ _ _ _ (hm _)]
      simp [binaryForCount, binaryPowValues]
    rw [heq]
    exact binaryPowBody_space _ _ _ _ _ (fun code ↦ hm (Nat.unpair code).1) _ _
      (fun code ↦ haW (Nat.unpair code).1) (fun code ↦ hmW (Nat.unpair code).1)
      (fun code ↦ hamW (Nat.unpair code).1)

theorem powCounter_update {k : ℕ} (r m a e i t : ℕ) (extra : Fin k → ℕ) :
    Function.update (framedModInput 0 m r 0 0 (powExtra a e i extra)) (powReg k 2) t =
      framedModInput 0 m r 0 0 (powExtra a e t extra) := by
  funext j
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
  · change Function.update (framedModInput 0 m r 0 0 (powExtra a e i extra))
      (powReg k 2) t (modReg (3 + k) j) =
      framedModInput _ _ _ _ _ _ (modReg (3 + k) j)
    fin_cases j <;> simp
  · refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
    · change _ = framedModInput _ _ _ _ _ _ (powReg k j)
      fin_cases j <;> simp [powReg]
    · have hne : j.natAdd 3 ≠ (2 : Fin 3).castAdd k := by
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      simp [framedModInput, Fin.append, powExtra, powReg, hne]

def binaryPowInit (k : ℕ) : BinaryRoutine (6 + (3 + k)) :=
  seq (seq (set (modReg (3 + k) 0) 1) (framedMod (3 + k)))
    (seq (binaryPowClean k) (clear (powReg k 2)))

/-- Initialized modular exponentiation, preserving the base, modulus,
exponent, and all caller-owned extra registers. -/
def binaryPow (k : ℕ) : BinaryRoutine (6 + (3 + k)) :=
  seq (binaryPowInit k) (binaryPowLoop k)

theorem binaryPowInit_sound (k : ℕ) : (binaryPowInit k).Sound :=
  ((set_sound _ _).seq (framedMod_sound _)).seq
    ((binaryPowClean_sound _).seq (clear_sound _))

theorem binaryPow_sound (k : ℕ) : (binaryPow k).Sound :=
  (binaryPowInit_sound k).seq (binaryPowLoop_sound k)

theorem binaryPowSetOne_effect {k : ℕ} (n m r d c a e i : ℕ) (extra : Fin k → ℕ) :
    (set (modReg (3 + k) 0) 1).effect
      (framedModInput n m r d c (powExtra a e i extra)) =
      framedModInput 1 m r d c (powExtra a e i extra) := by
  funext j
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
  · change (set (modReg (3 + k) 0) 1).effect _ (modReg (3 + k) j) =
      framedModInput _ _ _ _ _ _ (modReg (3 + k) j)
    fin_cases j <;> simp [BinaryRoutine.set, seq, clear, addConst]
  · simp [BinaryRoutine.set, seq, clear, addConst]

theorem binaryPowInit_requires {k : ℕ} (n m r d c a e i : ℕ) (extra : Fin k → ℕ)
    (hm : 0 < m) :
    (binaryPowInit k).requires (framedModInput n m r d c (powExtra a e i extra)) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp [BinaryRoutine.set, seq, clear, addConst]
  · rw [binaryPowSetOne_effect]
    exact framedMod_requires _ _ _ _ _ _ hm
  · simp [seq, binaryPowClean, clear]

theorem binaryPowInit_effect {k : ℕ} (n m r d c a e i : ℕ) (extra : Fin k → ℕ)
    (hm : 0 < m) :
    (binaryPowInit k).effect (framedModInput n m r d c (powExtra a e i extra)) =
      binaryPowValues a m e 0 extra := by
  change Function.update ((binaryPowClean k).effect
    ((framedMod (3 + k)).effect ((set (modReg (3 + k) 0) 1).effect _))) (powReg k 2) 0 = _
  rw [binaryPowSetOne_effect, framedMod_effect _ _ _ _ _ _ hm, binaryPowClean_effect,
    powCounter_update]
  simp [binaryPowValues]

theorem binaryPow_requires {k : ℕ} (n m r d c a e i : ℕ) (extra : Fin k → ℕ)
    (hm : 0 < m) :
    (binaryPow k).requires (framedModInput n m r d c (powExtra a e i extra)) := by
  refine ⟨binaryPowInit_requires _ _ _ _ _ _ _ _ _ hm, ?_⟩
  rw [binaryPowInit_effect _ _ _ _ _ _ _ _ _ hm]
  exact binaryPowLoop_requires _ _ _ _ hm

/-- The complete concrete subroutine returns exactly `a^e mod m`. -/
theorem binaryPow_effect {k : ℕ} (n m r d c a e i : ℕ) (extra : Fin k → ℕ)
    (hm : 0 < m) :
    (binaryPow k).effect (framedModInput n m r d c (powExtra a e i extra)) =
      binaryPowValues a m e e extra := by
  change (binaryPowLoop k).effect ((binaryPowInit k).effect _) = _
  rw [binaryPowInit_effect _ _ _ _ _ _ _ _ _ hm, binaryPowLoop_effect _ _ _ _ hm]

theorem binaryPowInit_space {k : ℕ} (n m r d c a e i : ℕ → ℕ)
    (extra : ℕ → Fin k → ℕ) (hm : ∀ j, 0 < m j) (S W : ℕ → ℕ)
    (hn : ∀ j, n j ≤ W j) (hmW : ∀ j, m j < W j)
    (hr : ∀ j, r j ≤ W j) (hd : ∀ j, d j ≤ W j) (hc : ∀ j, c j ≤ W j)
    (hi : ∀ j, i j ≤ W j) :
    SpaceBoundByWidthAt (binaryPowInit k) S
      (fun j ↦ framedModInput (n j) (m j) (r j) (d j) (c j)
        (powExtra (a j) (e j) (i j) (extra j))) W := by
  have h1 : ∀ j, 1 < W j := fun j ↦ lt_of_le_of_lt (hm j) (hmW j)
  apply SpaceBoundByWidthAt.seq
  · apply SpaceBoundByWidthAt.seq
    · apply SpaceBoundByWidthAt.set
      · intro j; simpa using hn j
      · intro j; exact Nat.le_of_lt (h1 j)
    · have heq : (fun j ↦ (set (modReg (3 + k) 0) 1).effect
          (framedModInput (n j) (m j) (r j) (d j) (c j)
            (powExtra (a j) (e j) (i j) (extra j)))) =
          (fun j ↦ framedModInput 1 (m j) (r j) (d j) (c j)
            (powExtra (a j) (e j) (i j) (extra j))) :=
        funext (fun j ↦ binaryPowSetOne_effect _ _ _ _ _ _ _ _ _)
      rw [heq]
      exact framedMod_space _ _ _ _ _ _ hm S W h1 hmW hr hd hc
  · have heq : (fun j ↦
        (seq (set (modReg (3 + k) 0) 1) (framedMod (3 + k))).effect
          (framedModInput (n j) (m j) (r j) (d j) (c j)
            (powExtra (a j) (e j) (i j) (extra j)))) =
        (fun j ↦ framedModValues 1 (m j) 1 (powExtra (a j) (e j) (i j) (extra j))) := by
      funext j
      change (framedMod (3 + k)).effect (_) = _
      rw [binaryPowSetOne_effect, framedMod_effect _ _ _ _ _ _ (hm j)]
    rw [heq]
    apply SpaceBoundByWidthAt.seq
    · apply binaryPowClean_space
      · intro j; simpa [binaryModValues] using Nat.le_of_lt (h1 j)
      · intro j
        simp only [framedModValues_reg, binaryModValues]
        simp
        have := hmW j
        omega
      · intro j; simpa [binaryModValues] using Nat.le_of_lt (h1 j)
    · apply SpaceBoundByWidthAt.clear
      intro j
      rw [binaryPowClean_effect]
      simpa using hi j

/-- The full initialized modular-power machine obeys one uniform linear
binary-width bound, including every internal multiplication and reduction. -/
theorem binaryPow_space {k : ℕ} (n m r d c a e i : ℕ → ℕ)
    (extra : ℕ → Fin k → ℕ) (hm : ∀ j, 0 < m j) (S W : ℕ → ℕ)
    (hn : ∀ j, n j ≤ W j) (hmW : ∀ j, m j < W j)
    (hr : ∀ j, r j ≤ W j) (hd : ∀ j, d j ≤ W j) (hc : ∀ j, c j ≤ W j)
    (hi : ∀ j, i j ≤ W j) (haW : ∀ j, a j ≤ W j)
    (hamW : ∀ j, a j * m j < W j) (heW : ∀ j, e j ≤ W j) :
    SpaceBoundByWidthAt (binaryPow k) S
      (fun j ↦ framedModInput (n j) (m j) (r j) (d j) (c j)
        (powExtra (a j) (e j) (i j) (extra j))) W := by
  apply SpaceBoundByWidthAt.seq
  · exact binaryPowInit_space n m r d c a e i extra hm S W hn hmW hr hd hc hi
  · have heq : (fun j ↦ (binaryPowInit k).effect
        (framedModInput (n j) (m j) (r j) (d j) (c j)
          (powExtra (a j) (e j) (i j) (extra j)))) =
        (fun j ↦ binaryPowValues (a j) (m j) (e j) 0 (extra j)) :=
      funext (fun j ↦ binaryPowInit_effect _ _ _ _ _ _ _ _ _ (hm j))
    rw [heq]
    exact binaryPowLoop_space a m e extra hm S W haW hmW hamW heW

end SparseIrred.UpperBounds.Machine
