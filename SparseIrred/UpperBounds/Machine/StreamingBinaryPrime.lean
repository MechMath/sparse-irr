import SparseIrred.UpperBounds.Machine.StreamingBinaryFramed
import Mathlib.Data.Nat.Prime.Defs

/-!
# Trial division on canonical binary work tapes

The deterministic routine tests all divisors from two to the input minus one.
Each test reuses the modular-reduction work tapes. The number of iterations
affects time, while the all-prefix space bound depends only on binary widths.
-/

namespace SparseIrred.UpperBounds.Machine

open Complexity BinaryRoutine

/-- The accumulating primality flag is the first register after the modular workspace. -/
def primeFlagReg (k : ℕ) : Fin (6 + (k + 1)) := (0 : Fin (k + 1)).natAdd 6

/-- Register invariant between trial divisions; arbitrary extra registers are preserved. -/
def binaryPrimeValues {k : ℕ} (n d flag : ℕ) (extra : Fin k → ℕ) :
    BinaryValues (6 + (k + 1)) := framedModInput n d 0 0 0 (Fin.cons flag extra)

/-- Mathematical invariant: no divisor has yet occurred in the tested interval. -/
noncomputable def trialPrimeFlag (n d : ℕ) : ℕ := by
  classical
  exact if ∀ a ∈ Finset.Ico 2 d, ¬ a ∣ n then 1 else 0

@[simp] theorem trialPrimeFlag_two (n : ℕ) : trialPrimeFlag n 2 = 1 := by
  simp [trialPrimeFlag]

theorem trialPrimeFlag_le_one (n d : ℕ) : trialPrimeFlag n d ≤ 1 := by
  classical
  simp only [trialPrimeFlag]
  split_ifs <;> omega

theorem trialPrimeFlag_succ (n d : ℕ) (hd : 2 ≤ d) :
    trialPrimeFlag n (d + 1) = if n % d = 0 then 0 else trialPrimeFlag n d := by
  classical
  rw [trialPrimeFlag, Nat.Ico_succ_right_eq_insert_Ico hd]
  by_cases h : n % d = 0
  · have hdvd := Nat.dvd_of_mod_eq_zero h
    simp [h, hdvd]
  · have hndvd : ¬d ∣ n := by simpa only [Nat.dvd_iff_mod_eq_zero] using h
    simp [h, hndvd, trialPrimeFlag]

theorem trialPrimeFlag_eq_one_iff (n : ℕ) (hn : 2 ≤ n) :
    trialPrimeFlag n n = 1 ↔ n.Prime := by
  classical
  simp only [trialPrimeFlag, ite_eq_left_iff, zero_ne_one, imp_false, not_not]
  rw [Nat.prime_def_lt']
  simp only [hn, true_and, Finset.mem_Ico]
  exact ⟨fun h a ha hb ↦ h a ⟨ha, hb⟩, fun h a ha ↦ h a ha.1 ha.2⟩

/-- Clear the three reusable modular registers between trial divisors. -/
def binaryPrimeClean (k : ℕ) : BinaryRoutine (6 + (k + 1)) :=
  seq (clear (modReg (k + 1) 2))
    (seq (clear (modReg (k + 1) 3)) (clear (modReg (k + 1) 4)))

/-- Compute one remainder, clear the flag when it vanishes, and reuse the workspace. -/
def binaryPrimeBody (k : ℕ) : BinaryRoutine (6 + (k + 1)) :=
  seq (framedMod (k + 1))
    (seq (branchZero (modReg (k + 1) 2) (clear (primeFlagReg k)) identity)
      (binaryPrimeClean k))

/-- Trial division from the current divisor to the preserved input. -/
def binaryPrimeLoop (k : ℕ) : BinaryRoutine (6 + (k + 1)) :=
  binaryFor (binaryPrimeBody k) (modReg (k + 1) 1) (modReg (k + 1) 0)

theorem binaryPrimeClean_sound (k : ℕ) : (binaryPrimeClean k).Sound :=
  (clear_sound _).seq ((clear_sound _).seq (clear_sound _))

theorem binaryPrimeBody_sound (k : ℕ) : (binaryPrimeBody k).Sound :=
  (framedMod_sound _).seq
    (((clear_sound _).branchZero identity_sound _).seq (binaryPrimeClean_sound k))

theorem binaryPrimeLoop_sound (k : ℕ) : (binaryPrimeLoop k).Sound :=
  (binaryPrimeBody_sound k).binaryFor _ _

theorem binaryPrimeBody_requires {k : ℕ} (n d flag : ℕ) (extra : Fin k → ℕ)
    (hd : 0 < d) : (binaryPrimeBody k).requires (binaryPrimeValues n d flag extra) := by
  refine ⟨framedMod_requires n d 0 0 0 _ hd, ?_⟩
  simp only [seq, branchZero, clear, identity, emitBits, binaryPrimeClean]
  split_ifs <;> trivial

/-- One divisor test computes its flag update and preserves all other live data. -/
theorem binaryPrimeBody_effect {k : ℕ} (n d flag : ℕ) (extra : Fin k → ℕ)
    (hd : 0 < d) :
    (binaryPrimeBody k).effect (binaryPrimeValues n d flag extra) =
      binaryPrimeValues n d (if n % d = 0 then 0 else flag) extra := by
  dsimp only [binaryPrimeBody, seq, binaryPrimeValues]
  rw [framedMod_effect n d 0 0 0 _ hd]
  have hcast (i : Fin 6) : i.castAdd (k + 1) = modReg (k + 1) i := rfl
  by_cases hmod : n % d = 0 <;>
    funext j <;> refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
  · simp only [hcast]
    fin_cases j <;> simp [seq, branchZero, clear, binaryPrimeClean, primeFlagReg,
      binaryModValues, hmod]
  · refine Fin.cases ?_ (fun i ↦ ?_) j
    · simp [seq, branchZero, clear, binaryPrimeClean, primeFlagReg,
        binaryModValues, hmod]
    · simp [seq, branchZero, clear, binaryPrimeClean, primeFlagReg,
        binaryModValues, hmod]
  · simp only [hcast]
    fin_cases j <;> simp [seq, branchZero, clear, binaryPrimeClean, primeFlagReg,
      binaryModValues, hmod, identity, emitBits]
  · refine Fin.cases ?_ (fun i ↦ ?_) j
    · simp [seq, branchZero, clear, binaryPrimeClean, primeFlagReg,
        binaryModValues, hmod, identity, emitBits]
    · simp [seq, branchZero, clear, binaryPrimeClean, primeFlagReg,
        binaryModValues, hmod, identity, emitBits]

theorem binaryPrimeValues_update_divisor {k : ℕ} (n d flag d' : ℕ) (extra : Fin k → ℕ) :
    Function.update (binaryPrimeValues n d flag extra) (modReg (k + 1) 1) d' =
      binaryPrimeValues n d' flag extra := by
  have hcast (i : Fin 6) : i.castAdd (k + 1) = modReg (k + 1) i := rfl
  funext j
  refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) j
  · simp only [hcast]
    fin_cases i <;> simp [binaryPrimeValues]
  · simp [binaryPrimeValues]

theorem binaryPrimeBody_step {k : ℕ} (n d : ℕ) (extra : Fin k → ℕ) (hd : 2 ≤ d) :
    binaryForStep (binaryPrimeBody k) (modReg (k + 1) 1)
        (binaryPrimeValues n d (trialPrimeFlag n d) extra) =
      binaryPrimeValues n (d + 1) (trialPrimeFlag n (d + 1)) extra := by
  unfold binaryForStep
  rw [binaryPrimeBody_effect n d _ extra (by omega), trialPrimeFlag_succ n d hd]
  simpa only [binaryPrimeValues, framedModInput_reg, Matrix.cons_val_one, Matrix.cons_val_zero] using
    binaryPrimeValues_update_divisor n d (if n % d = 0 then 0 else trialPrimeFlag n d)
      (d + 1) extra

theorem binaryPrimeLoop_values {k : ℕ} (n i : ℕ) (extra : Fin k → ℕ) :
    binaryForValues (binaryPrimeBody k) (modReg (k + 1) 1)
        (binaryPrimeValues n 2 1 extra) i =
      binaryPrimeValues n (2 + i) (trialPrimeFlag n (2 + i)) extra := by
  induction i with
  | zero => simp [binaryForValues]
  | succ i ih =>
    rw [binaryForValues, ih, binaryPrimeBody_step n (2 + i) extra (by omega)]
    rfl

theorem binaryPrimeLoop_requires {k : ℕ} (n : ℕ) (extra : Fin k → ℕ) (hn : 2 ≤ n) :
    (binaryPrimeLoop k).requires (binaryPrimeValues n 2 1 extra) := by
  refine ⟨by simp, by simpa [binaryPrimeValues] using hn, ?_⟩
  intro i hi
  rw [binaryPrimeLoop_values]
  refine ⟨binaryPrimeBody_requires n (2 + i) _ extra (by omega), ?_, ?_⟩ <;>
    rw [binaryPrimeBody_effect n (2 + i) _ extra (by omega)] <;>
    simp [binaryPrimeValues]

/-- The concrete loop's final flag is exactly primality for every input at least two. -/
theorem binaryPrimeLoop_effect {k : ℕ} (n : ℕ) (extra : Fin k → ℕ) (hn : 2 ≤ n) :
    (binaryPrimeLoop k).effect (binaryPrimeValues n 2 1 extra) =
      binaryPrimeValues n n (trialPrimeFlag n n) extra := by
  change binaryForValues (binaryPrimeBody k) (modReg (k + 1) 1)
    (binaryPrimeValues n 2 1 extra)
      (binaryForCount (modReg (k + 1) 1) (modReg (k + 1) 0)
        (binaryPrimeValues n 2 1 extra)) = _
  have hcount : binaryForCount (modReg (k + 1) 1) (modReg (k + 1) 0)
      (binaryPrimeValues n 2 1 extra) = n - 2 := by simp [binaryForCount, binaryPrimeValues]
  rw [hcount, binaryPrimeLoop_values]
  rw [show 2 + (n - 2) = n by omega]

theorem binaryPrimeLoop_flag_iff {k : ℕ} (n : ℕ) (extra : Fin k → ℕ) (hn : 2 ≤ n) :
    (binaryPrimeLoop k).effect (binaryPrimeValues n 2 1 extra) (primeFlagReg k) = 1 ↔
      n.Prime := by
  rw [binaryPrimeLoop_effect n extra hn]
  simpa only [binaryPrimeValues, primeFlagReg, framedModInput_extra, Fin.cons_zero] using
    trialPrimeFlag_eq_one_iff n hn

/-- Cleanup costs only the widths of the three reused registers. -/
theorem binaryPrimeClean_space {k : ℕ} {S W : ℕ → ℕ}
    {v : ℕ → BinaryValues (6 + (k + 1))}
    (hv : ∀ j i, v j (modReg (k + 1) i) ≤ W j) :
    SpaceBoundByWidthAt (binaryPrimeClean k) S v W := by
  apply SpaceBoundByWidthAt.seq
  · exact SpaceBoundByWidthAt.clear _ (fun j ↦ hv j 2)
  · apply SpaceBoundByWidthAt.seq
    · apply SpaceBoundByWidthAt.clear
      intro j
      simpa [clear] using hv j 3
    · apply SpaceBoundByWidthAt.clear
      intro j
      simpa [clear] using hv j 4

/-- A divisor test has a common binary-width bound, independently of its runtime. -/
theorem binaryPrimeBody_space {k : ℕ} (n d flag : ℕ → ℕ) (extra : ℕ → Fin k → ℕ)
    (hd : ∀ j, 0 < d j) (S W : ℕ → ℕ)
    (hn : ∀ j, n j < W j) (hdW : ∀ j, d j < W j) (hf : ∀ j, flag j ≤ W j) :
    SpaceBoundByWidthAt (binaryPrimeBody k) S
      (fun j ↦ binaryPrimeValues (n j) (d j) (flag j) (extra j)) W := by
  apply SpaceBoundByWidthAt.seq
  · exact framedMod_space n d (fun _ ↦ 0) (fun _ ↦ 0) (fun _ ↦ 0)
      (fun j ↦ Fin.cons (flag j) (extra j)) hd S W hn hdW
      (fun _ ↦ Nat.zero_le _) (fun _ ↦ Nat.zero_le _) (fun _ ↦ Nat.zero_le _)
  · have heq : (fun j ↦ (framedMod (k + 1)).effect
        (binaryPrimeValues (n j) (d j) (flag j) (extra j))) =
        (fun j ↦ framedModValues (n j) (d j) (n j) (Fin.cons (flag j) (extra j))) := by
      funext j
      exact framedMod_effect _ _ _ _ _ _ (hd j)
    rw [heq]
    apply SpaceBoundByWidthAt.seq
    · apply SpaceBoundByWidthAt.branchZero
      · apply SpaceBoundByWidthAt.clear
        intro j
        simpa [primeFlagReg] using hf j
      · exact SpaceBoundByWidthAt.identity
    · apply binaryPrimeClean_space
      intro j i
      have hr := Nat.mod_lt (n j) (hd j)
      have hn' := hn j
      have hd' := hdW j
      by_cases hmod : n j % d j = 0 <;> fin_cases i <;>
        simp [branchZero, clear, identity, emitBits, primeFlagReg, binaryModValues, hmod] <;>
        omega

/-- All prefixes of the entire trial-division loop use a constant multiple of
the binary input width, even though there may be exponentially many steps. -/
theorem binaryPrimeLoop_space {k : ℕ} (n : ℕ → ℕ) (extra : ℕ → Fin k → ℕ)
    (hn : ∀ j, 2 ≤ n j) (S : ℕ → ℕ) :
    SpaceBoundByWidthAt (binaryPrimeLoop k) S
      (fun j ↦ binaryPrimeValues (n j) 2 1 (extra j)) (fun j ↦ n j + 1) := by
  apply SpaceBoundByWidthAt.binaryFor_of_clamped_body
  · intro j
    simp [binaryPrimeValues]
  · intro j count hc
    rw [binaryPrimeLoop_values]
    simp only [binaryPrimeValues, framedModInput_reg, Matrix.cons_val_one, Matrix.cons_val_zero]
    have hcount : count < n j - 2 := by simpa [binaryForCount, binaryPrimeValues] using hc
    omega
  · have heq : binaryForClampedValues (binaryPrimeBody k) (modReg (k + 1) 1)
        (modReg (k + 1) 0) (fun j ↦ binaryPrimeValues (n j) 2 1 (extra j)) =
        (fun code ↦ binaryPrimeValues (n (Nat.unpair code).1)
          (2 + min (Nat.unpair code).2 (n (Nat.unpair code).1 - 2 - 1))
          (trialPrimeFlag (n (Nat.unpair code).1)
            (2 + min (Nat.unpair code).2 (n (Nat.unpair code).1 - 2 - 1)))
          (extra (Nat.unpair code).1)) := by
      funext code
      dsimp only [binaryForClampedValues]
      rw [binaryPrimeLoop_values]
      simp only [binaryForCount, binaryPrimeValues, framedModInput_reg,
        Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [heq]
    apply binaryPrimeBody_space
    · intro code; omega
    · intro code; omega
    · intro code
      have hn' := hn (Nat.unpair code).1
      have hm := Nat.min_le_right (Nat.unpair code).2 (n (Nat.unpair code).1 - 2 - 1)
      omega
    · intro code
      exact (trialPrimeFlag_le_one _ _).trans (by omega)

end SparseIrred.UpperBounds.Machine
