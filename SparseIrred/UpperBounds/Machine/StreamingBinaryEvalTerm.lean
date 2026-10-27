import SparseIrred.UpperBounds.Machine.StreamingBinaryTerm

/-!
# Signed sparse-term accumulation on the shared 70-tape core

The first ten registers are the modular-term workspace. Registers ten, eleven,
and twelve hold the sign and the positive and negative residue accumulators.
The remaining 57 registers are preserved by every call.
-/

set_option maxHeartbeats 1600000

namespace SparseIrred.UpperBounds.Machine

open Complexity BinaryRoutine

def signedTermExtra (sign pos neg : ℕ) (extra : Fin 57 → ℕ) : Fin 60 → ℕ :=
  Fin.append ![sign, pos, neg] extra

def signedTermValues (a m e i c sign pos neg r : ℕ) (extra : Fin 57 → ℕ) : BinaryValues 70 :=
  framedModInput 0 m r 0 0 (powExtra a e i (termExtra c (signedTermExtra sign pos neg extra)))

theorem signedTermValues_eq (a m e i c sign pos neg r : ℕ) (extra : Fin 57 → ℕ) :
    signedTermValues a m e i c sign pos neg r extra =
      Fin.append ![0, m, r, 0, 0, 0, a, e, i, c, sign, pos, neg] extra := by
  funext j
  fin_cases j <;> rfl

def signedAccumulator (negative : Bool) : Fin 70 := if negative then 12 else 11

/-- Form the sum of the old accumulator and the newly computed term residue. -/
def binaryAccLoad (negative : Bool) : BinaryRoutine 70 :=
  seq (binaryCopy (signedAccumulator negative) 0 5) (add 2 0 3)

/-- Store the reduced result and clean the reusable arithmetic workspace. -/
def binaryAccStore (negative : Bool) : BinaryRoutine 70 :=
  seq (binaryCopy 2 (signedAccumulator negative) 5)
    (seq (clear 0) (seq (clear 2) (seq (clear 3) (clear 4))))

/-- Add a term to the selected accumulator modulo the preserved modulus. -/
def binaryAccumulate (negative : Bool) : BinaryRoutine 70 :=
  seq (seq (binaryAccLoad negative) (framedMod 64)) (binaryAccStore negative)

/-- Evaluate a signed monomial and accumulate its positive or negative contribution. -/
def binarySignedTerm : BinaryRoutine 70 :=
  seq (binaryTerm 60) (branchZero 10 (binaryAccumulate false) (binaryAccumulate true))

theorem binaryAccLoad_sound (negative : Bool) : (binaryAccLoad negative).Sound :=
  (binaryCopy_sound _ _ _).seq (add_sound _ _ _)

theorem binaryAccStore_sound (negative : Bool) : (binaryAccStore negative).Sound :=
  (binaryCopy_sound _ _ _).seq
    ((clear_sound _).seq ((clear_sound _).seq ((clear_sound _).seq (clear_sound _))))

theorem binaryAccumulate_sound (negative : Bool) : (binaryAccumulate negative).Sound :=
  ((binaryAccLoad_sound negative).seq (framedMod_sound 64)).seq (binaryAccStore_sound negative)

theorem binarySignedTerm_sound : binarySignedTerm.Sound :=
  (binaryTerm_sound 60).seq
    ((binaryAccumulate_sound false).branchZero (binaryAccumulate_sound true) 10)

theorem binaryAccLoad_requires (negative : Bool) (a m e i c sign pos neg r : ℕ)
    (extra : Fin 57 → ℕ) :
    (binaryAccLoad negative).requires (signedTermValues a m e i c sign pos neg r extra) := by
  cases negative <;> simp [binaryAccLoad, seq, binaryCopy, add, signedAccumulator,
    signedTermValues_eq, Fin.append, Fin.addCases]

theorem binaryAccLoad_effect (negative : Bool) (a m e i c sign pos neg r : ℕ)
    (extra : Fin 57 → ℕ) :
    (binaryAccLoad negative).effect (signedTermValues a m e i c sign pos neg r extra) =
      framedModInput ((if negative then neg else pos) + r) m r 0 0
        (powExtra a e i (termExtra c (signedTermExtra sign pos neg extra))) := by
  funext j
  refine Fin.addCases (m := 13) (n := 57) (fun j ↦ ?_) (fun j ↦ ?_) j
  · fin_cases j <;> cases negative <;>
      simp [binaryAccLoad, seq, binaryCopy, add, signedAccumulator,
        signedTermValues_eq, framedModInput, powExtra, termExtra, signedTermExtra,
        Fin.append, Fin.addCases]
  · fin_cases j <;> cases negative <;>
      simp [binaryAccLoad, seq, binaryCopy, add, signedAccumulator,
        signedTermValues_eq, framedModInput, powExtra, termExtra, signedTermExtra,
        Fin.append, Fin.addCases]

theorem binaryAccStore_effect (negative : Bool) (a m e i c sign pos neg n : ℕ)
    (extra : Fin 57 → ℕ) :
    (binaryAccStore negative).effect
      (framedModValues n m n (powExtra a e i (termExtra c (signedTermExtra sign pos neg extra)))) =
      signedTermValues a m e i c sign
        (if negative then pos else n % m) (if negative then n % m else neg) 0 extra := by
  funext j
  refine Fin.addCases (m := 13) (n := 57) (fun j ↦ ?_) (fun j ↦ ?_) j
  · fin_cases j <;> cases negative <;>
      simp [binaryAccStore, seq, binaryCopy, clear, signedAccumulator,
        signedTermValues_eq, framedModValues, binaryModValues, powExtra, termExtra,
        signedTermExtra, Fin.append, Fin.addCases]
  · fin_cases j <;> cases negative <;>
      simp [binaryAccStore, seq, binaryCopy, clear, signedAccumulator,
        signedTermValues_eq, framedModValues, binaryModValues, powExtra, termExtra,
        signedTermExtra, Fin.append, Fin.addCases]

theorem binaryAccumulate_requires (negative : Bool) (a m e i c sign pos neg r : ℕ)
    (extra : Fin 57 → ℕ) (hm : 0 < m) :
    (binaryAccumulate negative).requires (signedTermValues a m e i c sign pos neg r extra) := by
  refine ⟨⟨binaryAccLoad_requires _ _ _ _ _ _ _ _ _ _ _, ?_⟩, ?_⟩
  · rw [binaryAccLoad_effect]
    exact framedMod_requires _ _ _ _ _ _ hm
  · change (binaryAccStore negative).requires ((framedMod 64).effect (_))
    rw [binaryAccLoad_effect, framedMod_effect _ _ _ _ _ _ hm]
    cases negative <;> simp [binaryAccStore, seq, binaryCopy, clear, signedAccumulator,
      framedModValues, binaryModValues, Fin.append, Fin.addCases]

theorem binaryAccumulate_effect (negative : Bool) (a m e i c sign pos neg r : ℕ)
    (extra : Fin 57 → ℕ) (hm : 0 < m) :
    (binaryAccumulate negative).effect (signedTermValues a m e i c sign pos neg r extra) =
      signedTermValues a m e i c sign
        (if negative then pos else (pos + r) % m)
        (if negative then (neg + r) % m else neg) 0 extra := by
  change (binaryAccStore negative).effect ((framedMod 64).effect (_)) = _
  rw [binaryAccLoad_effect, framedMod_effect _ _ _ _ _ _ hm, binaryAccStore_effect]
  cases negative <;> rfl

theorem binarySignedTerm_requires (a m e c sign pos neg : ℕ) (extra : Fin 57 → ℕ)
    (hm : 0 < m) :
    binarySignedTerm.requires (signedTermValues a m e 0 c sign pos neg 0 extra) := by
  refine ⟨binaryTerm_requires _ _ _ _ _ _ _ _ _ _ hm, ?_⟩
  have he : (binaryTerm 60).effect (signedTermValues a m e 0 c sign pos neg 0 extra) =
      signedTermValues a m e e c sign pos neg ((c * a ^ e) % m) extra :=
    binaryTerm_effect 0 m 0 0 0 a e 0 c (signedTermExtra sign pos neg extra) hm
  change (branchZero 10 _ _).requires ((binaryTerm 60).effect (_))
  rw [he]
  change (if sign = 0 then (binaryAccumulate false).requires
      (signedTermValues a m e e c sign pos neg ((c * a ^ e) % m) extra)
    else (binaryAccumulate true).requires
      (signedTermValues a m e e c sign pos neg ((c * a ^ e) % m) extra))
  split_ifs <;> exact binaryAccumulate_requires _ _ _ _ _ _ _ _ _ _ _ hm

/-- The signed monomial's exact contribution is accumulated with bounded residues. -/
theorem binarySignedTerm_effect (a m e c sign pos neg : ℕ) (extra : Fin 57 → ℕ)
    (hm : 0 < m) :
    binarySignedTerm.effect (signedTermValues a m e 0 c sign pos neg 0 extra) =
      signedTermValues a m e e c sign
        (if sign = 0 then (pos + c * a ^ e) % m else pos)
        (if sign = 0 then neg else (neg + c * a ^ e) % m) 0 extra := by
  change (branchZero 10 _ _).effect ((binaryTerm 60).effect (_)) = _
  have he : (binaryTerm 60).effect (signedTermValues a m e 0 c sign pos neg 0 extra) =
      signedTermValues a m e e c sign pos neg ((c * a ^ e) % m) extra :=
    binaryTerm_effect 0 m 0 0 0 a e 0 c (signedTermExtra sign pos neg extra) hm
  rw [he]
  change (if sign = 0 then (binaryAccumulate false).effect
      (signedTermValues a m e e c sign pos neg ((c * a ^ e) % m) extra)
    else (binaryAccumulate true).effect
      (signedTermValues a m e e c sign pos neg ((c * a ^ e) % m) extra)) = _
  split_ifs <;> rw [binaryAccumulate_effect _ _ _ _ _ _ _ _ _ _ _ hm] <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_mod_mod]

end SparseIrred.UpperBounds.Machine
