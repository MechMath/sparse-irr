import SparseIrred.UpperBounds.Machine.StreamingBinaryEvalTerm

/-! # The signed derivative-term machine and its exact accumulator interface -/

set_option maxHeartbeats 1600000

namespace SparseIrred.UpperBounds.Machine

open Complexity BinaryRoutine

/-- Replace the coefficient magnitude by `c*e` and the positive exponent by `e-1`. -/
def binaryDerivativePrepare : BinaryRoutine 70 :=
  seq (mulAdd 9 7 0 3 4)
    (seq (binaryCopy 0 9 5) (seq (clear 0) (binaryPred 7)))

/-- Constant terms have zero derivative; positive exponents use the verified term machine. -/
def binarySignedDerivative : BinaryRoutine 70 :=
  branchZero 7 identity (seq binaryDerivativePrepare binarySignedTerm)

/-- Select ordinary evaluation or formal-derivative evaluation. -/
def binarySignedEvalTerm (deriv : Bool) : BinaryRoutine 70 :=
  if deriv then binarySignedDerivative else binarySignedTerm

/-- Unsigned magnitude of a term's ordinary or derivative contribution. -/
def evalTermMagnitude (deriv : Bool) (a c e : ℕ) : ℕ :=
  if deriv then c * e * a ^ (e - 1) else c * a ^ e

theorem binaryDerivativePrepare_sound : binaryDerivativePrepare.Sound :=
  (mulAdd_sound _ _ _ _ _).seq
    ((binaryCopy_sound _ _ _).seq ((clear_sound _).seq (binaryPred_sound _)))

theorem binarySignedDerivative_sound : binarySignedDerivative.Sound :=
  identity_sound.branchZero (binaryDerivativePrepare_sound.seq binarySignedTerm_sound) _

theorem binarySignedEvalTerm_sound (deriv : Bool) : (binarySignedEvalTerm deriv).Sound := by
  cases deriv
  · exact binarySignedTerm_sound
  · exact binarySignedDerivative_sound

theorem binaryDerivativePrepare_requires (a m e c sign pos neg : ℕ) (extra : Fin 57 → ℕ)
    (he : 0 < e) :
    binaryDerivativePrepare.requires (signedTermValues a m e 0 c sign pos neg 0 extra) := by
  simp [binaryDerivativePrepare, seq, mulAdd, binaryCopy, clear, binaryPred,
    signedTermValues_eq, Fin.append, Fin.addCases, he]
  constructor <;> decide

theorem binaryDerivativePrepare_effect (a m e c sign pos neg : ℕ) (extra : Fin 57 → ℕ) :
    binaryDerivativePrepare.effect (signedTermValues a m e 0 c sign pos neg 0 extra) =
      signedTermValues a m (e - 1) 0 (c * e) sign pos neg 0 extra := by
  funext j
  fin_cases j <;>
    simp [binaryDerivativePrepare, seq, mulAdd, binaryCopy, clear, binaryPred,
      signedTermValues_eq, Fin.append, Fin.addCases]

theorem binarySignedDerivative_requires (a m e c sign pos neg : ℕ) (extra : Fin 57 → ℕ)
    (hm : 0 < m) :
    binarySignedDerivative.requires (signedTermValues a m e 0 c sign pos neg 0 extra) := by
  change (if e = 0 then True else binaryDerivativePrepare.requires _ ∧
    binarySignedTerm.requires (binaryDerivativePrepare.effect _))
  by_cases he : e = 0
  · simp [he]
  · rw [ite_eq_right he, binaryDerivativePrepare_effect]
    exact ⟨binaryDerivativePrepare_requires _ _ _ _ _ _ _ _ (Nat.pos_of_ne_zero he),
      binarySignedTerm_requires _ _ _ _ _ _ _ _ hm⟩

theorem binarySignedDerivative_effect (a m e c sign pos neg : ℕ) (extra : Fin 57 → ℕ)
    (hm : 0 < m) :
    binarySignedDerivative.effect (signedTermValues a m e 0 c sign pos neg 0 extra) =
      if e = 0 then signedTermValues a m e 0 c sign pos neg 0 extra
      else signedTermValues a m (e - 1) (e - 1) (c * e) sign
        (if sign = 0 then (pos + c * e * a ^ (e - 1)) % m else pos)
        (if sign = 0 then neg else (neg + c * e * a ^ (e - 1)) % m) 0 extra := by
  change (if e = 0 then _ else binarySignedTerm.effect (binaryDerivativePrepare.effect _)) = _
  by_cases he : e = 0
  · simp [he, identity, emitBits]
  · rw [ite_eq_right he, ite_eq_right he, binaryDerivativePrepare_effect,
      binarySignedTerm_effect _ _ _ _ _ _ _ _ hm]

theorem binarySignedEvalTerm_requires (deriv : Bool) (a m e c sign pos neg : ℕ)
    (extra : Fin 57 → ℕ) (hm : 0 < m) :
    (binarySignedEvalTerm deriv).requires (signedTermValues a m e 0 c sign pos neg 0 extra) := by
  cases deriv
  · exact binarySignedTerm_requires _ _ _ _ _ _ _ _ hm
  · exact binarySignedDerivative_requires _ _ _ _ _ _ _ _ hm

/-- Both evaluation modes return the exact reduced positive and negative sums. -/
theorem binarySignedEvalTerm_accumulators (deriv : Bool) (a m e c sign pos neg : ℕ)
    (extra : Fin 57 → ℕ) (hm : 0 < m) (hp : pos < m) (hn : neg < m) :
    let out := (binarySignedEvalTerm deriv).effect
      (signedTermValues a m e 0 c sign pos neg 0 extra)
    (out 11, out 12) =
      (if sign = 0 then (pos + evalTermMagnitude deriv a c e) % m else pos,
       if sign = 0 then neg else (neg + evalTermMagnitude deriv a c e) % m) := by
  cases deriv
  · simp only [binarySignedEvalTerm, Bool.false_eq_true, ↓reduceIte,
      binarySignedTerm_effect _ _ _ _ _ _ _ _ hm, evalTermMagnitude]
    simp [signedTermValues_eq, Fin.append, Fin.addCases]
  · simp only [binarySignedEvalTerm, ↓reduceIte,
      binarySignedDerivative_effect _ _ _ _ _ _ _ _ hm, evalTermMagnitude]
    by_cases he : e = 0 <;> by_cases hs : sign = 0 <;>
      simp [he, hs, signedTermValues_eq, Fin.append, Fin.addCases,
        Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hn]

/-- The term routines preserve the entire caller frame. -/
theorem binarySignedEvalTerm_extra (deriv : Bool) (a m e c sign pos neg : ℕ)
    (extra : Fin 57 → ℕ) (hm : 0 < m) (j : Fin 57) :
    (binarySignedEvalTerm deriv).effect (signedTermValues a m e 0 c sign pos neg 0 extra)
      (j.natAdd 13) = extra j := by
  cases deriv
  · rw [binarySignedEvalTerm, ite_eq_right Bool.false_ne_true,
      binarySignedTerm_effect _ _ _ _ _ _ _ _ hm, signedTermValues_eq]
    exact Fin.append_right _ _ _
  · simp only [binarySignedEvalTerm, ↓reduceIte,
      binarySignedDerivative_effect _ _ _ _ _ _ _ _ hm]
    split_ifs <;> rw [signedTermValues_eq] <;> exact Fin.append_right _ _ _

end SparseIrred.UpperBounds.Machine
