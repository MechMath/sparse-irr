import SparseIrred.UpperBounds.Machine.StreamingBinaryEvalDerivative
import SparseIrred.UpperBounds.SparseModularEval

/-! # Meaning of the positive and negative residue accumulators -/

namespace SparseIrred.UpperBounds.Machine

open Polynomial SparseDiv SparseDiv.Appendix

/-- One signed term updates exactly one residue accumulator. -/
def signedEvalStep (deriv : Bool) (a m : ℕ) (acc : ℕ × ℕ) (t : ℤ × ℕ) : ℕ × ℕ :=
  let mag := evalTermMagnitude deriv a t.1.natAbs t.2
  if t.1 < 0 then (acc.1, (acc.2 + mag) % m)
  else ((acc.1 + mag) % m, acc.2)

/-- Functional invariant of the actual signed-term accumulator loop. -/
def signedEvalFold (deriv : Bool) (a m : ℕ) (l : ITerms) (acc : ℕ × ℕ) : ℕ × ℕ :=
  l.foldl (signedEvalStep deriv a m) acc

/-- Both accumulators remain canonical residues after every term. -/
theorem signedEvalStep_lt (deriv : Bool) (a m : ℕ) (acc : ℕ × ℕ) (t : ℤ × ℕ)
    (hm : 0 < m) (hp : acc.1 < m) (hn : acc.2 < m) :
    (signedEvalStep deriv a m acc t).1 < m ∧ (signedEvalStep deriv a m acc t).2 < m := by
  unfold signedEvalStep
  split_ifs <;> simp only <;> exact ⟨by first | exact hp | exact Nat.mod_lt _ hm,
    by first | exact hn | exact Nat.mod_lt _ hm⟩

/-- Canonical-residue bounds hold throughout a complete sparse scan. -/
theorem signedEvalFold_lt (deriv : Bool) (a m : ℕ) (l : ITerms) (acc : ℕ × ℕ)
    (hm : 0 < m) (hp : acc.1 < m) (hn : acc.2 < m) :
    (signedEvalFold deriv a m l acc).1 < m ∧ (signedEvalFold deriv a m l acc).2 < m := by
  induction l generalizing acc with
  | nil => exact ⟨hp, hn⟩
  | cons t l ih =>
    exact ih (signedEvalStep deriv a m acc t)
      (signedEvalStep_lt deriv a m acc t hm hp hn).1
      (signedEvalStep_lt deriv a m acc t hm hp hn).2

/-- Subtracting the two unsigned accumulators recovers the signed term contribution. -/
theorem signedEvalStep_cast (deriv : Bool) (a m : ℕ) (acc : ℕ × ℕ) (c : ℤ) (e : ℕ) :
    ((signedEvalStep deriv a m acc (c, e)).1 : ZMod m) -
        ((signedEvalStep deriv a m acc (c, e)).2 : ZMod m) =
      ((acc.1 : ZMod m) - (acc.2 : ZMod m)) +
        if deriv then (c : ZMod m) * e * (a : ZMod m) ^ (e - 1)
        else (c : ZMod m) * (a : ZMod m) ^ e := by
  cases c with
  | ofNat c =>
    have hsign : ¬(c : ℤ) < 0 := by omega
    cases deriv <;>
      simp [signedEvalStep, evalTermMagnitude, hsign, ZMod.natCast_mod, Nat.cast_add,
        Nat.cast_mul, Nat.cast_pow] <;> ring
  | negSucc c =>
    cases deriv <;>
      simp [signedEvalStep, evalTermMagnitude, ZMod.natCast_mod, Nat.cast_add,
        Nat.cast_mul, Nat.cast_pow, Int.cast_negSucc] <;> ring

/-- The signed accumulator invariant computes the polynomial or its derivative. -/
theorem signedEvalFold_cast (deriv : Bool) (a m : ℕ) (l : ITerms) (acc : ℕ × ℕ) :
    ((signedEvalFold deriv a m l acc).1 : ZMod m) -
        ((signedEvalFold deriv a m l acc).2 : ZMod m) =
      ((acc.1 : ZMod m) - (acc.2 : ZMod m)) +
        if deriv then ((toPolyZ l).map (Int.castRingHom (ZMod m))).derivative.eval (a : ZMod m)
        else ((toPolyZ l).map (Int.castRingHom (ZMod m))).eval (a : ZMod m) := by
  induction l generalizing acc with
  | nil => cases deriv <;> simp [signedEvalFold, toPolyZ]
  | cons t l ih =>
    rcases t with ⟨c, e⟩
    change ((signedEvalFold deriv a m l (signedEvalStep deriv a m acc (c, e))).1 : ZMod m) -
      ((signedEvalFold deriv a m l (signedEvalStep deriv a m acc (c, e))).2 : ZMod m) = _
    rw [ih, signedEvalStep_cast]
    cases deriv <;> simp [toPolyZ_cons, Polynomial.derivative_X_pow] <;> ring

/-- Equal canonical residues are equivalent to zero difference in `ZMod`. -/
theorem residues_eq_iff_sub_cast_eq_zero (m pos neg : ℕ) (hm : 0 < m)
    (hp : pos < m) (hn : neg < m) :
    pos = neg ↔ (pos : ZMod m) - (neg : ZMod m) = 0 := by
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  rw [sub_eq_zero]
  constructor
  · intro h; rw [h]
  · intro h
    have hv := congrArg ZMod.val h
    simpa only [ZMod.val_natCast_of_lt hp, ZMod.val_natCast_of_lt hn] using hv

/-- Comparing the final positive and negative residues is exactly the required zero test. -/
theorem signedEvalFold_eq_iff_eval_zero (deriv : Bool) (a m : ℕ) (l : ITerms)
    (hm : 0 < m) :
    (signedEvalFold deriv a m l (0, 0)).1 = (signedEvalFold deriv a m l (0, 0)).2 ↔
      (if deriv then ((toPolyZ l).map (Int.castRingHom (ZMod m))).derivative.eval (a : ZMod m)
        else ((toPolyZ l).map (Int.castRingHom (ZMod m))).eval (a : ZMod m)) = 0 := by
  obtain ⟨hp, hn⟩ := signedEvalFold_lt deriv a m l (0, 0) hm hm hm
  rw [residues_eq_iff_sub_cast_eq_zero m _ _ hm hp hn, signedEvalFold_cast]
  simp

end SparseIrred.UpperBounds.Machine
