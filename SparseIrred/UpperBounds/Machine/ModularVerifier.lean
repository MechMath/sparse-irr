import SparseGcd.Machine.TermsStr
import SparseDivComplexity.Appendix.IntTermsString
import SparseIrred.UpperBounds.SparseModularEval

/-!
# Polynomial-time sparse modular evaluation on binary strings

The implementation uses binary modular exponentiation and framed-list maps and folds.
It never expands a sparse polynomial into a dense coefficient vector. Signed coefficients
are reduced before multiplication. Both the value and derivative are computed in Cobham's
algebra, which supplies actual polynomial-time Turing-machine implementations.
-/

open Polynomial Complexity SparseDiv SparseDiv.StringArith SparseDiv.Appendix SparseGcd

namespace SparseIrred.UpperBounds

/-- Reduce a sign-magnitude integer string modulo a binary modulus. -/
def intModStr (p c : List Bool) : List Bool :=
  redStr (caseBit₀ (negFlag c) (subBits p (redStr (magOf c) p)) (redStr (magOf c) p)) p

theorem cobham_intModStr_comp {n : ℕ} {gp gc : (Fin n → List Bool) → List Bool}
    (hp : Cobham gp) (hc : Cobham gc) :
    Cobham fun v ↦ intModStr (gp v) (gc v) := by
  unfold intModStr
  exact cobham_redStr_comp (Cobham.iteFn (cobham_negFlag_comp hc)
    (cobham_subBits_comp hp (cobham_redStr_comp (cobham_magOf_comp hc) hp))
    (cobham_redStr_comp (cobham_magOf_comp hc) hp)) hp

theorem natCast_decNat_redStr (x p : List Bool) (hp : decNat p ≠ 0) :
    (decNat (redStr x p) : ZMod (decNat p)) = (decNat x : ZMod (decNat p)) := by
  rw [decNat_redStr _ _ hp, ZMod.natCast_mod]

theorem natCast_decNat_intModStr (p c : List Bool) (hp : decNat p ≠ 0) :
    (decNat (intModStr p c) : ZMod (decNat p)) = (decInt c : ZMod (decNat p)) := by
  unfold intModStr
  rw [natCast_decNat_redStr _ _ hp]
  rcases negFlag_flag c with h | h
  · rw [h, caseBit₀_cons, Bool.cond_true, decNat_subBits,
      decNat_redStr _ _ hp, Nat.cast_sub (Nat.mod_lt _ (Nat.pos_of_ne_zero hp)).le,
      ZMod.natCast_self,
      ZMod.natCast_mod, zero_sub, decInt_of_negFlag_true h, Int.cast_neg, Int.cast_natCast]
  · rw [h, caseBit₀_cons, Bool.cond_false, natCast_decNat_redStr _ _ hp,
      decInt_of_negFlag_false h, Int.cast_natCast]

/-- One term's contribution; `deriv = true` computes its formal derivative. -/
def termEvalModStr (deriv : Bool) (p a t : List Bool) : List Bool :=
  let c := intModStr p (pairFst t)
  let e := pairSnd t
  let coeff := if deriv then mulBits c e else c
  let exponent := if deriv then subBits e [true] else e
  redStr (mulBits coeff (powModStr a exponent p)) p

theorem cobham_termEvalModStr_comp (deriv : Bool) {n : ℕ}
    {gp ga gt : (Fin n → List Bool) → List Bool}
    (hp : Cobham gp) (ha : Cobham ga) (ht : Cobham gt) :
    Cobham fun v ↦ termEvalModStr deriv (gp v) (ga v) (gt v) := by
  have hc := cobham_intModStr_comp hp (cobham_pairFst_comp ht)
  have he := cobham_pairSnd_comp ht
  cases deriv
  · exact cobham_redStr_comp
      (cobham_mulBits_comp hc (SparseGcd.cobham_powModStr_comp ha he hp)) hp
  · exact cobham_redStr_comp (cobham_mulBits_comp (cobham_mulBits_comp hc he)
      (SparseGcd.cobham_powModStr_comp ha
        (cobham_subBits_comp he (Cobham.const [true])) hp)) hp

theorem natCast_decNat_termEvalModStr (deriv : Bool) (p a : List Bool)
    (c : ℤ) (e : ℕ) (hp : decNat p ≠ 0) :
    (decNat (termEvalModStr deriv p a (encITerm (c, e))) : ZMod (decNat p)) =
      if deriv then (c : ZMod (decNat p)) * e * (decNat a : ZMod (decNat p)) ^ (e - 1)
      else (c : ZMod (decNat p)) * (decNat a : ZMod (decNat p)) ^ e := by
  cases deriv <;>
    simp only [termEvalModStr, Bool.false_eq_true, ↓reduceIte,
      encITerm, pairFst_pair, pairSnd_pair, natCast_decNat_redStr _ _ hp,
      decNat_mulBits, Nat.cast_mul, natCast_decNat_intModStr _ _ hp, decInt_encInt,
      decNat_powModStr _ _ _ hp, powMod, ZMod.natCast_mod, Nat.cast_pow,
      decNat_encNat, decNat_subBits, decNat_cons, decNat_nil, Nat.mul_zero,
      Nat.add_zero]

/-- Sum a framed list of binary numerals. -/
def sumNumeralsStr (s : List Bool) : List Bool := foldBlocks addBits [] s

theorem cobham_sumNumeralsStr : Cobham fun v : Fin 1 → List Bool ↦ sumNumeralsStr (v 0) := by
  exact (cobham_foldBlocks (n := 0) cobham_addBits (Cobham.const []) 2
    (fun w ↦ by have := length_addBits_le (w 0) (w 1); omega)).of_eq fun _ ↦ rfl

/-- Evaluate all sparse terms, or their derivatives, and reduce the resulting sum. -/
def sparseEvalModStr (deriv : Bool) (p a s : List Bool) : List Bool :=
  redStr (sumNumeralsStr (mapBlocks (termEvalModStr deriv p a) s)) p

theorem cobham_sparseEvalModStr (deriv : Bool) :
    Cobham fun v : Fin 3 → List Bool ↦ sparseEvalModStr deriv (v 0) (v 1) (v 2) := by
  have hm : Cobham fun v : Fin 3 → List Bool ↦
      mapBlocks (termEvalModStr deriv (v 0) (v 1)) (v 2) := by
    exact TermsStr.cobham_mapBlocks_comp
      (cobham_termEvalModStr_comp deriv (.proj 1) (.proj 2) (.proj 0)) (.proj 2)
  exact cobham_redStr_comp
    ((Cobham.comp cobham_sumNumeralsStr fun _ : Fin 1 ↦ hm).of_eq fun _ ↦ rfl) (.proj 0)

theorem cobham_sparseEvalModStr_comp (deriv : Bool) {n : ℕ}
    {gp ga gs : (Fin n → List Bool) → List Bool}
    (hp : Cobham gp) (ha : Cobham ga) (hs : Cobham gs) :
    Cobham fun v ↦ sparseEvalModStr deriv (gp v) (ga v) (gs v) :=
  (Cobham.comp₃ (cobham_sparseEvalModStr deriv) hp ha hs).of_eq fun _ ↦ rfl

/-- The encoded three-argument modular evaluator is an actual polynomial-time function. -/
theorem sparseEvalModStr_mem_FP (deriv : Bool) :
    (fun x ↦ sparseEvalModStr deriv (pairFst x) (pairFst (pairSnd x))
      (pairSnd (pairSnd x))) ∈ FP := by
  apply CobhamFP_subset_FP
  exact cobham_sparseEvalModStr_comp deriv (cobham_pairFst_comp (.proj 0))
    (cobham_pairFst_comp (cobham_pairSnd_comp (.proj 0)))
    (cobham_pairSnd_comp (cobham_pairSnd_comp (.proj 0)))

private theorem decNat_foldl_addBits (bs : List (List Bool)) (acc : List Bool) :
    decNat (bs.foldl addBits acc) = decNat acc + (bs.map decNat).sum := by
  induction bs generalizing acc with
  | nil => simp
  | cons b bs ih => simp [ih, decNat_addBits, Nat.add_assoc]

theorem decNat_sumNumeralsStr_frame (bs : List (List Bool)) :
    decNat (sumNumeralsStr (frame bs)) = (bs.map decNat).sum := by
  simp only [sumNumeralsStr, foldBlocks_frame, decNat_foldl_addBits, decNat_nil, zero_add]

/-- Correctness over every nonzero modulus, without primality or canonical-term assumptions. -/
theorem natCast_decNat_sparseEvalModStr (deriv : Bool) (p a : List Bool)
    (l : ITerms) (hp : decNat p ≠ 0) :
    (decNat (sparseEvalModStr deriv p a (encITerms l)) : ZMod (decNat p)) =
      if deriv then
        ((toPolyZ l).map (Int.castRingHom (ZMod (decNat p)))).derivative.eval
          (decNat a : ZMod (decNat p))
      else ((toPolyZ l).map (Int.castRingHom (ZMod (decNat p)))).eval
        (decNat a : ZMod (decNat p)) := by
  rw [sparseEvalModStr, natCast_decNat_redStr _ _ hp, encITerms, mapBlocks_frame,
    sumNumeralsStr, foldBlocks_frame, decNat_foldl_addBits]
  simp only [decNat_nil, zero_add, List.map_map]
  induction l with
  | nil => cases deriv <;> simp
  | cons t l ih =>
    rcases t with ⟨c, e⟩
    simp only [List.map_cons, List.sum_cons, Nat.cast_add, Function.comp_apply,
      natCast_decNat_termEvalModStr _ _ _ _ _ hp, ih]
    cases deriv <;>
      simp [toPolyZ_cons, Polynomial.derivative_X_pow, mul_assoc]

/-- The output is a canonical residue below the nonzero modulus. -/
theorem decNat_sparseEvalModStr_lt (deriv : Bool) (p a s : List Bool)
    (hp : decNat p ≠ 0) : decNat (sparseEvalModStr deriv p a s) < decNat p := by
  unfold sparseEvalModStr
  rw [decNat_redStr _ _ hp]
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero hp)

/-- Bitstring zero-testing is exactly modular polynomial (or derivative) zero-testing. -/
theorem sparseEvalModStr_isZero_iff (deriv : Bool) (p a : List Bool)
    (l : ITerms) (hp : decNat p ≠ 0) :
    isZeroBits (sparseEvalModStr deriv p a (encITerms l)) = [true] ↔
      (if deriv then
        ((toPolyZ l).map (Int.castRingHom (ZMod (decNat p)))).derivative.eval
          (decNat a : ZMod (decNat p))
      else ((toPolyZ l).map (Int.castRingHom (ZMod (decNat p)))).eval
        (decNat a : ZMod (decNat p))) = 0 := by
  rw [isZeroBits_eq_true_iff, ← natCast_decNat_sparseEvalModStr deriv p a l hp]
  have hv := ZMod.val_natCast_of_lt (decNat_sparseEvalModStr_lt deriv p a (encITerms l) hp)
  constructor
  · intro h
    rw [h, Nat.cast_zero]
  · intro h
    rw [h, ZMod.val_zero] at hv
    exact hv.symm

theorem sparseEvalModStr_zero_flag (deriv : Bool) (p a : List Bool)
    (l : ITerms) (hp : decNat p ≠ 0) :
    isZeroBits (sparseEvalModStr deriv p a (encITerms l)) =
      [decide ((if deriv then
        ((toPolyZ l).map (Int.castRingHom (ZMod (decNat p)))).derivative.eval
          (decNat a : ZMod (decNat p))
      else ((toPolyZ l).map (Int.castRingHom (ZMod (decNat p)))).eval
        (decNat a : ZMod (decNat p))) = 0)] := by
  rcases isZeroBits_flag (sparseEvalModStr deriv p a (encITerms l)) with h | h
  · rw [h, decide_eq_true ((sparseEvalModStr_isZero_iff deriv p a l hp).mp h)]
  · rw [h, decide_eq_false (by
      intro hz
      have ht := (sparseEvalModStr_isZero_iff deriv p a l hp).mpr hz
      rw [h] at ht
      simp at ht)]

/-- The common encoded-input specialization of the modular zero test. -/
theorem sparseEvalModStr_encoded_zero_iff (deriv : Bool) (p a : ℕ)
    (l : ITerms) (hp : p ≠ 0) :
    isZeroBits (sparseEvalModStr deriv (encNat p) (encNat a) (encITerms l)) = [true] ↔
      (if deriv then ((toPolyZ l).map (Int.castRingHom (ZMod p))).derivative.eval (a : ZMod p)
      else ((toPolyZ l).map (Int.castRingHom (ZMod p))).eval (a : ZMod p)) = 0 := by
  have h := sparseEvalModStr_isZero_iff deriv (encNat p) (encNat a) l (by simpa using hp)
  simp only [decNat_encNat] at h
  exact h.trans (Iff.of_eq (congrArg (fun q : ℕ ↦
    (if deriv then ((toPolyZ l).map (Int.castRingHom (ZMod q))).derivative.eval (a : ZMod q)
    else ((toPolyZ l).map (Int.castRingHom (ZMod q))).eval (a : ZMod q)) = 0)
    (decNat_encNat p)))

/-- The complete output bit agrees with the modular zero predicate. -/
theorem sparseEvalModStr_encoded_zero_flag (deriv : Bool) (p a : ℕ)
    (l : ITerms) (hp : p ≠ 0) :
    isZeroBits (sparseEvalModStr deriv (encNat p) (encNat a) (encITerms l)) =
      [decide ((if deriv then
        ((toPolyZ l).map (Int.castRingHom (ZMod p))).derivative.eval (a : ZMod p)
      else ((toPolyZ l).map (Int.castRingHom (ZMod p))).eval (a : ZMod p)) = 0)] := by
  rcases isZeroBits_flag (sparseEvalModStr deriv (encNat p) (encNat a) (encITerms l)) with h | h
  · rw [h, decide_eq_true ((sparseEvalModStr_encoded_zero_iff deriv p a l hp).mp h)]
  · rw [h, decide_eq_false (by
      intro hz
      have ht := (sparseEvalModStr_encoded_zero_iff deriv p a l hp).mpr hz
      rw [h] at ht
      simp at ht)]

end SparseIrred.UpperBounds
