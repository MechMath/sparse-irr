import SparseIrred.UpperBounds.Section4.FieldElements
import SparseGcd.Machine.TermsStr

/-!
# Verified binary arithmetic in the input prime field

All functions operate on little-endian bit strings and are total, including on
zero moduli and malformed numerals. Reduction gives a uniform output bound on
every input, which is needed when these operations occur inside bounded loops.
-/

namespace SparseIrred.UpperBounds.Section4

open Complexity SparseDiv SparseDiv.StringArith SparseGcd

def primeAddStr (p a b : List Bool) : List Bool := redStr (addBits a b) p
def primeMulStr (p a b : List Bool) : List Bool := redStr (mulBits a b) p
def primeNegStr (p a : List Bool) : List Bool := redStr (subBits p (redStr a p)) p
def primeSubStr (p a b : List Bool) : List Bool := primeAddStr p a (primeNegStr p b)
def primePowStr (p a e : List Bool) : List Bool := powModStr a e p
def primeInvStr (p a : List Bool) : List Bool :=
  caseBit₀ (isZeroBits (redStr a p)) [] (primePowStr p a (subBits p (encNat 2)))

theorem cobham_primeAddStr_comp {n : ℕ} {p a b : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (ha : Cobham a) (hb : Cobham b) :
    Cobham fun v ↦ primeAddStr (p v) (a v) (b v) :=
  cobham_redStr_comp (cobham_addBits_comp ha hb) hp

theorem cobham_primeMulStr_comp {n : ℕ} {p a b : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (ha : Cobham a) (hb : Cobham b) :
    Cobham fun v ↦ primeMulStr (p v) (a v) (b v) :=
  cobham_redStr_comp (cobham_mulBits_comp ha hb) hp

theorem cobham_primeNegStr_comp {n : ℕ} {p a : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (ha : Cobham a) : Cobham fun v ↦ primeNegStr (p v) (a v) :=
  cobham_redStr_comp (cobham_subBits_comp hp (cobham_redStr_comp ha hp)) hp

theorem cobham_primeSubStr_comp {n : ℕ} {p a b : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (ha : Cobham a) (hb : Cobham b) :
    Cobham fun v ↦ primeSubStr (p v) (a v) (b v) :=
  cobham_primeAddStr_comp hp ha (cobham_primeNegStr_comp hp hb)

theorem cobham_primePowStr_comp {n : ℕ} {p a e : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (ha : Cobham a) (he : Cobham e) :
    Cobham fun v ↦ primePowStr (p v) (a v) (e v) :=
  cobham_powModStr_comp ha he hp

theorem cobham_primeInvStr_comp {n : ℕ} {p a : (Fin n → List Bool) → List Bool}
    (hp : Cobham p) (ha : Cobham a) : Cobham fun v ↦ primeInvStr (p v) (a v) :=
  Cobham.iteFn (cobham_isZeroBits_comp (cobham_redStr_comp ha hp)) (Cobham.const [])
    (cobham_primePowStr_comp hp ha (cobham_subBits_comp hp (Cobham.const _)))

theorem primeAddStr_length (p a b : List Bool) : (primeAddStr p a b).length ≤ p.length :=
  length_redStr_le _ _
theorem primeMulStr_length (p a b : List Bool) : (primeMulStr p a b).length ≤ p.length :=
  length_redStr_le _ _
theorem primeNegStr_length (p a : List Bool) : (primeNegStr p a).length ≤ p.length :=
  length_redStr_le _ _
theorem primeSubStr_length (p a b : List Bool) : (primeSubStr p a b).length ≤ p.length :=
  length_redStr_le _ _
theorem primePowStr_length (p a e : List Bool) : (primePowStr p a e).length ≤ p.length :=
  length_powModAux_le _ _ _
theorem primeInvStr_length (p a : List Bool) : (primeInvStr p a).length ≤ p.length := by
  rcases caseBit₀_cases (isZeroBits (redStr a p)) []
    (primePowStr p a (subBits p (encNat 2))) with h | h
  · simpa only [primeInvStr, h, List.length_nil] using Nat.zero_le p.length
  · simpa only [primeInvStr, h] using primePowStr_length p a (subBits p (encNat 2))

theorem natCast_decNat_redStr (p a : List Bool) (hp : decNat p ≠ 0) :
    (decNat (redStr a p) : ZMod (decNat p)) = (decNat a : ZMod (decNat p)) := by
  rw [decNat_redStr a p hp, ZMod.natCast_mod]

theorem primeAddStr_correct (p a b : List Bool) (hp : decNat p ≠ 0) :
    (decNat (primeAddStr p a b) : ZMod (decNat p)) = decNat a + decNat b := by
  rw [primeAddStr, natCast_decNat_redStr p _ hp, decNat_addBits, Nat.cast_add]

theorem primeMulStr_correct (p a b : List Bool) (hp : decNat p ≠ 0) :
    (decNat (primeMulStr p a b) : ZMod (decNat p)) = decNat a * decNat b := by
  rw [primeMulStr, natCast_decNat_redStr p _ hp, decNat_mulBits, Nat.cast_mul]

theorem primeNegStr_correct (p a : List Bool) (hp : decNat p ≠ 0) :
    (decNat (primeNegStr p a) : ZMod (decNat p)) = -(decNat a : ZMod (decNat p)) := by
  rw [primeNegStr, natCast_decNat_redStr p _ hp, decNat_subBits, decNat_redStr a p hp]
  rw [Nat.cast_sub (Nat.le_of_lt (Nat.mod_lt _ (Nat.pos_of_ne_zero hp))),
    ZMod.natCast_self, ZMod.natCast_mod, zero_sub]

theorem primeSubStr_correct (p a b : List Bool) (hp : decNat p ≠ 0) :
    (decNat (primeSubStr p a b) : ZMod (decNat p)) = decNat a - decNat b := by
  rw [primeSubStr, primeAddStr_correct p _ _ hp, primeNegStr_correct p _ hp, sub_eq_add_neg]

theorem primePowStr_correct (p a e : List Bool) (hp : decNat p ≠ 0) :
    (decNat (primePowStr p a e) : ZMod (decNat p)) = (decNat a : ZMod (decNat p)) ^ decNat e := by
  rw [primePowStr, decNat_powModStr a e p hp]
  simp only [powMod, ZMod.natCast_mod, Nat.cast_pow]

/-- Inversion uses square-and-multiply with exponent `p-2`, with zero handled first. -/
theorem primeInvStr_correct (p a : List Bool) [Fact (decNat p).Prime] :
    (decNat (primeInvStr p a) : ZMod (decNat p)) = (decNat a : ZMod (decNat p))⁻¹ := by
  have hp : decNat p ≠ 0 := (Fact.out : (decNat p).Prime).ne_zero
  by_cases ha : decNat (redStr a p) = 0
  · have ha0 : (decNat a : ZMod (decNat p)) = 0 := by
      rw [← natCast_decNat_redStr p a hp, ha, Nat.cast_zero]
    rw [primeInvStr, (isZeroBits_eq_true_iff _).mpr ha]
    simp [ha0]
  · have ha0 : (decNat a : ZMod (decNat p)) ≠ 0 := by
      intro h
      apply ha
      rw [decNat_redStr a p hp]
      exact (ZMod.natCast_eq_zero_iff _ _).mp h |> Nat.mod_eq_zero_of_dvd
    rw [primeInvStr, isZeroBits_eq_false ha, caseBit₀_cons, Bool.cond_false,
      primePowStr_correct p a _ hp, decNat_subBits, decNat_encNat]
    apply (mul_right_cancel₀ ha0)
    rw [inv_mul_cancel₀ ha0, ← pow_succ]
    have hdeg : decNat p - 2 + 1 = decNat p - 1 := by
      have := (Fact.out : (decNat p).Prime).two_le
      omega
    rw [hdeg, ZMod.pow_card_sub_one_eq_one ha0]

/-- Reduction returns the exact canonical binary representative. -/
theorem redStr_eq_zmod_val (p : ℕ) [NeZero p] (a : List Bool) :
    redStr a (encNat p) = encNat (decNat a : ZMod p).val := by
  rw [redStr_eq_encNat _ _ (by simpa using NeZero.ne p), decNat_encNat, ZMod.val_natCast]

theorem primeAddStr_eq_zmod_val (p : ℕ) [NeZero p] (a b : List Bool) :
    primeAddStr (encNat p) a b =
      encNat ((decNat a : ZMod p) + decNat b).val := by
  rw [primeAddStr, redStr_eq_zmod_val, decNat_addBits, Nat.cast_add]

theorem primeMulStr_eq_zmod_val (p : ℕ) [NeZero p] (a b : List Bool) :
    primeMulStr (encNat p) a b =
      encNat ((decNat a : ZMod p) * decNat b).val := by
  rw [primeMulStr, redStr_eq_zmod_val, decNat_mulBits, Nat.cast_mul]

theorem primeNegStr_eq_zmod_val (p : ℕ) [NeZero p] (a : List Bool) :
    primeNegStr (encNat p) a = encNat (-(decNat a : ZMod p)).val := by
  rw [primeNegStr, redStr_eq_zmod_val]
  congr 2
  rw [decNat_subBits, decNat_redStr _ _ (by simpa using NeZero.ne p), decNat_encNat]
  rw [Nat.cast_sub (Nat.le_of_lt (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne p)))),
    ZMod.natCast_self, ZMod.natCast_mod, zero_sub]

end SparseIrred.UpperBounds.Section4
