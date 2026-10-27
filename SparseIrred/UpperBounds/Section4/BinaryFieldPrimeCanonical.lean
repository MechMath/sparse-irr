import SparseIrred.UpperBounds.Section4.BinaryField

/-! # Exact canonical outputs for prime-field operations -/

namespace SparseIrred.UpperBounds.Section4

open Complexity SparseDiv SparseDiv.StringArith SparseGcd

theorem primeAddStr_encoded (p : ℕ) [NeZero p] (a b : ZMod p) :
    primeAddStr (encNat p) (encNat a.val) (encNat b.val) = encNat (a + b).val := by
  rw [primeAddStr_eq_zmod_val, decNat_encNat, decNat_encNat,
    ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

theorem primeMulStr_encoded (p : ℕ) [NeZero p] (a b : ZMod p) :
    primeMulStr (encNat p) (encNat a.val) (encNat b.val) = encNat (a * b).val := by
  rw [primeMulStr_eq_zmod_val, decNat_encNat, decNat_encNat,
    ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

theorem primeNegStr_encoded (p : ℕ) [NeZero p] (a : ZMod p) :
    primeNegStr (encNat p) (encNat a.val) = encNat (-a).val := by
  rw [primeNegStr_eq_zmod_val, decNat_encNat, ZMod.natCast_zmod_val]

theorem primeSubStr_encoded (p : ℕ) [NeZero p] (a b : ZMod p) :
    primeSubStr (encNat p) (encNat a.val) (encNat b.val) = encNat (a - b).val := by
  rw [primeSubStr, primeNegStr_encoded, primeAddStr_encoded, sub_eq_add_neg]

theorem primePowStr_encoded (p : ℕ) [NeZero p] (a : ZMod p) (e : List Bool) :
    primePowStr (encNat p) (encNat a.val) e = encNat (a ^ decNat e).val := by
  rw [primePowStr, powModStr_eq_encNat _ _ _ (by simpa using NeZero.ne p)]
  simp only [powMod, decNat_encNat]
  congr 1
  have he : a ^ decNat e = ((a.val ^ decNat e : ℕ) : ZMod p) := by
    rw [Nat.cast_pow, ZMod.natCast_zmod_val]
  rw [he, ZMod.val_natCast]

theorem primeInvStr_encoded (p : ℕ) [Fact p.Prime] (a : ZMod p) :
    primeInvStr (encNat p) (encNat a.val) = encNat a⁻¹.val := by
  have hr : redStr (encNat a.val) (encNat p) = encNat a.val := by
    rw [redStr_eq_zmod_val, decNat_encNat, ZMod.natCast_zmod_val]
  unfold primeInvStr
  rw [hr]
  by_cases ha : a = 0
  · subst a
    rw [(isZeroBits_eq_true_iff _).mpr (by simp)]
    simp
    rfl
  · have hv : decNat (encNat a.val) ≠ 0 := by
      rw [decNat_encNat]
      exact fun h ↦ ha (ZMod.val_injective p (by simpa using h))
    rw [isZeroBits_eq_false hv, caseBit₀_cons, Bool.cond_false, primePowStr_encoded,
      decNat_subBits, decNat_encNat, decNat_encNat]
    have he : a ^ (p - 2) = a⁻¹ := by
      simpa only [ZMod.card] using finiteField_pow_card_sub_two a ha
    rw [he]

end SparseIrred.UpperBounds.Section4
