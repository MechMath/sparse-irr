import SparseIrred.UpperBounds.Section4.BinaryAddressFactor

/-! # Polynomial-time recognition of matrix-entry requests -/

namespace SparseIrred.UpperBounds.Section4

open Complexity SparseDiv SparseDiv.StringArith SparseGcd

def binarySomeEntry (i j : List Bool) : List Bool := true :: pair i j

def binaryFactorRequest (addr : List Bool) : List Bool :=
  let tag := binaryField 0 addr
  let s := binaryField 1 addr
  let k := binaryField 2 addr
  binaryEq tag (encNat 8) (binarySomeEntry s s)
    (binaryEq tag (encNat 6) (binarySomeEntry s (binaryTrailingIndex s k))
      (binaryEq tag (encNat 7) (binarySomeEntry (binaryTrailingIndex s k) s) [false]))

def binaryPowerRequest (addr : List Bool) : List Bool :=
  let s := pairFst addr
  let p := pairSnd addr
  binaryEq (binaryField 0 p) (encNat 1)
    (binaryEq (binaryField 2 p) (encNat 1)
      (binarySomeEntry (binaryTrailingIndex s (binaryField 3 p))
        (binaryTrailingIndex s (binaryField 4 p))) [false]) [false]

/-- `false` denotes no oracle query; `true` is followed by the pair of binary indices. -/
def binaryBerkowitzRequest (addr : List Bool) : List Bool :=
  binaryBit addr
    (binaryBit addr.tail
      (binaryBit addr.tail.tail [false]
        (binaryBit addr.tail.tail.tail
          (binaryBit addr.tail.tail.tail.tail [false]
            (binaryPowerRequest addr.tail.tail.tail.tail.tail))
          (binaryFactorRequest addr.tail.tail.tail.tail))) [false]) [false]

def encodeEntryRequest {n : ℕ} : Option (Fin n × Fin n) → List Bool
  | none => [false]
  | some ij => binarySomeEntry (encNat ij.1.val) (encNat ij.2.val)

theorem binaryBerkowitzRequest_eq {n : ℕ} (a : BerkowitzAddress n) :
    binaryBerkowitzRequest a.binaryCode = encodeEntryRequest (berkowitzEntryRequest a) := by
  have hcode : ∀ xs : List ℕ, encodeNumerals xs = binaryFields (xs.map encNat) :=
    fun xs ↦ (binaryFields_encNat xs).symm
  cases a with
  | initial | sign => rfl
  | core a => cases a with
    | outer a | zero => rfl
    | inner a => cases a with
      | zero => rfl
      | outer a =>
        cases a <;>
          simp [binaryBerkowitzRequest, BerkowitzAddress.binaryCode, berkowitzCoreCode,
            berkowitzExpandedFactorCode, SubstituteAddress.binaryCode, binaryBit,
            binaryFactorRequest, BerkowitzFactorAddress.binaryCode, BerkowitzFactorAddress.fields,
            hcode, binaryEq, encodeEntryRequest, berkowitzEntryRequest,
            binarySomeEntry, binaryTrailingIndex, berkowitzTrailingIndex]
      | inner a =>
        rcases a with ⟨s, a⟩
        cases a with
        | zero | sum start len i j lo count =>
          all_goals simp [binaryBerkowitzRequest, BerkowitzAddress.binaryCode, berkowitzCoreCode,
            berkowitzExpandedFactorCode, SubstituteAddress.binaryCode, binaryBit,
            binaryPowerRequest, berkowitzPowerCode, familyCode, ProductAddress.binaryCode,
            ProductAddress.fields, hcode, binaryEq, encodeEntryRequest, berkowitzEntryRequest]
        | entry start len i j =>
          by_cases h1 : len = 1
          all_goals simp [binaryBerkowitzRequest, BerkowitzAddress.binaryCode, berkowitzCoreCode,
            berkowitzExpandedFactorCode, SubstituteAddress.binaryCode, binaryBit,
            binaryPowerRequest, berkowitzPowerCode, familyCode, ProductAddress.binaryCode,
            ProductAddress.fields, hcode, binaryEq, encodeEntryRequest, berkowitzEntryRequest,
            h1, binarySomeEntry, binaryTrailingIndex, berkowitzTrailingIndex]

theorem cobham_binarySomeEntry {n : ℕ} {i j : (Fin n → List Bool) → List Bool}
    (hi : Cobham i) (hj : Cobham j) : Cobham fun v ↦ binarySomeEntry (i v) (j v) :=
  cobham_cons true (cobham_pair_comp hi hj)

theorem cobham_binaryFactorRequest {n : ℕ} {addr : (Fin n → List Bool) → List Bool}
    (ha : Cobham addr) : Cobham fun v ↦ binaryFactorRequest (addr v) := by
  have ht := cobham_binaryField 0 ha
  have hs := cobham_binaryField 1 ha
  have hk := cobham_binaryField 2 ha
  exact cobham_binaryEq ht (.const (encNat 8)) (cobham_binarySomeEntry hs hs)
    (cobham_binaryEq ht (.const (encNat 6))
      (cobham_binarySomeEntry hs (cobham_binaryTrailingIndex hs hk))
      (cobham_binaryEq ht (.const (encNat 7))
        (cobham_binarySomeEntry (cobham_binaryTrailingIndex hs hk) hs) (.const [false])))

theorem cobham_binaryPowerRequest {n : ℕ} {addr : (Fin n → List Bool) → List Bool}
    (ha : Cobham addr) : Cobham fun v ↦ binaryPowerRequest (addr v) := by
  have hs := cobham_pairFst_comp ha
  have hp := cobham_pairSnd_comp ha
  exact cobham_binaryEq (cobham_binaryField 0 hp) (.const (encNat 1))
    (cobham_binaryEq (cobham_binaryField 2 hp) (.const (encNat 1))
      (cobham_binarySomeEntry (cobham_binaryTrailingIndex hs (cobham_binaryField 3 hp))
        (cobham_binaryTrailingIndex hs (cobham_binaryField 4 hp))) (.const [false])) (.const [false])

theorem cobham_binaryBerkowitzRequest {n : ℕ} {addr : (Fin n → List Bool) → List Bool}
    (ha : Cobham addr) : Cobham fun v ↦ binaryBerkowitzRequest (addr v) := by
  have h1 := cobham_binaryTail ha
  have h2 := cobham_binaryTail h1
  have h3 := cobham_binaryTail h2
  have h4 := cobham_binaryTail h3
  have h5 := cobham_binaryTail h4
  exact cobham_binaryBit ha
    (cobham_binaryBit h1 (cobham_binaryBit h2 (.const [false])
      (cobham_binaryBit h3 (cobham_binaryBit h4 (.const [false])
        (cobham_binaryPowerRequest h5)) (cobham_binaryFactorRequest h4))) (.const [false]))
    (.const [false])

theorem binaryBerkowitzRequest_mem_FP : binaryBerkowitzRequest ∈ FP :=
  CobhamFP_subset_FP (cobham_binaryBerkowitzRequest (.proj 0))

end SparseIrred.UpperBounds.Section4
