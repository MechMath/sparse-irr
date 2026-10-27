import SparseIrred.UpperBounds.Section4.BinaryAddressBasic

/-! # Actual binary decoding of balanced product instructions -/

namespace SparseIrred.UpperBounds.Section4

open Complexity SparseDiv SparseDiv.StringArith SparseGcd

def binaryNatAdd (a b : List Bool) : List Bool := canonBits (addBits a b)
def binaryNatSub (a b : List Bool) : List Bool := canonBits (subBits a b)
def binaryNatHalf (a : List Bool) : List Bool := canonBits a.tail

@[simp] theorem binaryNatAdd_enc (a b : ℕ) :
    binaryNatAdd (encNat a) (encNat b) = encNat (a + b) := by
  simp [binaryNatAdd, canonBits, decNat_addBits]
@[simp] theorem binaryNatSub_enc (a b : ℕ) :
    binaryNatSub (encNat a) (encNat b) = encNat (a - b) := by
  simp [binaryNatSub, canonBits, decNat_subBits]
@[simp] theorem binaryNatHalf_enc (a : ℕ) : binaryNatHalf (encNat a) = encNat (a / 2) := by
  have ht (s : List Bool) : decNat s.tail = decNat s / 2 := by
    cases s with
    | nil => rfl
    | cons b s => cases b <;> simp [decNat_cons] <;> omega
  simp [binaryNatHalf, canonBits, ht]

def binaryProductEntry (s e i j : List Bool) : List Bool :=
  binaryFields [encNat 1, s, e, i, j]
def binaryProductSum (s e i j lo count : List Bool) : List Bool :=
  binaryFields [encNat 2, s, e, i, j, lo, count]
def binaryProductZero : List Bool := binaryFields [encNat 0]

def binaryProductInstruction (entry : List Bool → List Bool)
    (dim zero one addr : List Bool) : List Bool :=
  let tag := binaryField 0 addr
  let s := binaryField 1 addr
  let e := binaryField 2 addr
  let i := binaryField 3 addr
  let j := binaryField 4 addr
  let lo := binaryField 5 addr
  let count := binaryField 6 addr
  let entryCase := binaryEq e (encNat 0) (binaryValue (binaryEq i j one zero))
    (binaryEq e (encNat 1) (binaryValue (entry (pair s (pair i j))))
      (binaryBranch .add (binaryProductSum s e i j (encNat 0) dim) binaryProductZero))
  let atom := binaryLt lo dim
    (binaryBranch .mul (binaryProductEntry s (binaryNatHalf e) i lo)
      (binaryProductEntry (binaryNatAdd s (binaryNatHalf e))
        (binaryNatSub e (binaryNatHalf e)) lo j)) (binaryValue zero)
  let halves := binaryBranch .add
    (binaryProductSum s e i j lo (binaryNatHalf count))
    (binaryProductSum s e i j (binaryNatAdd lo (binaryNatHalf count))
      (binaryNatSub count (binaryNatHalf count)))
  let sumCase := binaryLt e (encNat 2) (binaryValue zero)
    (binaryEq count (encNat 0) (binaryValue zero) (binaryEq count (encNat 1) atom halves))
  binaryEq tag (encNat 0) (binaryValue zero) (binaryEq tag (encNat 1) entryCase sumCase)

theorem binaryProductInstruction_eq {R : Type*} [Semiring R] {n : ℕ}
    (A : ℕ → Matrix (Fin n) (Fin n) R) (encR : R → List Bool)
    (entry : List Bool → List Bool)
    (he : ∀ s i j, entry (pair (encNat s) (pair (encNat i.val) (encNat j.val))) = encR (A s i j))
    (a : ProductAddress n) :
    binaryProductInstruction entry (encNat n) (encR 0) (encR 1) a.binaryCode =
      (productInstruction A a).binaryCode ProductAddress.binaryCode encR := by
  have hcode : ∀ xs : List ℕ, encodeNumerals xs = binaryFields (xs.map encNat) :=
    fun xs ↦ (binaryFields_encNat xs).symm
  cases a with
  | zero =>
    simp [binaryProductInstruction, ProductAddress.binaryCode, ProductAddress.fields, hcode,
      binaryEq, binaryValue, productInstruction, EntryInstruction.binaryCode]
  | entry s e i j =>
    simp only [binaryProductInstruction, ProductAddress.binaryCode, ProductAddress.fields, hcode,
      List.map_cons, List.map_nil, binaryField_binaryFields, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, List.getElem?_nil, Option.getD_none,
      binaryEq, decNat_encNat]
    by_cases h0 : e = 0
    · by_cases hij : i = j
      · simp [h0, hij, binaryValue, productInstruction, EntryInstruction.binaryCode,
          Matrix.one_apply]
      · have hv : i.val ≠ j.val := fun hv ↦ hij (Fin.ext hv)
        simp [h0, hij, hv, binaryValue, productInstruction, EntryInstruction.binaryCode,
          Matrix.one_apply]
    · by_cases h1 : e = 1
      · simp [h0, h1, he, binaryValue, productInstruction, EntryInstruction.binaryCode]
      · simp [h0, h1, binaryBranch, productInstruction, EntryInstruction.binaryCode,
          ProductAddress.binaryCode, ProductAddress.fields, hcode, binaryProductSum,
          binaryProductZero]
  | sum s e i j lo count =>
    simp only [binaryProductInstruction, ProductAddress.binaryCode, ProductAddress.fields, hcode,
      List.map_cons, List.map_nil, binaryField_binaryFields, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, binaryEq, binaryLt, decNat_encNat]
    by_cases he' : e ≤ 1
    · have hh : e < 2 := by omega
      simp [he', hh, binaryValue, productInstruction, EntryInstruction.binaryCode]
    · have hh : ¬e < 2 := by omega
      by_cases h0 : count = 0
      · simp [he', hh, h0, binaryValue, productInstruction, EntryInstruction.binaryCode]
      · by_cases h1 : count = 1
        · by_cases hl : lo < n
          · simp [he', hh, h0, h1, hl, productInstruction, EntryInstruction.binaryCode,
              binaryBranch, binaryProductEntry, ProductAddress.binaryCode, ProductAddress.fields,
              hcode, binaryNatHalf_enc, binaryNatAdd_enc, binaryNatSub_enc]
          · simp [he', hh, h0, h1, hl, binaryValue, productInstruction, EntryInstruction.binaryCode]
        · simp [he', hh, h0, h1, productInstruction, EntryInstruction.binaryCode,
            binaryBranch, binaryProductSum, ProductAddress.binaryCode, ProductAddress.fields,
            hcode, binaryNatHalf_enc, binaryNatAdd_enc, binaryNatSub_enc]

theorem cobham_binaryNatAdd {n : ℕ} {a b : (Fin n → List Bool) → List Bool}
    (ha : Cobham a) (hb : Cobham b) : Cobham fun v ↦ binaryNatAdd (a v) (b v) :=
  cobham_canonBits_comp (cobham_addBits_comp ha hb)
theorem cobham_binaryNatSub {n : ℕ} {a b : (Fin n → List Bool) → List Bool}
    (ha : Cobham a) (hb : Cobham b) : Cobham fun v ↦ binaryNatSub (a v) (b v) :=
  cobham_canonBits_comp (cobham_subBits_comp ha hb)
theorem cobham_binaryNatHalf {n : ℕ} {a : (Fin n → List Bool) → List Bool}
    (ha : Cobham a) : Cobham fun v ↦ binaryNatHalf (a v) :=
  cobham_canonBits_comp (cobham_binaryTail ha)

theorem cobham_binaryProductEntry {n : ℕ} {s e i j : (Fin n → List Bool) → List Bool}
    (hs : Cobham s) (he : Cobham e) (hi : Cobham i) (hj : Cobham j) :
    Cobham fun v ↦ binaryProductEntry (s v) (e v) (i v) (j v) :=
  cobham_pair_comp (.const _) (cobham_pair_comp hs (cobham_pair_comp he
    (cobham_pair_comp hi (cobham_pair_comp hj (.const [])))))
theorem cobham_binaryProductSum {n : ℕ} {s e i j lo count : (Fin n → List Bool) → List Bool}
    (hs : Cobham s) (he : Cobham e) (hi : Cobham i) (hj : Cobham j)
    (hl : Cobham lo) (hc : Cobham count) :
    Cobham fun v ↦ binaryProductSum (s v) (e v) (i v) (j v) (lo v) (count v) :=
  cobham_pair_comp (.const _) (cobham_pair_comp hs (cobham_pair_comp he
    (cobham_pair_comp hi (cobham_pair_comp hj (cobham_pair_comp hl
      (cobham_pair_comp hc (.const [])))))))

theorem cobham_binaryProductInstructionWith {n : ℕ}
    {entry : (Fin n → List Bool) → List Bool → List Bool} (he : BinaryCobhamFamily entry)
    {dim zero one addr : (Fin n → List Bool) → List Bool}
    (hd : Cobham dim) (hz : Cobham zero) (ho : Cobham one) (ha : Cobham addr) :
    Cobham fun v ↦ binaryProductInstruction (entry v) (dim v) (zero v) (one v) (addr v) := by
  have ht := cobham_binaryField 0 ha
  have hs := cobham_binaryField 1 ha
  have hl := cobham_binaryField 2 ha
  have hi := cobham_binaryField 3 ha
  have hj := cobham_binaryField 4 ha
  have hlo := cobham_binaryField 5 ha
  have hc := cobham_binaryField 6 ha
  have hh := cobham_binaryNatHalf hl
  have hch := cobham_binaryNatHalf hc
  have hzv := cobham_binaryValue hz
  have hentry := cobham_binaryEq hl (.const (encNat 0))
    (cobham_binaryValue (cobham_binaryEq hi hj ho hz))
    (cobham_binaryEq hl (.const (encNat 1))
      (cobham_binaryValue (he _ (cobham_pair_comp hs (cobham_pair_comp hi hj))))
      (cobham_binaryBranch .add (cobham_binaryProductSum hs hl hi hj (.const (encNat 0)) hd)
        (Cobham.const binaryProductZero)))
  have hatom := cobham_binaryLt hlo hd
    (cobham_binaryBranch .mul (cobham_binaryProductEntry hs hh hi hlo)
      (cobham_binaryProductEntry (cobham_binaryNatAdd hs hh)
        (cobham_binaryNatSub hl hh) hlo hj)) hzv
  have hhalves := cobham_binaryBranch .add
    (cobham_binaryProductSum hs hl hi hj hlo hch)
    (cobham_binaryProductSum hs hl hi hj (cobham_binaryNatAdd hlo hch)
      (cobham_binaryNatSub hc hch))
  exact cobham_binaryEq ht (.const (encNat 0)) hzv
    (cobham_binaryEq ht (.const (encNat 1)) hentry
      (cobham_binaryLt hl (.const (encNat 2)) hzv
        (cobham_binaryEq hc (.const (encNat 0)) hzv
          (cobham_binaryEq hc (.const (encNat 1)) hatom hhalves))))

theorem cobham_binaryProductInstruction {n : ℕ} {entry : List Bool → List Bool}
    (he : Cobham fun v : Fin 1 → List Bool ↦ entry (v 0))
    {dim zero one addr : (Fin n → List Bool) → List Bool}
    (hd : Cobham dim) (hz : Cobham zero) (ho : Cobham one) (ha : Cobham addr) :
    Cobham fun v ↦ binaryProductInstruction entry (dim v) (zero v) (one v) (addr v) :=
  cobham_binaryProductInstructionWith (fun _ hg ↦ cobham_binaryCompose he hg) hd hz ho ha

end SparseIrred.UpperBounds.Section4
