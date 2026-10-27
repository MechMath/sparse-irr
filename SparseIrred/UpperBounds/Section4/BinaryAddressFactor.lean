import SparseIrred.UpperBounds.Section4.BinaryAddressCombinators

/-! # Binary local instructions for the two sums in a Berkowitz factor -/

namespace SparseIrred.UpperBounds.Section4

open Complexity SparseDiv SparseDiv.StringArith SparseGcd

def binaryFactorRow (s k : List Bool) : List Bool := binaryFields [encNat 6, s, k]
def binaryFactorCol (s k : List Bool) : List Bool := binaryFields [encNat 7, s, k]
def binaryFactorDiag (s : List Bool) : List Bool := binaryFields [encNat 8, s]
def binaryFactorTerm (tag : ℕ) (s e k l : List Bool) : List Bool :=
  binaryFields [encNat tag, s, e, k, l]
def binaryFactorRows (s e lo count : List Bool) : List Bool :=
  binaryFields [encNat 1, s, e, lo, count]
def binaryFactorCols (s e k lo count : List Bool) : List Bool :=
  binaryFields [encNat 2, s, e, k, lo, count]
def binaryFactorEntry (s i j : List Bool) : List Bool := binaryFields [encNat 0, s, i, j]
def binaryFactorZero : List Bool := binaryFields [encNat 10]
def binaryFactorNegOne : List Bool := binaryFields [encNat 9]

def binaryTrailingIndex (s k : List Bool) : List Bool :=
  binaryNatAdd (binaryNatAdd s (encNat 1)) k
def binaryTailDimension (dim s : List Bool) : List Bool :=
  binaryNatSub (binaryNatSub dim s) (encNat 1)

/-- The power case returns a dummy zero; the enclosing dispatcher replaces it by a call. -/
def binaryFactorInstruction (entry : List Bool → List Bool)
    (dim zero one negOne addr : List Bool) : List Bool :=
  let tag := binaryField 0 addr
  let s := binaryField 1 addr
  let e := binaryField 2 addr
  let k := binaryField 3 addr
  let l := binaryField 4 addr
  let last := binaryField 5 addr
  let tailDim := binaryTailDimension dim s
  let countLeft := binaryNatHalf l
  let countLast := binaryNatHalf last
  let entryCase :=
    binaryLt e (binaryNatAdd (binaryNatSub dim s) (encNat 1))
      (binaryLt k (binaryNatSub dim s)
        (binaryLt e k (binaryValue zero)
          (binaryEq (binaryNatSub e k) (encNat 0) (binaryValue one)
            (binaryEq (binaryNatSub e k) (encNat 1)
              (binaryBranch .mul binaryFactorNegOne (binaryFactorDiag s))
              (binaryBranch .mul binaryFactorNegOne
                (binaryFactorRows s (binaryNatSub (binaryNatSub e k) (encNat 2))
                  (encNat 0) tailDim))))) (binaryValue zero)) (binaryValue zero)
  let rowsCase := binaryEq l (encNat 0) (binaryValue zero)
    (binaryEq l (encNat 1)
      (binaryLt k tailDim
        (binaryBranch .add (binaryFactorCols s e k (encNat 0) tailDim) binaryFactorZero)
        (binaryValue zero))
      (binaryBranch .add (binaryFactorRows s e k countLeft)
        (binaryFactorRows s e (binaryNatAdd k countLeft) (binaryNatSub l countLeft))))
  let colsCase := binaryEq last (encNat 0) (binaryValue zero)
    (binaryEq last (encNat 1)
      (binaryLt l tailDim
        (binaryBranch .add (binaryFactorTerm 3 s e k l) binaryFactorZero)
        (binaryValue zero))
      (binaryBranch .add (binaryFactorCols s e k l countLast)
        (binaryFactorCols s e k (binaryNatAdd l countLast) (binaryNatSub last countLast))))
  binaryEq tag (encNat 0) entryCase
    (binaryEq tag (encNat 1) rowsCase
      (binaryEq tag (encNat 2) colsCase
        (binaryEq tag (encNat 3)
          (binaryBranch .mul (binaryFactorRow s k) (binaryFactorTerm 4 s e k l))
          (binaryEq tag (encNat 4)
            (binaryBranch .mul (binaryFactorTerm 5 s e k l) (binaryFactorCol s l))
            (binaryEq tag (encNat 6)
              (binaryValue (entry (pair s (binaryTrailingIndex s e))))
              (binaryEq tag (encNat 7)
                (binaryValue (entry (pair (binaryTrailingIndex s e) s)))
                (binaryEq tag (encNat 8) (binaryValue (entry (pair s s)))
                  (binaryEq tag (encNat 9) (binaryValue negOne) (binaryValue zero)))))))))

theorem binaryFactorInstruction_eq {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (encR : R → List Bool) (entry : List Bool → List Bool)
    (he : ∀ i j, entry (pair (encNat i.val) (encNat j.val)) = encR (A i j))
    (a : BerkowitzFactorAddress n)
    (hpow : ∀ s e k l, a ≠ .power s e k l) :
    binaryFactorInstruction entry (encNat n) (encR 0) (encR 1) (encR (-1)) a.binaryCode =
      (berkowitzFactorInstruction A a).binaryCode BerkowitzFactorAddress.binaryCode encR := by
  have hcode : ∀ xs : List ℕ, encodeNumerals xs = binaryFields (xs.map encNat) :=
    fun xs ↦ (binaryFields_encNat xs).symm
  have hb (i j : Fin n) : entry (pair (encNat i.val) (encNat j.val)) = encR (A i j) := he i j
  cases a with
  | power s e k l => exact (hpow s e k l rfl).elim
  | zero | negOne | diag s | row s k | col s k | weighted s e k l | term s e k l =>
    all_goals simp [binaryFactorInstruction, BerkowitzFactorAddress.binaryCode,
      BerkowitzFactorAddress.fields, hcode, binaryEq, binaryLt, binaryValue, binaryBranch,
      binaryFactorDiag, binaryFactorRow, binaryFactorCol, binaryFactorTerm, binaryTrailingIndex,
      binaryTailDimension, berkowitzFactorInstruction, EntryInstruction.binaryCode, hb,
      berkowitzTrailingIndex]
    all_goals first
      | exact he s (berkowitzTrailingIndex s.val k)
      | exact he (berkowitzTrailingIndex s.val k) s
  | rows s e lo count =>
    simp only [binaryFactorInstruction, BerkowitzFactorAddress.binaryCode,
      BerkowitzFactorAddress.fields, hcode, List.map_cons, List.map_nil,
      binaryField_binaryFields, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, List.getElem?_nil, Option.getD_none, binaryEq, binaryLt, decNat_encNat,
      binaryTailDimension, binaryNatSub_enc]
    by_cases h0 : count = 0
    · simp [h0, binaryValue, berkowitzFactorInstruction, EntryInstruction.binaryCode]
    · by_cases h1 : count = 1
      · by_cases hl : lo < n - s.val - 1
        all_goals simp [h0, h1, hl, binaryValue, binaryBranch, berkowitzFactorInstruction,
          EntryInstruction.binaryCode, BerkowitzFactorAddress.binaryCode,
          BerkowitzFactorAddress.fields, hcode, binaryFactorCols, binaryFactorZero]
      · simp [h0, h1, binaryBranch, berkowitzFactorInstruction, EntryInstruction.binaryCode,
          BerkowitzFactorAddress.binaryCode, BerkowitzFactorAddress.fields, hcode, binaryFactorRows]
  | cols s e k lo count =>
    simp only [binaryFactorInstruction, BerkowitzFactorAddress.binaryCode,
      BerkowitzFactorAddress.fields, hcode, List.map_cons, List.map_nil,
      binaryField_binaryFields, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, List.getElem?_nil, Option.getD_none, binaryEq, binaryLt, decNat_encNat,
      binaryTailDimension, binaryNatSub_enc]
    by_cases h0 : count = 0
    · simp [h0, binaryValue, berkowitzFactorInstruction, EntryInstruction.binaryCode]
    · by_cases h1 : count = 1
      · by_cases hl : lo < n - s.val - 1
        all_goals simp [h0, h1, hl, binaryValue, binaryBranch, berkowitzFactorInstruction,
          EntryInstruction.binaryCode, BerkowitzFactorAddress.binaryCode,
          BerkowitzFactorAddress.fields, hcode, binaryFactorTerm, binaryFactorZero]
      · simp [h0, h1, binaryBranch, berkowitzFactorInstruction, EntryInstruction.binaryCode,
          BerkowitzFactorAddress.binaryCode, BerkowitzFactorAddress.fields, hcode, binaryFactorCols]
  | entry s i j =>
    simp only [binaryFactorInstruction, BerkowitzFactorAddress.binaryCode,
      BerkowitzFactorAddress.fields, hcode, List.map_cons, List.map_nil,
      binaryField_binaryFields, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, List.getElem?_nil, Option.getD_none, binaryEq, binaryLt, decNat_encNat,
      binaryTailDimension, binaryNatSub_enc, binaryNatAdd_enc]
    by_cases hi : i.val < n - s.val + 1
    · by_cases hj : j.val < n - s.val
      · by_cases hij : i.val < j.val
        · have hnot : ¬j.val ≤ i.val := by omega
          simp [hi, hj, hij, hnot, binaryValue, berkowitzFactorInstruction,
            EntryInstruction.binaryCode]
        · have hle : j.val ≤ i.val := by omega
          by_cases h0 : i.val - j.val = 0
          · simp [hi, hj, hij, hle, h0, binaryValue, berkowitzFactorInstruction,
              EntryInstruction.binaryCode]
          · by_cases h1 : i.val - j.val = 1
            · simp [hi, hj, hij, hle, h0, h1, binaryValue, binaryBranch,
                berkowitzFactorInstruction, EntryInstruction.binaryCode,
                BerkowitzFactorAddress.binaryCode, BerkowitzFactorAddress.fields, hcode,
                binaryFactorDiag, binaryFactorNegOne]
            · simp [hi, hj, hij, hle, h0, h1, binaryValue, binaryBranch,
                berkowitzFactorInstruction, EntryInstruction.binaryCode,
                BerkowitzFactorAddress.binaryCode, BerkowitzFactorAddress.fields, hcode,
                binaryFactorRows, binaryFactorNegOne]
      · simp [hi, hj, binaryValue, berkowitzFactorInstruction, EntryInstruction.binaryCode]
    · simp [hi, binaryValue, berkowitzFactorInstruction, EntryInstruction.binaryCode]

theorem cobham_binaryFactorRow {n : ℕ} {s k : (Fin n → List Bool) → List Bool}
    (hs : Cobham s) (hk : Cobham k) : Cobham fun v ↦ binaryFactorRow (s v) (k v) :=
  cobham_pair_comp (.const _) (cobham_pair_comp hs (cobham_pair_comp hk (.const [])))
theorem cobham_binaryFactorCol {n : ℕ} {s k : (Fin n → List Bool) → List Bool}
    (hs : Cobham s) (hk : Cobham k) : Cobham fun v ↦ binaryFactorCol (s v) (k v) :=
  cobham_pair_comp (.const _) (cobham_pair_comp hs (cobham_pair_comp hk (.const [])))
theorem cobham_binaryFactorDiag {n : ℕ} {s : (Fin n → List Bool) → List Bool}
    (hs : Cobham s) : Cobham fun v ↦ binaryFactorDiag (s v) :=
  cobham_pair_comp (.const _) (cobham_pair_comp hs (.const []))
theorem cobham_binaryFactorTerm {n : ℕ} (tag : ℕ)
    {s e k l : (Fin n → List Bool) → List Bool}
    (hs : Cobham s) (he : Cobham e) (hk : Cobham k) (hl : Cobham l) :
    Cobham fun v ↦ binaryFactorTerm tag (s v) (e v) (k v) (l v) :=
  cobham_pair_comp (.const _) (cobham_pair_comp hs (cobham_pair_comp he
    (cobham_pair_comp hk (cobham_pair_comp hl (.const [])))))
theorem cobham_binaryFactorRows {n : ℕ} {s e l c : (Fin n → List Bool) → List Bool}
    (hs : Cobham s) (he : Cobham e) (hl : Cobham l) (hc : Cobham c) :
    Cobham fun v ↦ binaryFactorRows (s v) (e v) (l v) (c v) :=
  cobham_binaryFactorTerm 1 hs he hl hc
theorem cobham_binaryFactorCols {n : ℕ} {s e k l c : (Fin n → List Bool) → List Bool}
    (hs : Cobham s) (he : Cobham e) (hk : Cobham k) (hl : Cobham l) (hc : Cobham c) :
    Cobham fun v ↦ binaryFactorCols (s v) (e v) (k v) (l v) (c v) :=
  cobham_pair_comp (.const _) (cobham_pair_comp hs (cobham_pair_comp he
    (cobham_pair_comp hk (cobham_pair_comp hl (cobham_pair_comp hc (.const []))))))
theorem cobham_binaryFactorEntry {n : ℕ} {s i j : (Fin n → List Bool) → List Bool}
    (hs : Cobham s) (hi : Cobham i) (hj : Cobham j) :
    Cobham fun v ↦ binaryFactorEntry (s v) (i v) (j v) :=
  cobham_pair_comp (.const _) (cobham_pair_comp hs (cobham_pair_comp hi
    (cobham_pair_comp hj (.const []))))
theorem cobham_binaryTrailingIndex {n : ℕ} {s k : (Fin n → List Bool) → List Bool}
    (hs : Cobham s) (hk : Cobham k) : Cobham fun v ↦ binaryTrailingIndex (s v) (k v) :=
  cobham_binaryNatAdd (cobham_binaryNatAdd hs (.const _)) hk
theorem cobham_binaryTailDimension {n : ℕ} {d s : (Fin n → List Bool) → List Bool}
    (hd : Cobham d) (hs : Cobham s) : Cobham fun v ↦ binaryTailDimension (d v) (s v) :=
  cobham_binaryNatSub (cobham_binaryNatSub hd hs) (.const _)

theorem cobham_binaryFactorInstruction {n : ℕ}
    {entry : (Fin n → List Bool) → List Bool → List Bool} (he : BinaryCobhamFamily entry)
    {dim zero one negOne addr : (Fin n → List Bool) → List Bool}
    (hd : Cobham dim) (hz : Cobham zero) (ho : Cobham one) (hn : Cobham negOne) (ha : Cobham addr) :
    Cobham fun v ↦ binaryFactorInstruction (entry v) (dim v) (zero v) (one v) (negOne v) (addr v) := by
  have ht := cobham_binaryField 0 ha
  have hs := cobham_binaryField 1 ha
  have he' := cobham_binaryField 2 ha
  have hk := cobham_binaryField 3 ha
  have hl := cobham_binaryField 4 ha
  have hm := cobham_binaryField 5 ha
  have htail := cobham_binaryTailDimension hd hs
  have hh := cobham_binaryNatHalf hl
  have hh' := cobham_binaryNatHalf hm
  have hzv := cobham_binaryValue hz
  have hdiff := cobham_binaryNatSub he' hk
  have hentry := cobham_binaryLt he' (cobham_binaryNatAdd (cobham_binaryNatSub hd hs) (.const (encNat 1)))
    (cobham_binaryLt hk (cobham_binaryNatSub hd hs)
      (cobham_binaryLt he' hk hzv
        (cobham_binaryEq hdiff (.const (encNat 0)) (cobham_binaryValue ho)
          (cobham_binaryEq hdiff (.const (encNat 1))
            (cobham_binaryBranch .mul (.const binaryFactorNegOne) (cobham_binaryFactorDiag hs))
            (cobham_binaryBranch .mul (.const binaryFactorNegOne)
              (cobham_binaryFactorRows hs (cobham_binaryNatSub hdiff (.const (encNat 2)))
                (.const (encNat 0)) htail))))) hzv) hzv
  have hrows := cobham_binaryEq hl (.const (encNat 0)) hzv
    (cobham_binaryEq hl (.const (encNat 1))
      (cobham_binaryLt hk htail
        (cobham_binaryBranch .add (cobham_binaryFactorCols hs he' hk (.const (encNat 0)) htail)
          (.const binaryFactorZero)) hzv)
      (cobham_binaryBranch .add (cobham_binaryFactorRows hs he' hk hh)
        (cobham_binaryFactorRows hs he' (cobham_binaryNatAdd hk hh) (cobham_binaryNatSub hl hh))))
  have hcols := cobham_binaryEq hm (.const (encNat 0)) hzv
    (cobham_binaryEq hm (.const (encNat 1))
      (cobham_binaryLt hl htail
        (cobham_binaryBranch .add (cobham_binaryFactorTerm 3 hs he' hk hl) (.const binaryFactorZero)) hzv)
      (cobham_binaryBranch .add (cobham_binaryFactorCols hs he' hk hl hh')
        (cobham_binaryFactorCols hs he' hk (cobham_binaryNatAdd hl hh') (cobham_binaryNatSub hm hh'))))
  exact cobham_binaryEq ht (.const (encNat 0)) hentry
    (cobham_binaryEq ht (.const (encNat 1)) hrows
      (cobham_binaryEq ht (.const (encNat 2)) hcols
        (cobham_binaryEq ht (.const (encNat 3))
          (cobham_binaryBranch .mul (cobham_binaryFactorRow hs hk) (cobham_binaryFactorTerm 4 hs he' hk hl))
          (cobham_binaryEq ht (.const (encNat 4))
            (cobham_binaryBranch .mul (cobham_binaryFactorTerm 5 hs he' hk hl) (cobham_binaryFactorCol hs hl))
            (cobham_binaryEq ht (.const (encNat 6))
              (cobham_binaryValue (he _ (cobham_pair_comp hs (cobham_binaryTrailingIndex hs he'))))
              (cobham_binaryEq ht (.const (encNat 7))
                (cobham_binaryValue (he _ (cobham_pair_comp (cobham_binaryTrailingIndex hs he') hs)))
                (cobham_binaryEq ht (.const (encNat 8)) (cobham_binaryValue (he _ (cobham_pair_comp hs hs)))
                  (cobham_binaryEq ht (.const (encNat 9)) (cobham_binaryValue hn) hzv))))))))

end SparseIrred.UpperBounds.Section4
