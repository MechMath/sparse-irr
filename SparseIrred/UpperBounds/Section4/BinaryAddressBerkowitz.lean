import SparseIrred.UpperBounds.Section4.BinaryAddressOracle
import SparseIrred.UpperBounds.Section4.BinaryAddressSubstitute

/-! # Fully expanded binary Berkowitz instruction decoding -/

namespace SparseIrred.UpperBounds.Section4

open Complexity SparseDiv SparseDiv.StringArith SparseGcd Matrix

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def binaryPowerLocal (entry : List Bool → List Bool) (dim zero one query : List Bool) : List Bool :=
  let s := pairFst query
  binaryProductInstruction (fun q ↦ entry
    (pair (binaryTrailingIndex s (pairFst (pairSnd q)))
      (binaryTrailingIndex s (pairSnd (pairSnd q)))))
    (binaryTailDimension dim s) zero one (pairSnd query)

def binaryFactorPowerRequest (a : List Bool) : List Bool :=
  binaryEq (binaryField 0 a) (encNat 5)
    (true :: pair (binaryField 1 a)
      (binaryProductEntry (encNat 0) (binaryField 2 a) (binaryField 3 a) (binaryField 4 a))) [false]

def binaryExpandedFactorInstruction (entry : List Bool → List Bool)
    (dim zero one negOne addr : List Bool) : List Bool :=
  binarySubstituteInstruction (binaryFactorInstruction entry dim zero one negOne)
    (binaryFamilyInstruction (binaryPowerLocal entry dim zero one)) binaryFactorPowerRequest zero addr

def binaryProductFactorRequest (dim addr : List Bool) : List Bool :=
  binaryEq (binaryField 0 addr) (encNat 1)
    (binaryEq (binaryField 2 addr) (encNat 1)
      (binaryLt (binaryField 1 addr) dim
        (true :: false :: binaryFactorEntry (binaryField 1 addr) (binaryField 3 addr)
          (binaryField 4 addr)) [false]) [false]) [false]

def binaryCoreInstruction (entry : List Bool → List Bool)
    (dim zero one negOne addr : List Bool) : List Bool :=
  binarySubstituteInstruction
    (binaryProductInstruction (fun q ↦ binaryEq (pairFst (pairSnd q)) (pairSnd (pairSnd q)) one zero)
      (binaryNatAdd dim (encNat 1)) zero one)
    (binaryExpandedFactorInstruction entry dim zero one negOne)
    (binaryProductFactorRequest dim) zero addr

def binaryBerkowitzInitial (_dim : List Bool) : List Bool := [false, false]

def binaryBerkowitzInstruction (entry : List Bool → List Bool)
    (dim zero one negOne sign addr : List Bool) : List Bool :=
  binaryBit addr (binaryLift [true] (binaryCoreInstruction entry dim zero one negOne addr.tail))
    (binaryBit addr.tail (binaryValue sign)
      (binaryBranch .mul [false, true]
        (true :: false :: binaryProductEntry (encNat 0) dim dim (encNat 0))))

theorem binaryPowerLocal_eq {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (er : R → List Bool) (entry : List Bool → List Bool)
    (he : ∀ i j, entry (pair (encNat i.val) (encNat j.val)) = er (A i j))
    (s : Fin n) (a : ProductAddress (n - s.val - 1)) :
    binaryPowerLocal entry (encNat n) (er 0) (er 1) (pair (encNat s.val) a.binaryCode) =
      ((productProgram (fun _ ↦ berkowitzStrictTail A s)).instruction a).binaryCode
        ProductAddress.binaryCode er := by
  simp only [binaryPowerLocal, pairFst_pair, pairSnd_pair, binaryTailDimension, binaryNatSub_enc]
  apply binaryProductInstruction_eq
  intro st i j
  simp only [pairFst_pair, pairSnd_pair, binaryTrailingIndex, binaryNatAdd_enc]
  exact he (berkowitzTrailingIndex s.val i) (berkowitzTrailingIndex s.val j)

theorem binaryFactorPowerRequest_eq {n : ℕ} (a : BerkowitzFactorAddress n) :
    binaryFactorPowerRequest a.binaryCode = binaryOptionCode berkowitzPowerCode
      (berkowitzPowerRequest a) := by
  have hc : ∀ xs : List ℕ, encodeNumerals xs = binaryFields (xs.map encNat) :=
    fun xs ↦ (binaryFields_encNat xs).symm
  cases a <;> simp [binaryFactorPowerRequest, BerkowitzFactorAddress.binaryCode,
    BerkowitzFactorAddress.fields, hc, binaryEq, berkowitzPowerRequest, binaryOptionCode,
    berkowitzPowerCode, familyCode, binaryProductEntry, ProductAddress.binaryCode,
    ProductAddress.fields]

theorem binaryExpandedFactorInstruction_eq {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (er : R → List Bool) (entry : List Bool → List Bool)
    (he : ∀ i j, entry (pair (encNat i.val) (encNat j.val)) = er (A i j))
    (a : BerkowitzExpandedFactorAddress n) :
    binaryExpandedFactorInstruction entry (encNat n) (er 0) (er 1) (er (-1))
      (berkowitzExpandedFactorCode a) =
      ((berkowitzExpandedFactorProgram A).instruction a).binaryCode berkowitzExpandedFactorCode er := by
  apply binarySubstituteInstruction_eq
  · intro a hnone
    apply binaryFactorInstruction_eq A er entry he a
    intro s e k l ha
    subst a
    simp [berkowitzPowerRequest] at hnone
  · intro b
    apply binaryFamilyInstruction_eq
    exact binaryPowerLocal_eq A er entry he
  · exact binaryFactorPowerRequest_eq
  · intro a b hr
    cases a <;> simp only [berkowitzPowerRequest] at hr <;> try cases hr
    exact ⟨_, rfl⟩

theorem binaryProductFactorRequest_eq {n : ℕ} (a : ProductAddress (n + 1)) :
    binaryProductFactorRequest (encNat n) a.binaryCode =
      binaryOptionCode berkowitzExpandedFactorCode (berkowitzFactorRequest a) := by
  have hc : ∀ xs : List ℕ, encodeNumerals xs = binaryFields (xs.map encNat) :=
    fun xs ↦ (binaryFields_encNat xs).symm
  cases a with
  | zero | sum s e i j lo count =>
    all_goals simp [binaryProductFactorRequest, ProductAddress.binaryCode,
      ProductAddress.fields, hc, binaryEq, berkowitzFactorRequest, binaryOptionCode]
  | entry s e i j =>
    by_cases he : e = 1
    all_goals by_cases hs : s < n
    all_goals simp [binaryProductFactorRequest, ProductAddress.binaryCode,
      ProductAddress.fields, hc, binaryEq, binaryLt, berkowitzFactorRequest, binaryOptionCode,
      he, hs, berkowitzExpandedFactorCode, SubstituteAddress.binaryCode,
      binaryFactorEntry, BerkowitzFactorAddress.binaryCode, BerkowitzFactorAddress.fields]

theorem binaryCoreInstruction_eq {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (er : R → List Bool) (entry : List Bool → List Bool)
    (he : ∀ i j, entry (pair (encNat i.val) (encNat j.val)) = er (A i j))
    (a : BerkowitzCoreAddress n) :
    binaryCoreInstruction entry (encNat n) (er 0) (er 1) (er (-1)) (berkowitzCoreCode a) =
      ((berkowitzCoreProgram A).instruction a).binaryCode berkowitzCoreCode er := by
  apply binarySubstituteInstruction_eq
  · intro a hnone
    rw [binaryNatAdd_enc]
    have hb := binaryProductInstruction_eq
      (fun _ ↦ (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R)) er
      (fun q ↦ binaryEq (pairFst (pairSnd q)) (pairSnd (pairSnd q)) (er 1) (er 0))
      (by
        intro s i j
        by_cases hij : i = j
        · simp [binaryEq, Matrix.one_apply, hij]
        · have hv : i.val ≠ j.val := fun hv ↦ hij (Fin.ext hv)
          simp [binaryEq, Matrix.one_apply, hij, hv]) a
    rw [hb]
    congr 1
    cases a with
    | zero | sum _ _ _ _ _ _ => rfl
    | entry s e i j =>
      by_cases h0 : e = 0
      · simp [productProgram, productInstruction, h0]
      by_cases h1 : e = 1
      · have hs : ¬s < n := by simpa [berkowitzFactorRequest, h1] using hnone
        simp [productProgram, productInstruction, h1, indexedBerkowitzFactor, hs]
      · simp [productProgram, productInstruction, h0, h1]
  · exact binaryExpandedFactorInstruction_eq A er entry he
  · exact binaryProductFactorRequest_eq
  · intro a b hr
    cases a with
    | zero | sum _ _ _ _ _ _ => simp [berkowitzFactorRequest] at hr
    | entry start len i j =>
      simp only [berkowitzFactorRequest] at hr
      split_ifs at hr <;> try cases hr
      subst len
      exact ⟨_, rfl⟩

theorem binaryBerkowitzInstruction_eq {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (er : R → List Bool) (entry : List Bool → List Bool)
    (he : ∀ i j, entry (pair (encNat i.val) (encNat j.val)) = er (A i j))
    (a : BerkowitzAddress n) :
    binaryBerkowitzInstruction entry (encNat n) (er 0) (er 1) (er (-1)) (er ((-1) ^ n)) a.binaryCode =
      ((berkowitzProgram A).instruction a).binaryCode BerkowitzAddress.binaryCode er := by
  cases a with
  | sign => rfl
  | initial =>
    simp [binaryBerkowitzInstruction, BerkowitzAddress.binaryCode, binaryBit, binaryBranch,
      berkowitzProgram, berkowitzInstruction, EntryInstruction.binaryCode, berkowitzCoreInitial,
      berkowitzCoreCode, SubstituteAddress.binaryCode, ProductAddress.binaryCode,
      ProductAddress.fields, binaryProductEntry, ← binaryFields_encNat]
  | core a =>
    simp only [binaryBerkowitzInstruction, BerkowitzAddress.binaryCode, binaryBit,
      List.headD_cons, List.tail_cons, ↓reduceIte, binaryCoreInstruction_eq A er entry he]
    have h := binaryLift_eq berkowitzCoreCode BerkowitzAddress.binaryCode er BerkowitzAddress.core
      [true] (fun _ ↦ rfl) ((berkowitzCoreProgram A).instruction a)
    cases hh : (berkowitzCoreProgram A).instruction a <;>
      simpa [berkowitzProgram, berkowitzInstruction, hh] using h

/-- At non-query addresses the controller can use a zero entry callback. Actual
matrix entries are obtained only by the separately executed oracle coroutine. -/
theorem binaryBerkowitzInstruction_noquery_eq {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (er : R → List Bool) (a : BerkowitzAddress n)
    (ha : berkowitzEntryRequest a = none) :
    binaryBerkowitzInstruction (fun _ ↦ er 0) (encNat n) (er 0) (er 1) (er (-1))
      (er ((-1) ^ n)) a.binaryCode =
      ((berkowitzProgram A).instruction a).binaryCode BerkowitzAddress.binaryCode er := by
  rw [binaryBerkowitzInstruction_eq (0 : Matrix (Fin n) (Fin n) R) er
    (fun _ ↦ er 0) (fun _ _ ↦ rfl)]
  rw [berkowitzEntryRequest_none_instruction (0 : Matrix (Fin n) (Fin n) R) A a ha]

theorem cobham_binaryPowerLocal {n : ℕ}
    {entry : (Fin n → List Bool) → List Bool → List Bool} (he : BinaryCobhamFamily entry)
    {dim zero one query : (Fin n → List Bool) → List Bool}
    (hd : Cobham dim) (hz : Cobham zero) (ho : Cobham one) (hq : Cobham query) :
    Cobham fun v ↦ binaryPowerLocal (entry v) (dim v) (zero v) (one v) (query v) := by
  have hs := cobham_pairFst_comp hq
  exact cobham_binaryProductInstructionWith (n := n)
    (entry := fun v q ↦ entry v (pair
      (binaryTrailingIndex (pairFst (query v)) (pairFst (pairSnd q)))
      (binaryTrailingIndex (pairFst (query v)) (pairSnd (pairSnd q)))))
    (fun _ h ↦ he _ (cobham_pair_comp
      (cobham_binaryTrailingIndex hs (cobham_pairFst_comp (cobham_pairSnd_comp h)))
      (cobham_binaryTrailingIndex hs (cobham_pairSnd_comp (cobham_pairSnd_comp h)))))
    (cobham_binaryTailDimension hd hs) hz ho (cobham_pairSnd_comp hq)

theorem cobham_binaryFactorPowerRequest {n : ℕ} {addr : (Fin n → List Bool) → List Bool}
    (ha : Cobham addr) : Cobham fun v ↦ binaryFactorPowerRequest (addr v) :=
  cobham_binaryEq (cobham_binaryField 0 ha) (.const (encNat 5))
    (cobham_cons true (cobham_pair_comp (cobham_binaryField 1 ha)
      (cobham_binaryProductEntry (.const (encNat 0)) (cobham_binaryField 2 ha)
        (cobham_binaryField 3 ha) (cobham_binaryField 4 ha)))) (.const [false])

theorem cobham_binaryExpandedFactorInstruction {n : ℕ}
    {entry : (Fin n → List Bool) → List Bool → List Bool} (he : BinaryCobhamFamily entry)
    {dim zero one negOne addr : (Fin n → List Bool) → List Bool}
    (hd : Cobham dim) (hz : Cobham zero) (ho : Cobham one) (hn : Cobham negOne) (ha : Cobham addr) :
    Cobham fun v ↦ binaryExpandedFactorInstruction (entry v) (dim v) (zero v) (one v) (negOne v) (addr v) :=
  cobham_binarySubstituteInstruction (n := n)
    (outer := fun v ↦ binaryFactorInstruction (entry v) (dim v) (zero v) (one v) (negOne v))
    (inner := fun v ↦ binaryFamilyInstruction (binaryPowerLocal (entry v) (dim v) (zero v) (one v)))
    (request := fun _ ↦ binaryFactorPowerRequest)
    (fun _ h ↦ cobham_binaryFactorInstruction he hd hz ho hn h)
    (fun _ h ↦ cobham_binaryFamilyInstruction (fun _ h' ↦ cobham_binaryPowerLocal he hd hz ho h') h)
    (fun _ h ↦ cobham_binaryFactorPowerRequest h) hz ha

theorem cobham_binaryProductFactorRequest {n : ℕ}
    {dim addr : (Fin n → List Bool) → List Bool} (hd : Cobham dim) (ha : Cobham addr) :
    Cobham fun v ↦ binaryProductFactorRequest (dim v) (addr v) :=
  cobham_binaryEq (cobham_binaryField 0 ha) (.const (encNat 1))
    (cobham_binaryEq (cobham_binaryField 2 ha) (.const (encNat 1))
      (cobham_binaryLt (cobham_binaryField 1 ha) hd
        (cobham_cons true (cobham_cons false (cobham_binaryFactorEntry (cobham_binaryField 1 ha)
          (cobham_binaryField 3 ha) (cobham_binaryField 4 ha)))) (.const [false]))
      (.const [false])) (.const [false])

theorem cobham_binaryCoreInstruction {n : ℕ}
    {entry : (Fin n → List Bool) → List Bool → List Bool} (he : BinaryCobhamFamily entry)
    {dim zero one negOne addr : (Fin n → List Bool) → List Bool}
    (hd : Cobham dim) (hz : Cobham zero) (ho : Cobham one) (hn : Cobham negOne) (ha : Cobham addr) :
    Cobham fun v ↦ binaryCoreInstruction (entry v) (dim v) (zero v) (one v) (negOne v) (addr v) :=
  cobham_binarySubstituteInstruction (n := n)
    (outer := fun v ↦ binaryProductInstruction
      (fun q ↦ binaryEq (pairFst (pairSnd q)) (pairSnd (pairSnd q)) (one v) (zero v))
      (binaryNatAdd (dim v) (encNat 1)) (zero v) (one v))
    (inner := fun v ↦ binaryExpandedFactorInstruction (entry v) (dim v) (zero v) (one v) (negOne v))
    (request := fun v ↦ binaryProductFactorRequest (dim v))
    (fun _ h ↦ cobham_binaryProductInstructionWith (n := n)
      (entry := fun v q ↦ binaryEq (pairFst (pairSnd q)) (pairSnd (pairSnd q)) (one v) (zero v))
      (fun _ h' ↦ cobham_binaryEq (cobham_pairFst_comp (cobham_pairSnd_comp h'))
        (cobham_pairSnd_comp (cobham_pairSnd_comp h')) ho hz)
      (cobham_binaryNatAdd hd (.const (encNat 1))) hz ho h)
    (fun _ h ↦ cobham_binaryExpandedFactorInstruction he hd hz ho hn h)
    (fun _ h ↦ cobham_binaryProductFactorRequest hd h) hz ha

theorem cobham_binaryBerkowitzInstruction {n : ℕ}
    {entry : (Fin n → List Bool) → List Bool → List Bool} (he : BinaryCobhamFamily entry)
    {dim zero one negOne sign addr : (Fin n → List Bool) → List Bool}
    (hd : Cobham dim) (hz : Cobham zero) (ho : Cobham one) (hn : Cobham negOne)
    (hs : Cobham sign) (ha : Cobham addr) :
    Cobham fun v ↦ binaryBerkowitzInstruction (entry v) (dim v) (zero v) (one v)
      (negOne v) (sign v) (addr v) :=
  cobham_binaryBit ha
    (cobham_binaryLift [true] (cobham_binaryCoreInstruction he hd hz ho hn (cobham_binaryTail ha)))
    (cobham_binaryBit (cobham_binaryTail ha) (cobham_binaryValue hs)
      (cobham_binaryBranch .mul (.const [false, true])
        (cobham_cons true (cobham_cons false
          (cobham_binaryProductEntry (.const (encNat 0)) hd hd (.const (encNat 0)))))))

end SparseIrred.UpperBounds.Section4
