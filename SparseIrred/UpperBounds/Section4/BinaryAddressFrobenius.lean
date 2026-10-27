import SparseIrred.UpperBounds.Section4.BinaryAddressBerkowitz

/-! # Binary Frobenius power calls and deleted-minor instructions -/

namespace SparseIrred.UpperBounds.Section4

open Complexity SparseDiv SparseDiv.StringArith SparseGcd Matrix Polynomial

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def binaryNatMul (a b : List Bool) : List Bool := canonBits (mulBits a b)
@[simp] theorem binaryNatMul_enc (a b : ℕ) : binaryNatMul (encNat a) (encNat b) = encNat (a * b) := by
  simp [binaryNatMul, canonBits, decNat_mulBits]
theorem cobham_binaryNatMul {n : ℕ} {a b : (Fin n → List Bool) → List Bool}
    (ha : Cobham a) (hb : Cobham b) : Cobham fun v ↦ binaryNatMul (a v) (b v) :=
  cobham_canonBits_comp (cobham_mulBits_comp ha hb)

def binaryParitySign (n one negOne : List Bool) : List Bool := binaryBit n negOne one

theorem binaryParitySign_eq {R : Type*} [CommRing R] (er : R → List Bool) (n : ℕ) :
    binaryParitySign (encNat n) (er 1) (er (-1)) = er ((-1) ^ n) := by
  have hp (s : List Bool) : decNat s % 2 = if s.headD false then 1 else 0 := by
    cases s with
    | nil => rfl
    | cons b s => cases b <;> simp [decNat_cons] <;> omega
  have h := hp (encNat n)
  rw [decNat_encNat] at h
  rw [neg_one_pow_eq_pow_mod_two, h]
  simp only [binaryParitySign, binaryBit]
  split <;> simp_all only [↓reduceIte, pow_zero, pow_one]

def binaryFrobeniusEntry (i j : List Bool) : List Bool := false :: false :: binaryFields [i, j]
def binaryFrobeniusDelta (i j : List Bool) : List Bool := false :: true :: binaryFields [i, j]

def binaryFrobeniusInstruction (companion : List Bool → List Bool)
    (dim q zero one negOne addr : List Bool) : List Bool :=
  let i := binaryField 0 addr.tail.tail
  let j := binaryField 1 addr.tail.tail
  binaryBit addr
    (binaryLift [true]
      (binaryProductInstruction (fun query ↦ companion (pairSnd query)) dim zero one addr.tail))
    (binaryBit addr.tail (binaryValue (binaryEq i j negOne zero))
      (binaryBranch .add
        (true :: binaryProductEntry (encNat 0) (binaryNatMul q j) i (encNat 0))
        (binaryFrobeniusDelta i j)))

theorem binaryFrobeniusInstruction_eq {K : Type*} [Field K] [Fintype K]
    (f : K[X]) (hf : 0 < f.natDegree) (er : K → List Bool)
    (companion : List Bool → List Bool)
    (hc : ∀ i j, companion (pair (encNat i.val) (encNat j.val)) = er (coefficientCompanion f i j))
    (a : FrobeniusEntryAddress f.natDegree) :
    binaryFrobeniusInstruction companion (encNat f.natDegree) (encNat (Fintype.card K))
      (er 0) (er 1) (er (-1)) a.binaryCode =
      ((frobeniusEntryProgram f hf).instruction a).binaryCode FrobeniusEntryAddress.binaryCode er := by
  have hcode : ∀ xs : List ℕ, encodeNumerals xs = binaryFields (xs.map encNat) :=
    fun xs ↦ (binaryFields_encNat xs).symm
  cases a with
  | entry i j =>
    simp [binaryFrobeniusInstruction, FrobeniusEntryAddress.binaryCode, binaryBit, hcode,
      binaryBranch, binaryFrobeniusDelta, binaryProductEntry, frobeniusEntryProgram,
      frobeniusEntryInstruction, EntryInstruction.binaryCode, ProductAddress.binaryCode,
      ProductAddress.fields]
  | delta i j =>
    by_cases hij : i = j
    · simp [binaryFrobeniusInstruction, FrobeniusEntryAddress.binaryCode, binaryBit, hcode,
        binaryEq, binaryValue, frobeniusEntryProgram, frobeniusEntryInstruction,
        EntryInstruction.binaryCode, hij]
    · have hv : i.val ≠ j.val := fun hv ↦ hij (Fin.ext hv)
      simp [binaryFrobeniusInstruction, FrobeniusEntryAddress.binaryCode, binaryBit, hcode,
        binaryEq, binaryValue, frobeniusEntryProgram, frobeniusEntryInstruction,
        EntryInstruction.binaryCode, hij, hv]
  | power a =>
    simp only [binaryFrobeniusInstruction, FrobeniusEntryAddress.binaryCode, binaryBit,
      List.headD_cons, List.tail_cons, ↓reduceIte]
    rw [binaryProductInstruction_eq (fun _ ↦ coefficientCompanion f) er
      (fun query ↦ companion (pairSnd query)) (by intro s i j; simpa using hc i j)]
    have h := binaryLift_eq ProductAddress.binaryCode FrobeniusEntryAddress.binaryCode er
      FrobeniusEntryAddress.power [true] (fun _ ↦ rfl)
      ((productProgram (fun _ ↦ coefficientCompanion f)).instruction a)
    change binaryLift [true] (((productProgram (fun _ ↦ coefficientCompanion f)).instruction a).binaryCode
      ProductAddress.binaryCode er) = _
    cases he : (productProgram (fun _ ↦ coefficientCompanion f)).instruction a <;>
      simpa [frobeniusEntryProgram, frobeniusEntryInstruction, he] using h

def binarySuccAbove (deleted index : List Bool) : List Bool :=
  binaryLt index deleted index (binaryNatAdd index (encNat 1))

theorem binarySuccAbove_eq {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    binarySuccAbove (encNat i.val) (encNat j.val) = encNat (i.succAbove j).val := by
  by_cases h : j.val < i.val <;> simp [binarySuccAbove, binaryLt, Fin.succAbove, Fin.lt_def, h]

def binaryMinorRequest (row col addr : List Bool) : List Bool :=
  let request := binaryBerkowitzRequest addr
  binaryBit request
    (true :: binaryFrobeniusEntry
      (binarySuccAbove row (pairFst request.tail)) (binarySuccAbove col (pairSnd request.tail)))
    [false]

theorem binaryMinorRequest_eq {K : Type*} [Field K] [Fintype K]
    (f : K[X]) (hf : 0 < f.natDegree) (i j : Fin (f.natDegree - 1 + 1))
    (a : BerkowitzAddress (f.natDegree - 1)) :
    binaryMinorRequest (encNat i.val) (encNat j.val) a.binaryCode =
      binaryOptionCode FrobeniusEntryAddress.binaryCode
        (berkowitzSubprogramRequest (frobeniusMinorEntryInitial f hf i j) a) := by
  rw [binaryMinorRequest, binaryBerkowitzRequest_eq]
  cases he : berkowitzEntryRequest a with
  | none => simp [encodeEntryRequest, binaryBit, berkowitzSubprogramRequest, he, binaryOptionCode]
  | some kl =>
    simp [encodeEntryRequest, binaryBit, binarySomeEntry, berkowitzSubprogramRequest, he,
      binaryOptionCode, binarySuccAbove_eq, binaryFrobeniusEntry, frobeniusMinorEntryInitial,
      FrobeniusEntryAddress.binaryCode, ← binaryFields_encNat]

def binaryMinorInstruction (companion : List Bool → List Bool)
    (dim q zero one negOne row col addr : List Bool) : List Bool :=
  let minorDim := binaryNatSub dim (encNat 1)
  binarySubstituteInstruction
    (binaryBerkowitzInstruction (fun _ ↦ zero) minorDim zero one negOne
      (binaryParitySign minorDim one negOne))
    (binaryFrobeniusInstruction companion dim q zero one negOne)
    (binaryMinorRequest row col) zero addr

theorem binaryMinorInstruction_eq {K : Type*} [Field K] [Fintype K]
    (f : K[X]) (hf : 0 < f.natDegree) (er : K → List Bool)
    (companion : List Bool → List Bool)
    (hc : ∀ i j, companion (pair (encNat i.val) (encNat j.val)) = er (coefficientCompanion f i j))
    (i j : Fin (f.natDegree - 1 + 1)) (a : FrobeniusMinorAddress f.natDegree) :
    binaryMinorInstruction companion (encNat f.natDegree) (encNat (Fintype.card K))
      (er 0) (er 1) (er (-1)) (encNat i.val) (encNat j.val) (frobeniusMinorCode a) =
      ((minorProgram f hf i j).instruction a).binaryCode frobeniusMinorCode er := by
  unfold binaryMinorInstruction
  rw [binaryNatSub_enc]
  dsimp only
  rw [binaryParitySign_eq]
  apply binarySubstituteInstruction_eq
  · exact berkowitzSubprogramRequest_rank _ _ _ (fun _ ↦ frobeniusEntryProgram_rank f hf _ _)
  · intro a _
    exact binaryBerkowitzInstruction_eq (0 : Matrix (Fin (f.natDegree - 1))
      (Fin (f.natDegree - 1)) K) er (fun _ ↦ er 0) (fun _ _ ↦ rfl) a
  · exact binaryFrobeniusInstruction_eq f hf er companion hc
  · exact binaryMinorRequest_eq f hf i j
  · intro a b hr
    unfold berkowitzSubprogramRequest at hr
    cases he : berkowitzEntryRequest a with
    | none => simp [he] at hr
    | some ij => exact ⟨_, berkowitzEntryRequest_instruction _ a ij he⟩

theorem cobham_binaryParitySign {n : ℕ} {d o m : (Fin n → List Bool) → List Bool}
    (hd : Cobham d) (ho : Cobham o) (hm : Cobham m) :
    Cobham fun v ↦ binaryParitySign (d v) (o v) (m v) := cobham_binaryBit hd hm ho

theorem cobham_binaryFrobeniusEntry {n : ℕ} {i j : (Fin n → List Bool) → List Bool}
    (hi : Cobham i) (hj : Cobham j) : Cobham fun v ↦ binaryFrobeniusEntry (i v) (j v) :=
  cobham_cons false (cobham_cons false (cobham_pair_comp hi (cobham_pair_comp hj (.const []))))

theorem cobham_binaryFrobeniusDelta {n : ℕ} {i j : (Fin n → List Bool) → List Bool}
    (hi : Cobham i) (hj : Cobham j) : Cobham fun v ↦ binaryFrobeniusDelta (i v) (j v) :=
  cobham_cons false (cobham_cons true (cobham_pair_comp hi (cobham_pair_comp hj (.const []))))

theorem cobham_binaryFrobeniusInstruction {n : ℕ}
    {companion : (Fin n → List Bool) → List Bool → List Bool} (hc : BinaryCobhamFamily companion)
    {dim q zero one negOne addr : (Fin n → List Bool) → List Bool}
    (hd : Cobham dim) (hq : Cobham q) (hz : Cobham zero) (ho : Cobham one)
    (hn : Cobham negOne) (ha : Cobham addr) :
    Cobham fun v ↦ binaryFrobeniusInstruction (companion v) (dim v) (q v)
      (zero v) (one v) (negOne v) (addr v) := by
  have ht := cobham_binaryTail ha
  have htt := cobham_binaryTail ht
  have hi := cobham_binaryField 0 htt
  have hj := cobham_binaryField 1 htt
  exact cobham_binaryBit ha
    (cobham_binaryLift [true] (cobham_binaryProductInstructionWith (n := n)
      (entry := fun v query ↦ companion v (pairSnd query))
      (fun _ h ↦ hc _ (cobham_pairSnd_comp h)) hd hz ho ht))
    (cobham_binaryBit ht (cobham_binaryValue (cobham_binaryEq hi hj hn hz))
      (cobham_binaryBranch .add
        (cobham_cons true (cobham_binaryProductEntry (.const (encNat 0))
          (cobham_binaryNatMul hq hj) hi (.const (encNat 0))))
        (cobham_binaryFrobeniusDelta hi hj)))

theorem cobham_binarySuccAbove {n : ℕ} {d i : (Fin n → List Bool) → List Bool}
    (hd : Cobham d) (hi : Cobham i) : Cobham fun v ↦ binarySuccAbove (d v) (i v) :=
  cobham_binaryLt hi hd hi (cobham_binaryNatAdd hi (.const (encNat 1)))

theorem cobham_binaryMinorRequest {n : ℕ} {r c a : (Fin n → List Bool) → List Bool}
    (hr : Cobham r) (hc : Cobham c) (ha : Cobham a) :
    Cobham fun v ↦ binaryMinorRequest (r v) (c v) (a v) := by
  have hq := cobham_binaryBerkowitzRequest ha
  have ht := cobham_binaryTail hq
  exact cobham_binaryBit hq (cobham_cons true
    (cobham_binaryFrobeniusEntry (cobham_binarySuccAbove hr (cobham_pairFst_comp ht))
      (cobham_binarySuccAbove hc (cobham_pairSnd_comp ht)))) (.const [false])

theorem cobham_binaryMinorInstruction {n : ℕ}
    {companion : (Fin n → List Bool) → List Bool → List Bool} (hc : BinaryCobhamFamily companion)
    {dim q zero one negOne row col addr : (Fin n → List Bool) → List Bool}
    (hd : Cobham dim) (hq : Cobham q) (hz : Cobham zero) (ho : Cobham one) (hn : Cobham negOne)
    (hr : Cobham row) (hl : Cobham col) (ha : Cobham addr) :
    Cobham fun v ↦ binaryMinorInstruction (companion v) (dim v) (q v) (zero v) (one v)
      (negOne v) (row v) (col v) (addr v) := by
  have hm := cobham_binaryNatSub hd (.const (encNat 1))
  apply cobham_binarySubstituteInstruction (n := n)
    (outer := fun v ↦ binaryBerkowitzInstruction (fun _ ↦ zero v)
      (binaryNatSub (dim v) (encNat 1)) (zero v) (one v) (negOne v)
      (binaryParitySign (binaryNatSub (dim v) (encNat 1)) (one v) (negOne v)))
    (inner := fun v ↦ binaryFrobeniusInstruction (companion v) (dim v) (q v) (zero v) (one v) (negOne v))
    (request := fun v ↦ binaryMinorRequest (row v) (col v))
  · intro g hg
    exact cobham_binaryBerkowitzInstruction (fun _ _ ↦ hz) hm hz ho hn
      (cobham_binaryParitySign hm ho hn) hg
  · intro g hg
    exact cobham_binaryFrobeniusInstruction hc hd hq hz ho hn hg
  · intro g hg
    exact cobham_binaryMinorRequest hr hl hg
  · exact hz
  · exact ha

end SparseIrred.UpperBounds.Section4
