import SparseIrred.UpperBounds.Machine.StreamingBinaryInputFrame
import SparseDivComplexity.StringArith.Add
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.List

/-! # Complete framed-word decoding by a fixed binary-counter loop -/
namespace SparseIrred.UpperBounds.Machine
open Complexity BinaryRoutine SparseDiv SparseDiv.StringArith

/-- The first `processed` payload bits have been consumed, or the reader has finished. -/
def frameInputStage {k : ℕ} (payload rest : List Bool) (limit processed counter : ℕ)
    (extra : Fin k → ℕ) : BinaryValues (5 + (8 + k)) :=
  if processed ≤ payload.length then
    frameInputValues (packedInput (delimit (payload.drop processed) ++ rest))
      (decNat (payload.take processed)) (2 ^ processed) 0 counter limit extra
  else
    frameInputValues (packedInput rest) (decNat payload) (2 ^ payload.length) 1 counter limit extra

@[simp] theorem frameInputStage_counter {k : ℕ} (payload rest : List Bool)
    (limit processed counter : ℕ) (extra : Fin k → ℕ) :
    frameInputStage payload rest limit processed counter extra (frameInputReg k 6) = counter := by
  unfold frameInputStage
  split_ifs <;> simp

@[simp] theorem frameInputStage_limit {k : ℕ} (payload rest : List Bool)
    (limit processed counter : ℕ) (extra : Fin k → ℕ) :
    frameInputStage payload rest limit processed counter extra (frameInputReg k 7) = limit := by
  unfold frameInputStage
  split_ifs <;> simp

theorem frameInputValues_update_counter {k : ℕ} (n acc power done i limit j : ℕ) (extra : Fin k → ℕ) :
    Function.update (frameInputValues n acc power done i limit extra) (frameInputReg k 6) j =
      frameInputValues n acc power done j limit extra := by
  funext p
  refine Fin.addCases (fun p ↦ ?_) (fun p ↦ ?_) p
  · change Function.update (frameInputValues n acc power done i limit extra) (frameInputReg k 6) j (inputReg (8 + k) p) =
      frameInputValues _ _ _ _ _ _ _ (inputReg (8 + k) p)
    simp
  · refine Fin.addCases (fun p ↦ ?_) (fun p ↦ ?_) p
    · change Function.update (frameInputValues n acc power done i limit extra) (frameInputReg k 6) j (frameInputReg k p) =
        frameInputValues _ _ _ _ _ _ _ (frameInputReg k p)
      fin_cases p <;> simp
    · simp

theorem frameInputStage_update_counter {k : ℕ} (payload rest : List Bool)
    (limit processed counter counter' : ℕ) (extra : Fin k → ℕ) :
    Function.update (frameInputStage payload rest limit processed counter extra)
      (frameInputReg k 6) counter' = frameInputStage payload rest limit processed counter' extra := by
  unfold frameInputStage
  split_ifs <;> exact frameInputValues_update_counter _ _ _ _ _ _ _ _

/-- Exact input/accumulator invariant of one frame-decoding transition. -/
theorem frameInputBody_stage {k : ℕ} (payload rest : List Bool)
    (limit processed counter : ℕ) (extra : Fin k → ℕ) :
    (frameInputBody k).effect (frameInputStage payload rest limit processed counter extra) =
      frameInputStage payload rest limit (processed + 1) counter extra := by
  by_cases hlt : processed < payload.length
  · have hle : processed ≤ payload.length := by omega
    have hle' : processed + 1 ≤ payload.length := by omega
    simp only [frameInputStage, hle, hle', ↓reduceIte]
    rw [List.drop_eq_getElem_cons hlt, delimit_cons, List.cons_append, List.cons_append,
      frameInputBody_payload]
    have htake : decNat (payload.take (processed + 1)) =
        decNat (payload.take processed) + (if payload[processed] then 2 ^ processed else 0) := by
      rw [List.take_succ_eq_append_getElem hlt, decNat_append]
      simp only [List.length_take, min_eq_left hle, decNat_cons, decNat_nil, mul_zero, add_zero]
      cases payload[processed] <;> simp
    rw [htake]
    congr 1
    rw [pow_succ]
    omega
  · by_cases heq : processed = payload.length
    · subst processed
      simp only [frameInputStage, le_refl, Nat.add_one_le_iff, lt_self_iff_false, ↓reduceIte,
        List.drop_length, delimit_nil, List.cons_append, List.nil_append, List.take_length]
      exact frameInputBody_delimiter rest _ _ _ _ extra
    · have hn : ¬processed ≤ payload.length := by omega
      have hn' : ¬processed + 1 ≤ payload.length := by omega
      simp only [frameInputStage, hn, hn', ↓reduceIte]
      exact frameInputBody_done _ _ _ _ _ extra

/-- A literal binary-counter loop; the budget may be exponentially large. -/
def frameInputLoop (k : ℕ) : BinaryRoutine (5 + (8 + k)) :=
  binaryFor (frameInputBody k) (frameInputReg k 6) (frameInputReg k 7)

theorem frameInputLoop_sound (k : ℕ) : (frameInputLoop k).Sound :=
  (frameInputBody_sound k).binaryFor _ _

theorem frameInputLoop_values {k : ℕ} (payload rest : List Bool) (limit count : ℕ)
    (extra : Fin k → ℕ) :
    binaryForValues (frameInputBody k) (frameInputReg k 6)
      (frameInputStage payload rest limit 0 0 extra) count =
        frameInputStage payload rest limit count count extra := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [binaryForValues, ih, binaryForStep, frameInputBody_stage,
      frameInputStage_counter, frameInputStage_update_counter]

theorem frameInputLoop_requires {k : ℕ} (payload rest : List Bool) (limit : ℕ)
    (extra : Fin k → ℕ) :
    (frameInputLoop k).requires (frameInputStage payload rest limit 0 0 extra) := by
  refine ⟨by simp, by simp, ?_⟩
  intro count hc
  rw [frameInputLoop_values]
  refine ⟨?_, ?_, ?_⟩
  · unfold frameInputStage
    split_ifs <;> exact frameInputBody_requires _ _ _ _ _ _ _
  · rw [frameInputBody_stage]
    simp
  · rw [frameInputBody_stage]
    simp

/-- A completed frame reader returns the tail as a packed input and the payload
as its raw natural value plus its separate sentinel weight. -/
theorem frameInputLoop_effect {k : ℕ} (payload rest : List Bool) (limit : ℕ)
    (extra : Fin k → ℕ) (hlen : payload.length + 1 ≤ limit) :
    (frameInputLoop k).effect (frameInputValues (packedInput (pair payload rest)) 0 1 0 0 limit extra) =
      frameInputValues (packedInput rest) (decNat payload) (2 ^ payload.length) 1 limit limit extra := by
  have hinitial : frameInputValues (packedInput (pair payload rest)) 0 1 0 0 limit extra =
      frameInputStage payload rest limit 0 0 extra := by simp [frameInputStage, pair]
  rw [hinitial]
  change binaryForValues (frameInputBody k) (frameInputReg k 6)
    (frameInputStage payload rest limit 0 0 extra)
    (binaryForCount (frameInputReg k 6) (frameInputReg k 7)
      (frameInputStage payload rest limit 0 0 extra)) = _
  simp only [binaryForCount, frameInputStage_counter, frameInputStage_limit, Nat.sub_zero,
    frameInputLoop_values]
  simp [frameInputStage, show ¬limit ≤ payload.length by omega]

theorem frameInputLoop_requires_values {k : ℕ} (payload rest : List Bool) (limit : ℕ)
    (extra : Fin k → ℕ) :
    (frameInputLoop k).requires (frameInputValues (packedInput (pair payload rest)) 0 1 0 0 limit extra) := by
  simpa [frameInputStage, pair] using frameInputLoop_requires payload rest limit extra

theorem packedInput_ge_length (x : List Bool) : x.length + 1 ≤ packedInput x := by
  induction x with
  | nil => simp
  | cons b x ih =>
    rw [List.length_cons, packedInput_cons]
    split <;> omega

theorem frameInputLoop_budget (payload rest : List Bool) :
    payload.length + 1 ≤ packedInput (pair payload rest) := by
  have h := packedInput_ge_length (pair payload rest)
  rw [pair_length] at h
  omega

/-- Clear the thirteen working registers except the packed input cursor. -/
def frameInputClear (k : ℕ) : BinaryRoutine (5 + (8 + k)) :=
  seq (inputReadReset (8 + k)) (seqList
    [clear (frameInputReg k 0), clear (frameInputReg k 1), clear (frameInputReg k 2),
     clear (frameInputReg k 3), clear (frameInputReg k 4), clear (frameInputReg k 5),
     clear (frameInputReg k 6), clear (frameInputReg k 7)])

theorem frameInputClear_sound (k : ℕ) : (frameInputClear k).Sound := by
  apply (inputReadReset_sound _).seq
  apply seqList_sound
  intro routine hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact clear_sound _

private theorem clearList_effect {n : ℕ} (indices : List (Fin n)) (v : BinaryValues n) (j : Fin n) :
    (seqList (indices.map clear)).effect v j = if j ∈ indices then 0 else v j := by
  induction indices generalizing v with
  | nil => simp [seqList, identity, emitBits]
  | cons i is ih =>
    change (seqList (is.map clear)).effect ((clear i).effect v) j = _
    rw [ih]
    by_cases hj : j ∈ is <;> by_cases hji : j = i <;> simp [clear, hj, hji]

private theorem clearList_requires {n : ℕ} (indices : List (Fin n)) (v : BinaryValues n) :
    (seqList (indices.map clear)).requires v := by
  induction indices generalizing v with
  | nil => trivial
  | cons i is ih => exact ⟨trivial, ih _⟩

private theorem routine_seq_effect {n : ℕ} (R T : BinaryRoutine n) (v : BinaryValues n) :
    (seq R T).effect v = T.effect (R.effect v) := rfl

private theorem routine_set_effect {n : ℕ} (idx : Fin n) (value : ℕ) (v : BinaryValues n) :
    (BinaryRoutine.set idx value).effect v = Function.update v idx value := by
  simp only [BinaryRoutine.set, routine_seq_effect, clear, addConst,
    Function.update_self, Nat.zero_add, Function.update_idem]

 theorem frameInputClear_effect {k : ℕ} (v : BinaryValues (5 + (8 + k))) :
    (frameInputClear k).effect v = frameInputValues (v (inputReg (8 + k) 0)) 0 0 0 0 0
      (fun j ↦ v ((j.natAdd 8).natAdd 5)) := by
  funext j
  have hclear : ∀ i, (frameInputClear k).effect v i =
      if i ∈ [frameInputReg k 0, frameInputReg k 1, frameInputReg k 2,
        frameInputReg k 3, frameInputReg k 4, frameInputReg k 5, frameInputReg k 6,
        frameInputReg k 7] then 0 else (inputReadReset (8 + k)).effect v i := by
    intro i
    exact clearList_effect
      [frameInputReg k 0, frameInputReg k 1, frameInputReg k 2, frameInputReg k 3,
        frameInputReg k 4, frameInputReg k 5, frameInputReg k 6, frameInputReg k 7]
      ((inputReadReset (8 + k)).effect v) i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
  · change (frameInputClear k).effect v (inputReg (8 + k) j) =
      frameInputValues _ _ _ _ _ _ _ (inputReg (8 + k) j)
    fin_cases j <;> simp [hclear, inputReadReset_effect]
  · refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
    · change (frameInputClear k).effect v (frameInputReg k j) =
        frameInputValues _ _ _ _ _ _ _ (frameInputReg k j)
      fin_cases j <;> simp [hclear]
    · simp [hclear, inputReadReset_effect]

def frameInputInit (k : ℕ) : BinaryRoutine (5 + (8 + k)) :=
  seq (frameInputClear k) (seq (BinaryRoutine.set (frameInputReg k 2) 1)
    (binaryCopy (inputReg (8 + k) 0) (frameInputReg k 7) (inputReg (8 + k) 4)))

theorem frameInputInit_sound (k : ℕ) : (frameInputInit k).Sound :=
  (frameInputClear_sound k).seq ((set_sound _ _).seq (binaryCopy_sound _ _ _))

theorem frameInputInit_requires {k : ℕ} (v : BinaryValues (5 + (8 + k))) :
    (frameInputInit k).requires v := by
  refine ⟨⟨by simp [inputReadReset, seq, clear], ?_⟩, ⟨?_, ?_⟩⟩
  · exact clearList_requires
      [frameInputReg k 0, frameInputReg k 1, frameInputReg k 2, frameInputReg k 3,
        frameInputReg k 4, frameInputReg k 5, frameInputReg k 6, frameInputReg k 7] _
  · simp [BinaryRoutine.set, seq, clear, addConst]
  · rw [frameInputClear_effect, routine_set_effect]
    simp [binaryCopy]

theorem frameInputInit_effect {k : ℕ} (v : BinaryValues (5 + (8 + k))) :
    (frameInputInit k).effect v =
      frameInputValues (v (inputReg (8 + k) 0)) 0 1 0 0 (v (inputReg (8 + k) 0))
        (fun j ↦ v ((j.natAdd 8).natAdd 5)) := by
  simp only [frameInputInit, routine_seq_effect, frameInputClear_effect, routine_set_effect]
  funext j
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
  · change (_ : BinaryValues (5 + (8 + k))) (inputReg (8 + k) j) =
      frameInputValues _ _ _ _ _ _ _ (inputReg (8 + k) j)
    fin_cases j <;> simp [binaryCopy]
  · refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
    · change (_ : BinaryValues (5 + (8 + k))) (frameInputReg k j) =
        frameInputValues _ _ _ _ _ _ _ (frameInputReg k j)
      fin_cases j <;> simp [binaryCopy]
    · simp [binaryCopy]

/-- A reusable frame decoder with automatically reset scratch registers and budget. -/
def frameInput (k : ℕ) : BinaryRoutine (5 + (8 + k)) := seq (frameInputInit k) (frameInputLoop k)

theorem frameInput_sound (k : ℕ) : (frameInput k).Sound :=
  (frameInputInit_sound k).seq (frameInputLoop_sound k)

theorem frameInput_requires {k : ℕ} (v : BinaryValues (5 + (8 + k))) (payload rest : List Bool)
    (hinput : v (inputReg (8 + k) 0) = packedInput (pair payload rest)) :
    (frameInput k).requires v := by
  refine ⟨frameInputInit_requires v, ?_⟩
  rw [frameInputInit_effect, hinput]
  exact frameInputLoop_requires_values _ _ _ _

theorem frameInput_effect {k : ℕ} (v : BinaryValues (5 + (8 + k))) (payload rest : List Bool)
    (hinput : v (inputReg (8 + k) 0) = packedInput (pair payload rest)) :
    (frameInput k).effect v =
      frameInputValues (packedInput rest) (decNat payload) (2 ^ payload.length) 1
        (packedInput (pair payload rest)) (packedInput (pair payload rest))
        (fun j ↦ v ((j.natAdd 8).natAdd 5)) := by
  simp only [frameInput, seq, frameInputInit_effect, hinput]
  exact frameInputLoop_effect payload rest _ _ (frameInputLoop_budget payload rest)

end SparseIrred.UpperBounds.Machine
