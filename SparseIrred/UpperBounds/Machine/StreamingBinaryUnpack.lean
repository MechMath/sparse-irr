import SparseIrred.UpperBounds.Machine.StreamingBinaryInput
import SparseIrred.UpperBounds.Machine.StreamingBinaryWorkspace
import SparseDivComplexity.StringArith.Sub

/-! # Removing a packed-input sentinel with a linear-space binary routine -/

namespace SparseIrred.UpperBounds.Machine

open Complexity BinaryRoutine SparseDiv SparseDiv.StringArith

def unpackReg (i : Fin 11) : Fin 70 := i.castAdd 59

@[simp] theorem unpackReg_inj (i j : Fin 11) :
    unpackReg i = unpackReg j ↔ i = j := by
  constructor
  · intro h; apply Fin.ext; exact congrArg (fun z : Fin 70 ↦ z.val) h
  · rintro rfl; rfl

@[simp] theorem unpackReg_ne_extra (i : Fin 11) (j : Fin 59) :
    unpackReg i ≠ j.natAdd 11 := by
  intro h
  have := congrArg Fin.val h
  simp [unpackReg] at this
  omega

@[simp] theorem extra_ne_unpackReg (i : Fin 11) (j : Fin 59) :
    j.natAdd 11 ≠ unpackReg i := (unpackReg_ne_extra i j).symm

private theorem unpack_natAdd_subNat (i : Fin 70) (h : 5 ≤ i.val) :
    (Fin.subNat 5 i h : Fin 65).natAdd 5 = i := by
  apply Fin.ext
  simp only [Fin.val_natAdd, Fin.subNat]
  omega

private theorem unpack_subNat_natAdd (i : Fin 59) (h : 11 ≤ (i.natAdd 11).val) :
    (Fin.subNat 11 (i.natAdd 11) h : Fin 59) = i := by
  apply Fin.ext
  simp only [Fin.subNat, Fin.val_natAdd]
  omega

/-- Process one payload bit, adding its positional value and doubling the weight. -/
def unpackActive : BinaryRoutine 70 :=
  seq (inputReadBit 65)
    (seq (branchZero (unpackReg 2) identity (add (unpackReg 6) (unpackReg 5)
      (unpackReg 4)))
      (seq (binaryCopy (unpackReg 6) (unpackReg 9) (unpackReg 4))
        (seq (add (unpackReg 9) (unpackReg 6) (unpackReg 4))
          (seq (clear (unpackReg 9)) (clear (unpackReg 2))))))

/-- Once only the sentinel remains, subsequent passes leave the decoded value fixed. -/
def unpackBody : BinaryRoutine 70 :=
  seq (binaryCopy (unpackReg 0) (unpackReg 10) (unpackReg 4))
    (seq (binaryPred (unpackReg 10))
      (seq (branchZero (unpackReg 10) identity (unpackActive))
        (clear (unpackReg 10))))

def unpackLoop : BinaryRoutine 70 :=
  binaryFor (unpackBody) (unpackReg 7) (unpackReg 8)

theorem unpackActive_sound : (unpackActive).Sound :=
  (inputReadBit_sound _).seq
    ((identity_sound.branchZero (add_sound _ _ _) _).seq
      ((binaryCopy_sound _ _ _).seq ((add_sound _ _ _).seq
        ((clear_sound _).seq (clear_sound _)))))

theorem unpackBody_sound : (unpackBody).Sound :=
  (binaryCopy_sound _ _ _).seq ((binaryPred_sound _).seq
    ((identity_sound.branchZero (unpackActive_sound) _).seq (clear_sound _)))

theorem unpackLoop_sound : (unpackLoop).Sound :=
  (unpackBody_sound).binaryFor _ _

def unpackValues (source acc weight count limit : ℕ) (extra : Fin 59 → ℕ) :
    BinaryValues 70 :=
  Fin.append ![source, 0, 0, 0, 0, acc, weight, count, limit, 0, 0] extra

@[simp] theorem unpackValues_reg (s a w i N : ℕ) (extra : Fin 59 → ℕ)
    (j : Fin 11) :
    unpackValues s a w i N extra (unpackReg j) = ![s, 0, 0, 0, 0, a, w, i, N, 0, 0] j :=
  Fin.append_left _ _ _

@[simp] theorem unpackValues_extra (s a w i N : ℕ) (extra : Fin 59 → ℕ)
    (j : Fin 59) : unpackValues s a w i N extra (j.natAdd 11) = extra j :=
  Fin.append_right _ _ _

theorem unpackActive_requires (s a w i N probe : ℕ) (extra : Fin 59 → ℕ) :
    (unpackActive).requires
      (Function.update (unpackValues s a w i N extra) (unpackReg 10) probe) := by
  refine ⟨inputReadBit_requires _, ?_⟩
  rw [inputReadBit_effect]
  by_cases hb : s % 2 = 0 <;>
    simp [unpackActive, seq, branchZero, binaryCopy, add, clear, identity, hb,
      inputReg, unpackReg, unpackValues, Fin.append, Fin.addCases, emitBits, two_mul]

theorem unpackActive_effect (s a w i N probe : ℕ) (extra : Fin 59 → ℕ) :
    (unpackActive).effect
      (Function.update (unpackValues s a w i N extra) (unpackReg 10) probe) =
      Function.update (unpackValues (s / 2) (a + s % 2 * w) (2 * w) i N extra)
        (unpackReg 10) probe := by
  have hbnd := Nat.mod_lt s (by decide : 0 < 2)
  by_cases hb : s % 2 = 0
  · unfold unpackActive
    simp only [seq, inputReadBit_effect]
    funext j
    refine Fin.addCases (m := 11) (n := 59) (fun j ↦ ?_) (fun j ↦ ?_) j
    · fin_cases j <;> simp [branchZero, binaryCopy, add, clear, identity, hb, inputReg, unpackReg, unpackValues, Fin.append, Fin.addCases, emitBits, two_mul]
    · have h2 : j.natAdd 11 ≠ (2 : Fin 70) := by
        intro h
        have hh := congrArg (fun z : Fin 70 ↦ z.val) h
        norm_num [Fin.val_natAdd] at hh
        omega
      have h5 : j.natAdd 11 ≠ (5 : Fin 70) := by
        intro h
        have hh := congrArg (fun z : Fin 70 ↦ z.val) h
        norm_num [Fin.val_natAdd] at hh
        omega
      have h6 : j.natAdd 11 ≠ (6 : Fin 70) := by
        intro h
        have hh := congrArg (fun z : Fin 70 ↦ z.val) h
        norm_num [Fin.val_natAdd] at hh
        omega
      have h9 : j.natAdd 11 ≠ (9 : Fin 70) := by
        intro h
        have hh := congrArg (fun z : Fin 70 ↦ z.val) h
        norm_num [Fin.val_natAdd] at hh
        omega
      have h10 : j.natAdd 11 ≠ (10 : Fin 70) := by
        intro h
        have hh := congrArg (fun z : Fin 70 ↦ z.val) h
        norm_num [Fin.val_natAdd] at hh
        omega
      simp [branchZero, binaryCopy, add, clear, identity, hb, inputReg, unpackReg,
        unpackValues, Fin.append, Fin.addCases, emitBits, two_mul, h2, h5, h6, h9, h10]
      simp only [dite_eq_right (by omega : ¬11 + j.val < 5), unpack_natAdd_subNat,
        Function.update_of_ne h10, Fin.addCases_right, unpack_subNat_natAdd]
  · have hb1 : s % 2 = 1 := by omega
    unfold unpackActive
    simp only [seq, inputReadBit_effect]
    funext j
    refine Fin.addCases (m := 11) (n := 59) (fun j ↦ ?_) (fun j ↦ ?_) j
    · fin_cases j <;> simp [branchZero, binaryCopy, add, clear, identity, hb1, inputReg, unpackReg, unpackValues, Fin.append, Fin.addCases, emitBits, two_mul]
    · have h2 : j.natAdd 11 ≠ (2 : Fin 70) := by
        intro h
        have hh := congrArg (fun z : Fin 70 ↦ z.val) h
        norm_num [Fin.val_natAdd] at hh
        omega
      have h5 : j.natAdd 11 ≠ (5 : Fin 70) := by
        intro h
        have hh := congrArg (fun z : Fin 70 ↦ z.val) h
        norm_num [Fin.val_natAdd] at hh
        omega
      have h6 : j.natAdd 11 ≠ (6 : Fin 70) := by
        intro h
        have hh := congrArg (fun z : Fin 70 ↦ z.val) h
        norm_num [Fin.val_natAdd] at hh
        omega
      have h9 : j.natAdd 11 ≠ (9 : Fin 70) := by
        intro h
        have hh := congrArg (fun z : Fin 70 ↦ z.val) h
        norm_num [Fin.val_natAdd] at hh
        omega
      have h10 : j.natAdd 11 ≠ (10 : Fin 70) := by
        intro h
        have hh := congrArg (fun z : Fin 70 ↦ z.val) h
        norm_num [Fin.val_natAdd] at hh
        omega
      simp [branchZero, binaryCopy, add, clear, identity, hb1, inputReg, unpackReg,
        unpackValues, Fin.append, Fin.addCases, emitBits, two_mul, h2, h5, h6, h9, h10]
      simp only [dite_eq_right (by omega : ¬11 + j.val < 5), unpack_natAdd_subNat,
        Function.update_of_ne h10, Fin.addCases_right, unpack_subNat_natAdd]

theorem unpackBody_requires (s a w i N : ℕ) (extra : Fin 59 → ℕ) (hs : 0 < s) :
    unpackBody.requires (unpackValues s a w i N extra) := by
  by_cases h : s = 1
  · subst s
    simp [unpackBody, seq, binaryCopy, binaryPred, branchZero, clear, identity, emitBits]
  · have hne : s - 1 ≠ 0 := by omega
    simpa [unpackBody, seq, binaryCopy, binaryPred, branchZero, clear, hne, hs] using
      unpackActive_requires s a w i N (s - 1) extra

theorem unpackBody_effect (s a w i N : ℕ) (extra : Fin 59 → ℕ) (hs : 0 < s) :
    unpackBody.effect (unpackValues s a w i N extra) =
      if s = 1 then unpackValues s a w i N extra
      else unpackValues (s / 2) (a + s % 2 * w) (2 * w) i N extra := by
  have hz (source acc weight : ℕ) :
      Function.update (unpackValues source acc weight i N extra) (unpackReg 10) 0 =
        unpackValues source acc weight i N extra :=
    Function.update_eq_self _ _
  by_cases h : s = 1
  · subst s
    simpa [unpackBody, seq, binaryCopy, binaryPred, branchZero, identity, emitBits, clear] using
      hz 1 a w
  · have hne : s - 1 ≠ 0 := by omega
    simpa [unpackBody, seq, binaryCopy, binaryPred, branchZero, hne, h,
      unpackActive_effect, clear] using hz (s / 2) (a + s % 2 * w) (2 * w)

theorem unpackValues_update_counter (s a w i N j : ℕ) (extra : Fin 59 → ℕ) :
    Function.update (unpackValues s a w i N extra) (unpackReg 7) j =
      unpackValues s a w j N extra := by
  funext z
  refine Fin.addCases (m := 11) (n := 59) (fun z ↦ ?_) (fun z ↦ ?_) z
  · fin_cases z <;> simp [unpackReg, unpackValues, Fin.append, Fin.addCases]
  · simp

def unpackTraceValues (x : List Bool) (i : ℕ) (extra : Fin 59 → ℕ) : BinaryValues 70 :=
  unpackValues (packedInput (x.drop i)) (decNat (x.take i)) (2 ^ min i x.length)
    i (packedInput x) extra

theorem unpackTraceValues_step (x : List Bool) (i : ℕ) (extra : Fin 59 → ℕ) :
    binaryForStep unpackBody (unpackReg 7) (unpackTraceValues x i extra) =
      unpackTraceValues x (i + 1) extra := by
  unfold unpackTraceValues binaryForStep
  rw [unpackBody_effect _ _ _ _ _ _ (packedInput_pos _)]
  by_cases hi : i < x.length
  · have hd := List.drop_eq_getElem_cons hi
    have hs : packedInput (x.drop i) ≠ 1 := by
      rw [hd, packedInput_cons]
      have := packedInput_pos (x.drop (i + 1))
      split <;> omega
    rw [ite_eq_right hs, unpackValues_reg, unpackValues_update_counter]
    rw [hd, packedInput_div_two, packedInput_mod_two]
    have hacc := decNat_take_add_one_eq x i
    rw [List.getD_eq_getElem x false hi] at hacc
    have hm : min i x.length = i := Nat.min_eq_left hi.le
    have hm' : min (i + 1) x.length = i + 1 := Nat.min_eq_left hi
    simp only [hm, hm', pow_succ]
    congr 1
    · cases h : x[i] <;> simp_all [Bool.toNat, Nat.mul_comm]
    · omega
  · have hlen : x.length ≤ i := by omega
    simp only [List.drop_eq_nil_of_le hlen, packedInput_nil, ite_eq_left,
      unpackValues_reg, unpackValues_update_counter,
      List.drop_eq_nil_of_le (show x.length ≤ i + 1 by omega),
      List.take_of_length_le hlen, List.take_of_length_le (show x.length ≤ i + 1 by omega),
      Nat.min_eq_right hlen, Nat.min_eq_right (show x.length ≤ i + 1 by omega)]
    rfl

theorem unpackLoop_values (x : List Bool) (i : ℕ) (extra : Fin 59 → ℕ) :
    binaryForValues unpackBody (unpackReg 7) (unpackTraceValues x 0 extra) i =
      unpackTraceValues x i extra := by
  induction i with
  | zero => rfl
  | succ i ih => rw [binaryForValues, ih, unpackTraceValues_step]

theorem unpackBody_preserves (s a w i N : ℕ) (extra : Fin 59 → ℕ) (hs : 0 < s) :
    (unpackBody.effect (unpackValues s a w i N extra)) (unpackReg 7) = i ∧
      (unpackBody.effect (unpackValues s a w i N extra)) (unpackReg 8) = N := by
  rw [unpackBody_effect _ _ _ _ _ _ hs]
  split_ifs <;> simp

theorem unpackLoop_requires (x : List Bool) (extra : Fin 59 → ℕ) :
    unpackLoop.requires (unpackTraceValues x 0 extra) := by
  refine ⟨by simp, by simp [unpackTraceValues], ?_⟩
  intro i hi
  rw [unpackLoop_values]
  exact ⟨unpackBody_requires _ _ _ _ _ _ (packedInput_pos _),
    (unpackBody_preserves _ _ _ _ _ _ (packedInput_pos _)).1,
    (unpackBody_preserves _ _ _ _ _ _ (packedInput_pos _)).2⟩

theorem length_le_packedInput (x : List Bool) : x.length ≤ packedInput x := by
  induction x with
  | nil => simp
  | cons b x ih =>
      rw [List.length_cons, packedInput_cons]
      have := packedInput_pos x
      split <;> omega

theorem unpackLoop_effect (x : List Bool) (extra : Fin 59 → ℕ) :
    unpackLoop.effect (unpackTraceValues x 0 extra) =
      unpackValues 1 (decNat x) (2 ^ x.length) (packedInput x) (packedInput x) extra := by
  change binaryForValues unpackBody (unpackReg 7) _
    (binaryForCount (unpackReg 7) (unpackReg 8) (unpackTraceValues x 0 extra)) = _
  have hc : binaryForCount (unpackReg 7) (unpackReg 8) (unpackTraceValues x 0 extra) =
      packedInput x := by simp [binaryForCount, unpackTraceValues]
  rw [hc, unpackLoop_values]
  simp [unpackTraceValues, List.drop_eq_nil_of_le (length_le_packedInput x),
    List.take_of_length_le (length_le_packedInput x), Nat.min_eq_right (length_le_packedInput x)]

/-- Reset the private workspace and preserve every caller-owned register. -/
def unpackInit : BinaryRoutine 70 :=
  seq (clearRegisters ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10].map unpackReg))
    (seq (BinaryRoutine.set (unpackReg 6) 1)
      (binaryCopy (unpackReg 0) (unpackReg 8) (unpackReg 4)))

theorem unpackInit_sound : unpackInit.Sound :=
  (clearRegisters_sound _).seq ((set_sound _ _).seq (binaryCopy_sound _ _ _))

theorem unpackInit_requires (v : BinaryValues 70) : unpackInit.requires v := by
  refine ⟨clearRegisters_requires _ _, ?_⟩
  simp [seq, BinaryRoutine.set, clear, addConst, binaryCopy, clearRegisters_effect]

theorem unpackInit_effect (v : BinaryValues 70) :
    unpackInit.effect v = unpackValues (v (unpackReg 0)) 0 1 0 (v (unpackReg 0))
      (fun j ↦ v (j.natAdd 11)) := by
  unfold unpackInit
  simp only [seq]
  funext j
  refine Fin.addCases (m := 11) (n := 59) (fun j ↦ ?_) (fun j ↦ ?_) j
  · fin_cases j <;> simp [BinaryRoutine.set, clear, addConst, binaryCopy, seq,
      clearRegisters_effect, unpackReg, unpackValues, Fin.append, Fin.addCases]
  · have h4 : j.natAdd 11 ≠ unpackReg 4 := extra_ne_unpackReg _ _
    have h6 : j.natAdd 11 ≠ unpackReg 6 := extra_ne_unpackReg _ _
    have h8 : j.natAdd 11 ≠ unpackReg 8 := extra_ne_unpackReg _ _
    simp [BinaryRoutine.set, clear, addConst, binaryCopy, seq, clearRegisters_effect,
      h4, h6, h8]

/-- Remove the sentinel from a packed binary string, resetting all private temporaries. -/
def unpackInput : BinaryRoutine 70 := seq unpackInit unpackLoop

theorem unpackInput_sound : unpackInput.Sound := unpackInit_sound.seq unpackLoop_sound

theorem unpackInput_requires (v : BinaryValues 70) (x : List Bool)
    (hx : v (unpackReg 0) = packedInput x) : unpackInput.requires v := by
  refine ⟨unpackInit_requires v, ?_⟩
  rw [unpackInit_effect, hx]
  simpa [unpackTraceValues] using unpackLoop_requires x (fun j ↦ v (j.natAdd 11))

theorem unpackInput_effect (v : BinaryValues 70) (x : List Bool)
    (hx : v (unpackReg 0) = packedInput x) :
    unpackInput.effect v = unpackValues 1 (decNat x) (2 ^ x.length)
      (packedInput x) (packedInput x) (fun j ↦ v (j.natAdd 11)) := by
  simp only [unpackInput, seq, unpackInit_effect, hx]
  simpa [unpackTraceValues] using unpackLoop_effect x (fun j ↦ v (j.natAdd 11))

end SparseIrred.UpperBounds.Machine
