import SparseIrred.UpperBounds.Section4.BerkowitzProgramFactors

/-!
# A complete arithmetic stack program for the Berkowitz determinant

The outer product, each factor's two sums, and all trailing-matrix powers share
one address machine. The only scalar leaves are entries of the original matrix
and ring constants; no determinant, matrix power, or factor entry is an oracle.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace SparseIrred.UpperBounds.Section4

open Matrix

variable {R : Type*} [CommRing R] {n : ℕ}

theorem splitDepth_le_log2_of_le {e N : ℕ} (h : e ≤ N) :
    splitDepth e ≤ N.log2 + 2 := by
  simpa [Nat.add_assoc] using splitDepth_le_of_le_pow e (N.log2 + 1)
    (h.trans (Nat.lt_log2_self (n := N)).le)

theorem intervalProduct_const {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R) (start len : ℕ) :
    intervalProduct (fun _ ↦ M) start len = M ^ len := by
  induction len generalizing start with
  | zero => simp [intervalProduct]
  | succ len ih => simp [intervalProduct, ih, pow_succ']

abbrev BerkowitzPowerAddress (n : ℕ) := Σ s : Fin n, ProductAddress (n - s.val - 1)

def berkowitzPowerProgram (A : Matrix (Fin n) (Fin n) R) :
    EntryProgram (BerkowitzPowerAddress n) R :=
  EntryProgram.family (fun s : Fin n ↦ productProgram (fun _ ↦ berkowitzStrictTail A s))

def berkowitzPowerRequest : BerkowitzFactorAddress n → Option (BerkowitzPowerAddress n)
  | .power s e k l => some ⟨s, .entry 0 e.val k l⟩
  | _ => none

def berkowitzPowerBound (n : ℕ) : ℕ := ((n + 1).log2 + 3) * ((n + 1).log2 + 4) + 1

theorem berkowitzPowerRequest_rank (A : Matrix (Fin n) (Fin n) R)
    (a : BerkowitzFactorAddress n) (b : BerkowitzPowerAddress n)
    (h : berkowitzPowerRequest a = some b) :
    (berkowitzPowerProgram A).rank b ≤ berkowitzPowerBound n := by
  cases a <;> simp only [berkowitzPowerRequest] at h <;> try cases h
  rename_i s e k l
  change (splitDepth e.val + 1) * (splitDepth (n - s.val - 1) + 2) + 1 ≤ _
  have he := splitDepth_le_log2_of_le (show e.val ≤ n + 1 by omega)
  have hn := splitDepth_le_log2_of_le (show n - s.val - 1 ≤ n + 1 by omega)
  unfold berkowitzPowerBound
  nlinarith

theorem berkowitzPowerRequest_value (A : Matrix (Fin n) (Fin n) R)
    (a : BerkowitzFactorAddress n) (b : BerkowitzPowerAddress n) (v : R)
    (hv : (berkowitzFactorProgram A).instruction a = .value v)
    (h : berkowitzPowerRequest a = some b) : (berkowitzPowerProgram A).value b = v := by
  cases a <;> simp only [berkowitzPowerRequest] at h <;> try cases h
  rename_i s e k l
  change EntryInstruction.value (powerEntry (berkowitzStrictTail A s) e.val k l) = _ at hv
  cases hv
  simp [berkowitzPowerProgram, EntryProgram.family_value, productProgram_value,
    intervalProduct_const, powerEntry_eq]

abbrev BerkowitzExpandedFactorAddress (n : ℕ) :=
  SubstituteAddress (BerkowitzFactorAddress n) (BerkowitzPowerAddress n)

/-- The factor program after its power leaves have become genuine subprogram calls. -/
def berkowitzExpandedFactorProgram (A : Matrix (Fin n) (Fin n) R) :
    EntryProgram (BerkowitzExpandedFactorAddress n) R :=
  (berkowitzFactorProgram A).substitute (berkowitzPowerProgram A) berkowitzPowerRequest
    (berkowitzPowerBound n) (berkowitzPowerRequest_rank A)

theorem berkowitzExpandedFactorProgram_value (A : Matrix (Fin n) (Fin n) R)
    (a : BerkowitzFactorAddress n) :
    (berkowitzExpandedFactorProgram A).value (.outer a) = berkowitzFactorValue A a := by
  rw [berkowitzExpandedFactorProgram, EntryProgram.substitute_value _ _ _ _ _
    (berkowitzPowerRequest_value A)]
  exact berkowitzFactorProgram_value A a

def berkowitzFactorBound (n : ℕ) : ℕ :=
  2 * (n + 1).log2 + 12 + berkowitzPowerBound n

def berkowitzFactorRequest : ProductAddress (n + 1) →
    Option (BerkowitzExpandedFactorAddress n)
  | .entry start len i j => if len = 1 then
      if h : start < n then some (.outer (.entry ⟨start, h⟩ i j)) else none
    else none
  | _ => none

theorem berkowitzFactorRequest_rank (A : Matrix (Fin n) (Fin n) R)
    (a : ProductAddress (n + 1)) (b : BerkowitzExpandedFactorAddress n)
    (h : berkowitzFactorRequest a = some b) :
    (berkowitzExpandedFactorProgram A).rank b ≤ berkowitzFactorBound n := by
  cases a with
  | zero | sum _ _ _ _ _ _ => simp [berkowitzFactorRequest] at h
  | entry start len i j =>
    simp only [berkowitzFactorRequest] at h
    split_ifs at h <;> try cases h
    change 2 * splitDepth (n - start - 1) + 6 + berkowitzPowerBound n + 2 ≤ _
    have hn := splitDepth_le_log2_of_le (show n - start - 1 ≤ n + 1 by omega)
    unfold berkowitzFactorBound
    omega

theorem berkowitzFactorRequest_value (A : Matrix (Fin n) (Fin n) R)
    (a : ProductAddress (n + 1)) (b : BerkowitzExpandedFactorAddress n) (v : R)
    (hv : (productProgram (indexedBerkowitzFactor (n + 1) A)).instruction a = .value v)
    (h : berkowitzFactorRequest a = some b) :
    (berkowitzExpandedFactorProgram A).value b = v := by
  cases a with
  | zero | sum _ _ _ _ _ _ => simp [berkowitzFactorRequest] at h
  | entry start len i j =>
    simp only [berkowitzFactorRequest] at h
    split_ifs at h with hlen hs <;> try cases h
    subst len
    simp only [productProgram, productInstruction, Nat.one_ne_zero, ↓reduceIte] at hv
    cases hv
    exact berkowitzExpandedFactorProgram_value A (.entry ⟨start, hs⟩ i j)

abbrev BerkowitzCoreAddress (n : ℕ) :=
  SubstituteAddress (ProductAddress (n + 1)) (BerkowitzExpandedFactorAddress n)

/-- All levels of the determinant recursion, before the constant sign correction. -/
def berkowitzCoreProgram (A : Matrix (Fin n) (Fin n) R) :
    EntryProgram (BerkowitzCoreAddress n) R :=
  (productProgram (indexedBerkowitzFactor (n + 1) A)).substitute
    (berkowitzExpandedFactorProgram A) berkowitzFactorRequest (berkowitzFactorBound n)
    (berkowitzFactorRequest_rank A)

def berkowitzCoreInitial (n : ℕ) : BerkowitzCoreAddress n :=
  .outer (.entry 0 n (Fin.last n) 0)

theorem berkowitzCoreProgram_value (A : Matrix (Fin n) (Fin n) R) :
    (-1) ^ n * (berkowitzCoreProgram A).value (berkowitzCoreInitial n) = A.det := by
  rw [berkowitzCoreProgram, berkowitzCoreInitial,
    EntryProgram.substitute_value _ _ _ _ _ (berkowitzFactorRequest_value A)]
  change (-1) ^ n * (productProgram (indexedBerkowitzFactor (n + 1) A)).value
    (.entry 0 n (Fin.last n) 0) = _
  rw [productProgram_value, ← productEntry_eq]
  exact indexedBerkowitzDeterminant_eq_det A

inductive BerkowitzAddress (n : ℕ) where
  | initial
  | sign
  | core (a : BerkowitzCoreAddress n)

def berkowitzInstruction (A : Matrix (Fin n) (Fin n) R) :
    BerkowitzAddress n → EntryInstruction (BerkowitzAddress n) R
  | .initial => .branch .mul .sign (.core (berkowitzCoreInitial n))
  | .sign => .value ((-1) ^ n)
  | .core a => match (berkowitzCoreProgram A).instruction a with
    | .value v => .value v
    | .branch op l r => .branch op (.core l) (.core r)

def berkowitzRank (A : Matrix (Fin n) (Fin n) R) : BerkowitzAddress n → ℕ
  | .initial => (berkowitzCoreProgram A).rank (berkowitzCoreInitial n) + 2
  | .sign => 0
  | .core a => (berkowitzCoreProgram A).rank a + 1

theorem berkowitzInstruction_descend (A : Matrix (Fin n) (Fin n) R)
    (a : BerkowitzAddress n) (op : BinaryOp) (l r : BerkowitzAddress n)
    (h : berkowitzInstruction A a = .branch op l r) :
    berkowitzRank A l < berkowitzRank A a ∧ berkowitzRank A r < berkowitzRank A a := by
  cases a with
  | sign => simp [berkowitzInstruction] at h
  | initial => cases h; simp [berkowitzRank]
  | core a =>
    cases he : (berkowitzCoreProgram A).instruction a with
    | value v => simp [berkowitzInstruction, he] at h
    | branch op' l' r' =>
      simp only [berkowitzInstruction, he, EntryInstruction.branch.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have hd := (berkowitzCoreProgram A).descend a op' l' r' he
      simp only [berkowitzRank]
      omega

/-- The complete determinant address machine, including its final sign correction. -/
def berkowitzProgram (A : Matrix (Fin n) (Fin n) R) : EntryProgram (BerkowitzAddress n) R :=
  ⟨berkowitzInstruction A, berkowitzRank A, berkowitzInstruction_descend A⟩

def berkowitzProgramMeaning (A : Matrix (Fin n) (Fin n) R) : BerkowitzAddress n → R
  | .initial => A.det
  | .sign => (-1) ^ n
  | .core a => (berkowitzCoreProgram A).value a

theorem berkowitzProgram_value (A : Matrix (Fin n) (Fin n) R) :
    (berkowitzProgram A).value .initial = A.det := by
  apply EntryProgram.value_eq_of_equations (f := berkowitzProgramMeaning A)
  intro a
  cases a with
  | sign => rfl
  | initial => exact (berkowitzCoreProgram_value A).symm
  | core a =>
    change (berkowitzCoreProgram A).value a = _
    rw [EntryProgram.value]
    cases he : (berkowitzCoreProgram A).instruction a <;>
      simp [berkowitzProgram, berkowitzInstruction, berkowitzProgramMeaning, he]

/-- The explicit instruction machine halts and returns the determinant. -/
theorem berkowitzProgram_correct (A : Matrix (Fin n) (Fin n) R) :
    ∃ t, (berkowitzProgram A).step^[t] (.eval .initial []) = .ret A.det [] := by
  simpa only [berkowitzProgram_value] using (berkowitzProgram A).correct .initial

/-- A binary-length bound for the entire nesting of products, sums, and powers. -/
def berkowitzStackBound (n : ℕ) : ℕ := 2 * ((n + 1).log2 + 4) ^ 2 + 2 * (n + 1).log2 + 20

theorem berkowitzProgram_rank_initial (A : Matrix (Fin n) (Fin n) R) :
    (berkowitzProgram A).rank .initial ≤ berkowitzStackBound n := by
  change (splitDepth n + 1) * (splitDepth (n + 1) + 2) + 1 +
    berkowitzFactorBound n + 2 + 2 ≤ _
  have hn := splitDepth_le_log2_of_le (show n ≤ n + 1 by omega)
  have hn' := splitDepth_le_log (n + 1)
  unfold berkowitzStackBound berkowitzFactorBound berkowitzPowerBound
  nlinarith

/-- The bound covers every intermediate stack, not just completed recursive calls. -/
theorem berkowitzProgram_stack_bound (A : Matrix (Fin n) (Fin n) R) (t : ℕ) :
    ((berkowitzProgram A).step^[t] (.eval .initial [])).stack.length ≤ berkowitzStackBound n :=
  ((berkowitzProgram A).stack_length_iterate_le .initial t).trans
    (berkowitzProgram_rank_initial A)

end SparseIrred.UpperBounds.Section4
