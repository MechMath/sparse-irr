import SparseIrred.UpperBounds.Section4.EntryMachineDecision

/-! # Balanced Boolean combinations of address programs -/

namespace SparseIrred.UpperBounds.Section4

inductive BinaryAddress (A B : Type*) where
  | root
  | left (address : A)
  | right (address : B)

section Binary
variable {A B R : Type*} [Add R] [Mul R]

/-- Call two programs sequentially and combine their returned values. -/
def binaryProgram (op : BinaryOp) (P : EntryProgram A R) (Q : EntryProgram B R)
    (a : A) (b : B) : EntryProgram (BinaryAddress A B) R where
  instruction c := match c with
    | .root => .branch op (.left a) (.right b)
    | .left i => match P.instruction i with
      | .value v => .value v
      | .branch op l r => .branch op (.left l) (.left r)
    | .right i => match Q.instruction i with
      | .value v => .value v
      | .branch op l r => .branch op (.right l) (.right r)
  rank c := match c with
    | .root => max (P.rank a) (Q.rank b) + 2
    | .left i => P.rank i + 1
    | .right i => Q.rank i + 1
  descend c op l r h := by
    cases c with
    | root => cases h; dsimp only; omega
    | left i =>
      dsimp only at h ⊢
      cases he : P.instruction i with
      | value v => simp only [he] at h; cases h
      | branch op l r =>
        simp only [he] at h
        cases h
        have hd := P.descend _ _ _ _ he
        dsimp only
        omega
    | right i =>
      dsimp only at h ⊢
      cases he : Q.instruction i with
      | value v => simp only [he] at h; cases h
      | branch op l r =>
        simp only [he] at h
        cases h
        have hd := Q.descend _ _ _ _ he
        dsimp only
        omega

private def binaryMeaning (op : BinaryOp) (P : EntryProgram A R) (Q : EntryProgram B R)
    (a : A) (b : B) : BinaryAddress A B → R
  | .root => op.apply (P.value a) (Q.value b)
  | .left i => P.value i
  | .right i => Q.value i

theorem binaryProgram_value (op : BinaryOp) (P : EntryProgram A R) (Q : EntryProgram B R)
    (a : A) (b : B) :
    (binaryProgram op P Q a b).value .root = op.apply (P.value a) (Q.value b) := by
  apply (binaryProgram op P Q a b).value_eq_of_equations (binaryMeaning op P Q a b)
  intro c
  cases c with
  | root => rfl
  | left i =>
    cases he : P.instruction i <;> simp only [binaryProgram, he, binaryMeaning] <;>
      rw [EntryProgram.value, he]
  | right i =>
    cases he : Q.instruction i <;> simp only [binaryProgram, he, binaryMeaning] <;>
      rw [EntryProgram.value, he]

@[simp] theorem binaryProgram_rank (op : BinaryOp) (P : EntryProgram A R) (Q : EntryProgram B R)
    (a : A) (b : B) :
    (binaryProgram op P Q a b).rank .root = max (P.rank a) (Q.rank b) + 2 := rfl
end Binary

inductive OrAddress {m : ℕ} (A : Fin m → Type*) where
  | range (lo count : ℕ)
  | call (i : Fin m) (address : A i)
  | zero

variable {K : Type*} [Add K] [Mul K] [Zero K] [DecidableEq K]
    {m : ℕ} {A : Fin m → Type*}

/-- A balanced fold over Boolean-valued subprograms; only one subprogram is active at a time. -/
def orProgram (P : ∀ i, EntryProgram (A i) (DecisionScalar K)) (initial : ∀ i, A i)
    (bound : ℕ) (hbound : ∀ i, (P i).rank (initial i) ≤ bound) :
    EntryProgram (OrAddress A) (DecisionScalar K) where
  instruction a := match a with
    | .zero => .value (.flag false)
    | .call i a => match (P i).instruction a with
      | .value v => .value v
      | .branch op l r => .branch op (.call i l) (.call i r)
    | .range lo count =>
      if count = 0 then .value (.flag false)
      else if count = 1 then
        if h : lo < m then .branch .add (.call ⟨lo, h⟩ (initial ⟨lo, h⟩)) .zero
        else .value (.flag false)
      else .branch .add (.range lo (count / 2)) (.range (lo + count / 2) (count - count / 2))
  rank a := match a with
    | .zero => 0
    | .call i a => (P i).rank a + 1
    | .range _ count => bound + splitDepth count + 2
  descend a op l r h := by
    cases a with
    | zero => cases h
    | call i a =>
      dsimp only at h ⊢
      cases he : (P i).instruction a with
      | value v => simp only [he] at h; cases h
      | branch op l r =>
        simp only [he] at h
        cases h
        have hd := (P i).descend _ _ _ _ he
        dsimp only
        omega
    | range lo count =>
      dsimp only at h ⊢
      split_ifs at h with h0 h1 hlo <;> cases h
      · dsimp only
        have hb := hbound ⟨lo, hlo⟩
        omega
      · dsimp only
        have hh : splitDepth count =
            1 + max (splitDepth (count / 2)) (splitDepth (count - count / 2)) := by
          rw [splitDepth, if_neg (by omega)]
        omega

private def orMeaning (P : ∀ i, EntryProgram (A i) (DecisionScalar K))
    (answer : Fin m → Bool) : OrAddress A → DecisionScalar K
  | .zero => .flag false
  | .call i a => (P i).value a
  | .range lo count => .flag ((List.range count).any
      (fun k ↦ if h : lo + k < m then answer ⟨lo + k, h⟩ else false))

private theorem any_range_split (f : ℕ → Bool) (lo count : ℕ) :
    (List.range count).any (fun k ↦ f (lo + k)) =
      ((List.range (count / 2)).any (fun k ↦ f (lo + k)) ||
        (List.range (count - count / 2)).any (fun k ↦ f (lo + count / 2 + k))) := by
  conv_lhs => rw [← Nat.add_sub_of_le (Nat.div_le_self count 2)]
  rw [List.range_add, List.any_append, List.any_map]
  simp only [Function.comp_def, Nat.add_assoc]

theorem orProgram_value (P : ∀ i, EntryProgram (A i) (DecisionScalar K))
    (initial : ∀ i, A i) (bound : ℕ) (hbound : ∀ i, (P i).rank (initial i) ≤ bound)
    (answer : Fin m → Bool) (hanswer : ∀ i, (P i).value (initial i) = .flag (answer i))
    (lo count : ℕ) :
    (orProgram P initial bound hbound).value (.range lo count) =
      .flag ((List.range count).any (fun k ↦ if h : lo + k < m then answer ⟨lo + k, h⟩
        else false)) := by
  apply (orProgram P initial bound hbound).value_eq_of_equations (orMeaning P answer)
  intro a
  cases a with
  | zero => rfl
  | call i a =>
    cases he : (P i).instruction a <;> simp only [orProgram, he, orMeaning] <;>
      rw [EntryProgram.value, he]
  | range lo count =>
    simp only [orProgram]
    split_ifs with h0 h1 hlo
    · subst count; simp [orMeaning]
    · subst count; simp [orMeaning, hlo, hanswer, BinaryOp.apply]
    · subst count; simp [orMeaning, hlo]
    · simp only [orMeaning, BinaryOp.apply, DecisionScalar.flag_add]
      congr 1
      exact any_range_split (fun k ↦ if h : k < m then answer ⟨k, h⟩ else false) lo count

@[simp] theorem orProgram_rank (P : ∀ i, EntryProgram (A i) (DecisionScalar K))
    (initial : ∀ i, A i) (bound : ℕ) (hbound : ∀ i, (P i).rank (initial i) ≤ bound)
    (lo count : ℕ) :
    (orProgram P initial bound hbound).rank (.range lo count) = bound + splitDepth count + 2 := rfl

/-- The full fold accepts exactly when one of the individual tests accepts. -/
theorem orProgram_true_iff (P : ∀ i, EntryProgram (A i) (DecisionScalar K))
    (initial : ∀ i, A i) (bound : ℕ) (hbound : ∀ i, (P i).rank (initial i) ≤ bound)
    (answer : Fin m → Bool) (hanswer : ∀ i, (P i).value (initial i) = .flag (answer i)) :
    (orProgram P initial bound hbound).value (.range 0 m) = .flag true ↔
      ∃ i, answer i = true := by
  rw [orProgram_value P initial bound hbound answer hanswer]
  simp only [DecisionScalar.flag.injEq, List.any_eq_true, List.mem_range, Nat.zero_add]
  constructor
  · rintro ⟨i, hi, he⟩
    exact ⟨⟨i, hi⟩, by simpa [hi] using he⟩
  · rintro ⟨i, hi⟩
    exact ⟨i.val, i.isLt, by simpa [i.isLt] using hi⟩

end SparseIrred.UpperBounds.Section4
