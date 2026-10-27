import SparseIrred.UpperBounds.Section4.BerkowitzProgramCompose
import SparseIrred.UpperBounds.Section4.BerkowitzIndexed
import SparseIrred.UpperBounds.Section4.EntryMachineProduct

/-!
# An address program for a single Berkowitz factor

The two finite sums are evaluated by balanced addition. Only their endpoints,
two indices, and scalar continuations are stored. The power leaves are replaced
by the power program in the subsequent composition.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace SparseIrred.UpperBounds.Section4

open Matrix

inductive BerkowitzFactorAddress (n : ℕ) where
  | entry (s : Fin n) (i j : Fin (n + 1))
  | rows (s : Fin n) (e : Fin (n + 1)) (lo count : ℕ)
  | cols (s : Fin n) (e : Fin (n + 1)) (k : Fin (n - s.val - 1)) (lo count : ℕ)
  | term (s : Fin n) (e : Fin (n + 1)) (k l : Fin (n - s.val - 1))
  | weighted (s : Fin n) (e : Fin (n + 1)) (k l : Fin (n - s.val - 1))
  | power (s : Fin n) (e : Fin (n + 1)) (k l : Fin (n - s.val - 1))
  | row (s : Fin n) (k : Fin (n - s.val - 1))
  | col (s : Fin n) (l : Fin (n - s.val - 1))
  | diag (s : Fin n)
  | negOne
  | zero

variable {R : Type*} [CommRing R] {n : ℕ}

def berkowitzStrictTail (A : Matrix (Fin n) (Fin n) R) (s : Fin n) :
    Matrix (Fin (n - s.val - 1)) (Fin (n - s.val - 1)) R :=
  A.submatrix (berkowitzTrailingIndex s.val) (berkowitzTrailingIndex s.val)

def berkowitzFactorInstruction (A : Matrix (Fin n) (Fin n) R) :
    BerkowitzFactorAddress n → EntryInstruction (BerkowitzFactorAddress n) R
  | .zero => .value 0
  | .negOne => .value (-1)
  | .diag s => .value (A s s)
  | .row s k => .value (A s (berkowitzTrailingIndex s.val k))
  | .col s l => .value (A (berkowitzTrailingIndex s.val l) s)
  | .power s e k l => .value (powerEntry (berkowitzStrictTail A s) e.val k l)
  | .weighted s e k l => .branch .mul (.power s e k l) (.col s l)
  | .term s e k l => .branch .mul (.row s k) (.weighted s e k l)
  | .cols s e k lo count =>
    if count = 0 then .value 0
    else if count = 1 then
      if h : lo < n - s.val - 1 then .branch .add (.term s e k ⟨lo, h⟩) .zero
      else .value 0
    else .branch .add (.cols s e k lo (count / 2))
      (.cols s e k (lo + count / 2) (count - count / 2))
  | .rows s e lo count =>
    if count = 0 then .value 0
    else if count = 1 then
      if h : lo < n - s.val - 1 then
        .branch .add (.cols s e ⟨lo, h⟩ 0 (n - s.val - 1)) .zero
      else .value 0
    else .branch .add (.rows s e lo (count / 2))
      (.rows s e (lo + count / 2) (count - count / 2))
  | .entry s i j =>
    if i.val < n - s.val + 1 ∧ j.val < n - s.val ∧ j.val ≤ i.val then
      if i.val - j.val = 0 then .value 1
      else if i.val - j.val = 1 then .branch .mul .negOne (.diag s)
      else .branch .mul .negOne
        (.rows s ⟨i.val - j.val - 2, by have := i.isLt; omega⟩ 0 (n - s.val - 1))
    else .value 0

def berkowitzFactorRank : BerkowitzFactorAddress n → ℕ
  | .entry s _ _ => 2 * splitDepth (n - s.val - 1) + 6
  | .rows s _ _ count => splitDepth count + splitDepth (n - s.val - 1) + 4
  | .cols _ _ _ _ count => splitDepth count + 3
  | .term _ _ _ _ => 2
  | .weighted _ _ _ _ => 1
  | _ => 0

private theorem splitDepth_halves_lt (e : ℕ) (he : 1 < e) :
    splitDepth (e / 2) < splitDepth e ∧ splitDepth (e - e / 2) < splitDepth e := by
  have h : splitDepth e = 1 + max (splitDepth (e / 2)) (splitDepth (e - e / 2)) := by
    rw [splitDepth, ite_eq_right (by omega)]
  omega

theorem berkowitzFactorInstruction_descend (A : Matrix (Fin n) (Fin n) R)
    (a : BerkowitzFactorAddress n) (op : BinaryOp) (l r : BerkowitzFactorAddress n)
    (h : berkowitzFactorInstruction A a = .branch op l r) :
    berkowitzFactorRank l < berkowitzFactorRank a ∧
      berkowitzFactorRank r < berkowitzFactorRank a := by
  cases a with
  | zero | negOne | row s k | col s l | diag s | power s e k l =>
    simp [berkowitzFactorInstruction] at h
  | weighted s e k l | term s e k l =>
    cases h
    simp [berkowitzFactorRank]
  | cols s e k lo count =>
    simp only [berkowitzFactorInstruction] at h
    split_ifs at h with hc0 hc1 hlo <;> try cases h
    · subst count
      simp only [berkowitzFactorRank]
      omega
    · have hd := splitDepth_halves_lt count (by omega)
      simp only [berkowitzFactorRank]
      omega
  | rows s e lo count =>
    simp only [berkowitzFactorInstruction] at h
    split_ifs at h with hc0 hc1 hlo <;> try cases h
    · subst count
      have h1 : splitDepth 1 = 1 := by rw [splitDepth]; norm_num
      simp only [berkowitzFactorRank, h1]
      omega
    · have hd := splitDepth_halves_lt count (by omega)
      simp only [berkowitzFactorRank]
      omega
  | entry s i j =>
    simp only [berkowitzFactorInstruction] at h
    split_ifs at h <;> try cases h
    all_goals simp only [berkowitzFactorRank]; omega

def berkowitzFactorProgram (A : Matrix (Fin n) (Fin n) R) :
    EntryProgram (BerkowitzFactorAddress n) R :=
  ⟨berkowitzFactorInstruction A, berkowitzFactorRank, berkowitzFactorInstruction_descend A⟩

def berkowitzFactorValue (A : Matrix (Fin n) (Fin n) R) : BerkowitzFactorAddress n → R
  | .entry s i j => indexedBerkowitzFactor (n + 1) A s.val i j
  | .zero => 0
  | .negOne => -1
  | .diag s => A s s
  | .row s k => A s (berkowitzTrailingIndex s.val k)
  | .col s l => A (berkowitzTrailingIndex s.val l) s
  | .power s e k l => powerEntry (berkowitzStrictTail A s) e.val k l
  | .weighted s e k l => powerEntry (berkowitzStrictTail A s) e.val k l *
      A (berkowitzTrailingIndex s.val l) s
  | .term s e k l => A s (berkowitzTrailingIndex s.val k) *
      (powerEntry (berkowitzStrictTail A s) e.val k l * A (berkowitzTrailingIndex s.val l) s)
  | .cols s e k lo count =>
      ∑ t ∈ Finset.range count, if h : lo + t < n - s.val - 1 then
        A s (berkowitzTrailingIndex s.val k) *
          (powerEntry (berkowitzStrictTail A s) e.val k ⟨lo + t, h⟩ *
            A (berkowitzTrailingIndex s.val ⟨lo + t, h⟩) s) else 0
  | .rows s e lo count =>
      ∑ t ∈ Finset.range count, if h : lo + t < n - s.val - 1 then
        ∑ l : Fin (n - s.val - 1), A s (berkowitzTrailingIndex s.val ⟨lo + t, h⟩) *
          (powerEntry (berkowitzStrictTail A s) e.val ⟨lo + t, h⟩ l *
            A (berkowitzTrailingIndex s.val l) s) else 0

private theorem sum_range_split (f : ℕ → R) (lo count : ℕ) :
    (∑ k ∈ Finset.range count, f (lo + k)) =
      (∑ k ∈ Finset.range (count / 2), f (lo + k)) +
      ∑ k ∈ Finset.range (count - count / 2), f (lo + count / 2 + k) := by
  conv_lhs => rw [← Nat.add_sub_of_le (Nat.div_le_self count 2)]
  rw [Finset.sum_range_add]
  simp [Nat.add_assoc]

theorem berkowitzFactorValue_equations (A : Matrix (Fin n) (Fin n) R)
    (a : BerkowitzFactorAddress n) :
    berkowitzFactorValue A a = match berkowitzFactorInstruction A a with
      | .value v => v
      | .branch op l r => op.apply (berkowitzFactorValue A l) (berkowitzFactorValue A r) := by
  cases a with
  | zero | negOne | row s k | col s l | diag s | power s e k l
  | weighted s e k l | term s e k l => rfl
  | cols s e k lo count =>
    simp only [berkowitzFactorInstruction]
    split_ifs with hc0 hc1 hlo
    · subst count; simp [berkowitzFactorValue]
    · subst count; simp [berkowitzFactorValue, hlo, BinaryOp.apply]
    · subst count; simp [berkowitzFactorValue, hlo]
    · simp only [berkowitzFactorValue, BinaryOp.apply]
      exact sum_range_split (fun t ↦ if h : t < n - s.val - 1 then
        A s (berkowitzTrailingIndex s.val k) *
          (powerEntry (berkowitzStrictTail A s) e.val k ⟨t, h⟩ *
            A (berkowitzTrailingIndex s.val ⟨t, h⟩) s) else 0) lo count
  | rows s e lo count =>
    simp only [berkowitzFactorInstruction]
    split_ifs with hc0 hc1 hlo
    · subst count; simp [berkowitzFactorValue]
    · subst count
      simp only [berkowitzFactorValue, Finset.sum_range_one, dite_true, hlo,
        BinaryOp.apply, add_zero, Nat.zero_add]
      rw [Finset.sum_fin_eq_sum_range]
    · subst count; simp [berkowitzFactorValue, hlo]
    · simp only [berkowitzFactorValue, BinaryOp.apply]
      exact sum_range_split (fun t ↦ if h : t < n - s.val - 1 then
        ∑ l : Fin (n - s.val - 1), A s (berkowitzTrailingIndex s.val ⟨t, h⟩) *
          (powerEntry (berkowitzStrictTail A s) e.val ⟨t, h⟩ l *
            A (berkowitzTrailingIndex s.val l) s) else 0) lo count
  | entry s i j =>
    simp only [berkowitzFactorInstruction]
    split_ifs with hij h0 h1
    · simp only [berkowitzFactorValue, indexedBerkowitzFactor, s.isLt, ↓reduceDIte,
        hij, true_and, ↓reduceIte, h0, berkowitzColumnEntry]
    · simp only [berkowitzFactorValue, indexedBerkowitzFactor, s.isLt, ↓reduceDIte,
        hij, true_and, ↓reduceIte, h1, berkowitzColumnEntry, BinaryOp.apply, neg_one_mul]
    · have he : i.val - j.val = (i.val - j.val - 2) + 2 := by omega
      simp only [berkowitzFactorValue, indexedBerkowitzFactor, s.isLt, ↓reduceDIte,
        hij, true_and, ↓reduceIte, BinaryOp.apply, neg_one_mul, Nat.zero_add]
      conv_lhs => rw [he, berkowitzColumnEntry]
      congr 1
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro t ht
      split_ifs with ht'
      · apply Finset.sum_congr rfl
        intro l _
        simp only [berkowitzStrictTail]
        ring
      · rfl
    · simp only [berkowitzFactorValue, indexedBerkowitzFactor, s.isLt, ↓reduceDIte,
        hij, ↓reduceIte]

theorem berkowitzFactorProgram_value (A : Matrix (Fin n) (Fin n) R)
    (a : BerkowitzFactorAddress n) : (berkowitzFactorProgram A).value a =
      berkowitzFactorValue A a := by
  apply EntryProgram.value_eq_of_equations
  intro a
  have h := berkowitzFactorValue_equations A a
  cases he : berkowitzFactorInstruction A a <;>
    simpa only [berkowitzFactorProgram, he] using h

end SparseIrred.UpperBounds.Section4
