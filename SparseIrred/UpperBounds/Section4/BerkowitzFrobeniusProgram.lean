import SparseIrred.UpperBounds.Section4.BerkowitzProgramOracle
import SparseIrred.UpperBounds.Section4.FactorRankOracle

/-!
# Frobenius entries and their deleted minors as stack programs

Each Frobenius entry invokes companion-matrix powering. Substituting these calls
into the determinant machine proves the full nested minor computation, with a
bound in the binary lengths of the degree and the field cardinality.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace SparseIrred.UpperBounds.Section4

open Matrix Polynomial

inductive FrobeniusEntryAddress (n : ℕ) where
  | entry (i j : Fin n)
  | delta (i j : Fin n)
  | power (a : ProductAddress n)

variable {K : Type*} [Field K] [Fintype K]

def frobeniusEntryInstruction (f : K[X]) (hf : 0 < f.natDegree) :
    FrobeniusEntryAddress f.natDegree → EntryInstruction (FrobeniusEntryAddress f.natDegree) K
  | .entry i j => .branch .add
      (.power (.entry 0 (Fintype.card K * j.val) i ⟨0, hf⟩)) (.delta i j)
  | .delta i j => .value (if i = j then -1 else 0)
  | .power a => match (productProgram (fun _ ↦ coefficientCompanion f)).instruction a with
    | .value v => .value v
    | .branch op l r => .branch op (.power l) (.power r)

def frobeniusEntryRank (f : K[X]) : FrobeniusEntryAddress f.natDegree → ℕ
  | .entry _ j => (splitDepth (Fintype.card K * j.val) + 1) *
      (splitDepth f.natDegree + 2) + 3
  | .delta _ _ => 0
  | .power a => productRank a + 1

theorem frobeniusEntryInstruction_descend (f : K[X]) (hf : 0 < f.natDegree)
    (a : FrobeniusEntryAddress f.natDegree) (op : BinaryOp)
    (l r : FrobeniusEntryAddress f.natDegree)
    (h : frobeniusEntryInstruction f hf a = .branch op l r) :
    frobeniusEntryRank f l < frobeniusEntryRank f a ∧
      frobeniusEntryRank f r < frobeniusEntryRank f a := by
  cases a with
  | delta i j => simp [frobeniusEntryInstruction] at h
  | entry i j => cases h; simp [frobeniusEntryRank, productRank]
  | power a =>
    cases he : (productProgram (fun _ ↦ coefficientCompanion f)).instruction a with
    | value v => simp [frobeniusEntryInstruction, he] at h
    | branch op' l' r' =>
      simp only [frobeniusEntryInstruction, he, EntryInstruction.branch.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have hd := (productProgram (fun _ ↦ coefficientCompanion f)).descend a op' l' r' he
      change productRank l' < productRank a ∧ productRank r' < productRank a at hd
      simp only [frobeniusEntryRank]
      omega

/-- An entry program for `B-I`, with companion entries as its only nonconstant leaves. -/
def frobeniusEntryProgram (f : K[X]) (hf : 0 < f.natDegree) :
    EntryProgram (FrobeniusEntryAddress f.natDegree) K :=
  ⟨frobeniusEntryInstruction f hf, frobeniusEntryRank f,
    frobeniusEntryInstruction_descend f hf⟩

def frobeniusEntryMeaning (f : K[X]) (hf : 0 < f.natDegree) :
    FrobeniusEntryAddress f.natDegree → K
  | .entry i j => (coefficientFrobenius f hf - 1) i j
  | .delta i j => if i = j then -1 else 0
  | .power a => (productProgram (fun _ ↦ coefficientCompanion f)).value a

theorem frobeniusEntryProgram_value (f : K[X]) (hf : 0 < f.natDegree)
    (i j : Fin f.natDegree) :
    (frobeniusEntryProgram f hf).value (.entry i j) = (coefficientFrobenius f hf - 1) i j := by
  apply EntryProgram.value_eq_of_equations (f := frobeniusEntryMeaning f hf)
  intro a
  cases a with
  | delta i j => rfl
  | entry i j =>
    change (coefficientFrobenius f hf - 1) i j = _
    simp only [frobeniusEntryProgram, frobeniusEntryInstruction, frobeniusEntryMeaning,
      BinaryOp.apply, productProgram_value, intervalProduct_const,
      coefficientFrobenius_sub_one_entry, powerEntry_eq]
    split_ifs <;> ring
  | power a =>
    change (productProgram (fun _ ↦ coefficientCompanion f)).value a = _
    rw [EntryProgram.value]
    cases he : (productProgram (fun _ ↦ coefficientCompanion f)).instruction a <;>
      simp only [frobeniusEntryProgram, frobeniusEntryInstruction, frobeniusEntryMeaning, he]

theorem splitDepth_mul_le (q d j : ℕ) (hj : j ≤ d) :
    splitDepth (q * j) ≤ q.log2 + d.log2 + 3 := by
  have hq : q ≤ 2 ^ (q.log2 + 1) := (Nat.lt_log2_self (n := q)).le
  have hd : d ≤ 2 ^ (d.log2 + 1) := (Nat.lt_log2_self (n := d)).le
  have hmul : q * j ≤ 2 ^ (q.log2 + d.log2 + 2) := calc
    q * j ≤ q * d := Nat.mul_le_mul_left q hj
    _ ≤ 2 ^ (q.log2 + 1) * 2 ^ (d.log2 + 1) := Nat.mul_le_mul hq hd
    _ = 2 ^ (q.log2 + d.log2 + 2) := by rw [← pow_add]; congr 1; omega
  simpa [Nat.add_assoc] using splitDepth_le_of_le_pow (q * j)
    (q.log2 + d.log2 + 2) hmul

/-- Explicit polynomial in the binary lengths of degree and field cardinality. -/
def frobeniusEntryBound (d q : ℕ) : ℕ := (q.log2 + d.log2 + 4) * (d.log2 + 4) + 3

theorem frobeniusEntryProgram_rank (f : K[X]) (hf : 0 < f.natDegree)
    (i j : Fin f.natDegree) :
    (frobeniusEntryProgram f hf).rank (.entry i j) ≤
      frobeniusEntryBound f.natDegree (Fintype.card K) := by
  have he := splitDepth_mul_le (Fintype.card K) f.natDegree j.val (by omega)
  have hd := splitDepth_le_log f.natDegree
  change (splitDepth (Fintype.card K * j.val) + 1) *
    (splitDepth f.natDegree + 2) + 3 ≤ _
  unfold frobeniusEntryBound
  nlinarith

/-- The actual minor whose nonvanishing is tested in Theorem 18. -/
def frobeniusDeletedMinor (f : K[X]) (hf : 0 < f.natDegree)
    (i j : Fin (f.natDegree - 1 + 1)) :
    Matrix (Fin (f.natDegree - 1)) (Fin (f.natDegree - 1)) K :=
  (positiveCoefficientFrobenius f hf - 1).submatrix i.succAbove j.succAbove

def frobeniusMinorEntryInitial (f : K[X]) (hf : 0 < f.natDegree)
    (i j : Fin (f.natDegree - 1 + 1))
    (kl : Fin (f.natDegree - 1) × Fin (f.natDegree - 1)) :
    FrobeniusEntryAddress f.natDegree :=
  .entry (Fin.cast (by omega) (i.succAbove kl.1)) (Fin.cast (by omega) (j.succAbove kl.2))

theorem frobeniusMinorEntryInitial_value (f : K[X]) (hf : 0 < f.natDegree)
    (i j : Fin (f.natDegree - 1 + 1))
    (kl : Fin (f.natDegree - 1) × Fin (f.natDegree - 1)) :
    (frobeniusEntryProgram f hf).value (frobeniusMinorEntryInitial f hf i j kl) =
      frobeniusDeletedMinor f hf i j kl.1 kl.2 := by
  simp [frobeniusMinorEntryInitial, frobeniusEntryProgram_value, frobeniusDeletedMinor,
    positiveCoefficientFrobenius, Matrix.sub_apply, Matrix.one_apply]

abbrev FrobeniusMinorAddress (d : ℕ) :=
  SubstituteAddress (BerkowitzAddress (d - 1)) (FrobeniusEntryAddress d)

/-- The complete deleted-minor machine, including all Frobenius power calls. -/
def minorProgram (f : K[X]) (hf : 0 < f.natDegree)
    (i j : Fin (f.natDegree - 1 + 1)) : EntryProgram (FrobeniusMinorAddress f.natDegree) K :=
  berkowitzOracleProgram (frobeniusEntryProgram f hf)
    (frobeniusMinorEntryInitial f hf i j) (frobeniusEntryBound f.natDegree (Fintype.card K))
    (fun _ ↦ frobeniusEntryProgram_rank f hf _ _)

def minorInitial (d : ℕ) : FrobeniusMinorAddress d := .outer .initial

theorem minorProgram_value (f : K[X]) (hf : 0 < f.natDegree)
    (i j : Fin (f.natDegree - 1 + 1)) :
    (minorProgram f hf i j).value (minorInitial f.natDegree) =
      ((positiveCoefficientFrobenius f hf - 1).submatrix i.succAbove j.succAbove).det :=
  berkowitzOracleProgram_value (frobeniusDeletedMinor f hf i j) _ _ _ _
    (frobeniusMinorEntryInitial_value f hf i j)

theorem minorProgram_correct (f : K[X]) (hf : 0 < f.natDegree)
    (i j : Fin (f.natDegree - 1 + 1)) :
    ∃ t, (minorProgram f hf i j).step^[t] (.eval (minorInitial f.natDegree) []) =
      .ret ((positiveCoefficientFrobenius f hf - 1).submatrix i.succAbove j.succAbove).det [] := by
  simpa only [minorProgram_value] using (minorProgram f hf i j).correct (minorInitial f.natDegree)

def minorStackBound (d q : ℕ) : ℕ := berkowitzStackBound (d - 1) + frobeniusEntryBound d q + 2

theorem minorProgram_rank_initial (f : K[X]) (hf : 0 < f.natDegree)
    (i j : Fin (f.natDegree - 1 + 1)) :
    (minorProgram f hf i j).rank (minorInitial f.natDegree) ≤
      minorStackBound f.natDegree (Fintype.card K) := by
  change (berkowitzProgram (0 : Matrix (Fin (f.natDegree - 1)) (Fin (f.natDegree - 1)) K)).rank
    .initial +
    frobeniusEntryBound f.natDegree (Fintype.card K) + 2 ≤ _
  unfold minorStackBound
  have := berkowitzProgram_rank_initial
    (0 : Matrix (Fin (f.natDegree - 1)) (Fin (f.natDegree - 1)) K)
  omega

theorem minorProgram_stack_bound (f : K[X]) (hf : 0 < f.natDegree)
    (i j : Fin (f.natDegree - 1 + 1)) (t : ℕ) :
    ((minorProgram f hf i j).step^[t] (.eval (minorInitial f.natDegree) [])).stack.length ≤
      minorStackBound f.natDegree (Fintype.card K) :=
  ((minorProgram f hf i j).stack_length_iterate_le _ t).trans
    (minorProgram_rank_initial f hf i j)

end SparseIrred.UpperBounds.Section4
