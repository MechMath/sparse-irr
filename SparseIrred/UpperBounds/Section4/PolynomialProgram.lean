import SparseIrred.UpperBounds.Section4.BerkowitzFrobeniusProgram
import SparseIrred.UpperBounds.Section4.EntryMachineBoolean
import SparseIrred.UpperBounds.Section4.PrimalityProgram

/-!
# The complete polynomial test as one address-stack program

The squarefree filter and all deleted minors are combined by Boolean arithmetic.
Every determinant, its Berkowitz factors, and every Frobenius power are expanded
into the same local evaluator. Leaves read coefficients or perform field operations.
-/

noncomputable section

namespace SparseIrred.UpperBounds.Section4

open Polynomial Matrix

set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def sylvesterProgram (f : K[X]) :
    EntryProgram (BerkowitzAddress (f.natDegree + f.derivative.natDegree)) K :=
  berkowitzProgram (fun i j ↦ coefficientSylvesterEntry f i.val j.val)

theorem sylvesterProgram_value (f : K[X]) :
    (sylvesterProgram f).value .initial = f.resultant f.derivative := by
  rw [sylvesterProgram, berkowitzProgram_value]
  congr 1
  ext i j
  exact coefficientSylvesterEntry_eq f i j

def minorPair (d : ℕ) (k : Fin ((d - 1 + 1) * (d - 1 + 1))) :
    Fin (d - 1 + 1) × Fin (d - 1 + 1) := finProdFinEquiv.symm k

abbrev MinorSearchAddress (d : ℕ) :=
  OrAddress (fun _ : Fin ((d - 1 + 1) * (d - 1 + 1)) ↦
    TestAddress (FrobeniusMinorAddress d))

def minorSearchProgram (f : K[X]) (hf : 0 < f.natDegree) :
    EntryProgram (MinorSearchAddress f.natDegree) (DecisionScalar K) :=
  orProgram (fun k ↦ nonzeroProgram
    (minorProgram f hf (minorPair _ k).1 (minorPair _ k).2) (minorInitial f.natDegree))
    (fun _ ↦ .test) (minorStackBound f.natDegree (Fintype.card K) + 2)
    (fun k ↦ by
      rw [nonzeroProgram_rank]
      exact Nat.add_le_add_right (minorProgram_rank_initial f hf _ _) 2)

def minorSearchInitial (d : ℕ) : MinorSearchAddress d := .range 0 ((d - 1 + 1) * (d - 1 + 1))

def minorAnswer (f : K[X]) (hf : 0 < f.natDegree)
    (k : Fin ((f.natDegree - 1 + 1) * (f.natDegree - 1 + 1))) : Bool :=
  decide (((positiveCoefficientFrobenius f hf - 1).submatrix
    (minorPair _ k).1.succAbove (minorPair _ k).2.succAbove).det ≠ 0)

theorem minorLeaf_value (f : K[X]) (hf : 0 < f.natDegree)
    (k : Fin ((f.natDegree - 1 + 1) * (f.natDegree - 1 + 1))) :
    (nonzeroProgram (minorProgram f hf (minorPair _ k).1 (minorPair _ k).2)
      (minorInitial f.natDegree)).value .test = .flag (minorAnswer f hf k) := by
  rw [nonzeroProgram_value, minorProgram_value]
  rfl

def minorSearchAnswer (f : K[X]) (hf : 0 < f.natDegree) : Bool :=
  (List.range ((f.natDegree - 1 + 1) * (f.natDegree - 1 + 1))).any
    (fun k ↦ if hk : k < (f.natDegree - 1 + 1) * (f.natDegree - 1 + 1) then
      minorAnswer f hf ⟨k, hk⟩ else false)

theorem minorSearchProgram_value (f : K[X]) (hf : 0 < f.natDegree) :
    (minorSearchProgram f hf).value (minorSearchInitial f.natDegree) =
      .flag (minorSearchAnswer f hf) := by
  rw [minorSearchProgram, minorSearchInitial,
    orProgram_value _ _ _ _ (minorAnswer f hf) (minorLeaf_value f hf)]
  simp only [minorSearchAnswer, Nat.zero_add]

theorem minorSearchAnswer_correct (f : K[X]) (hf : 0 < f.natDegree) :
    minorSearchAnswer f hf = true ↔ ∃ i j : Fin (f.natDegree - 1 + 1),
      ((positiveCoefficientFrobenius f hf - 1).submatrix i.succAbove j.succAbove).det ≠ 0 := by
  have h := orProgram_true_iff
    (fun k ↦ nonzeroProgram (minorProgram f hf (minorPair _ k).1 (minorPair _ k).2)
      (minorInitial f.natDegree)) (fun _ ↦ .test)
    (minorStackBound f.natDegree (Fintype.card K) + 2)
    (fun k ↦ Nat.add_le_add_right (minorProgram_rank_initial f hf _ _) 2)
    (minorAnswer f hf) (minorLeaf_value f hf)
  change (minorSearchProgram f hf).value (minorSearchInitial _) = .flag true ↔ _ at h
  rw [minorSearchProgram_value, DecisionScalar.flag.injEq] at h
  rw [h]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨(minorPair _ k).1, (minorPair _ k).2, of_decide_eq_true hk⟩
  · rintro ⟨i, j, hij⟩
    refine ⟨finProdFinEquiv (i, j), ?_⟩
    simpa [minorAnswer, minorPair] using hij

abbrev PositivePolynomialAddress (n e : ℕ) :=
  BinaryAddress (TestAddress (BerkowitzAddress (n + e))) (MinorSearchAddress n)

def positivePolynomialProgram (f : K[X]) (hf : 0 < f.natDegree) :
    EntryProgram (PositivePolynomialAddress f.natDegree f.derivative.natDegree) (DecisionScalar K) :=
  binaryProgram .mul (nonzeroProgram (sylvesterProgram f) .initial)
    (minorSearchProgram f hf) .test (minorSearchInitial f.natDegree)

theorem positivePolynomialProgram_value (f : K[X]) (hf : 0 < f.natDegree) :
    (positivePolynomialProgram f hf).value .root =
      .flag (decide (f.resultant f.derivative ≠ 0) && minorSearchAnswer f hf) := by
  rw [positivePolynomialProgram, binaryProgram_value, nonzeroProgram_value,
    sylvesterProgram_value, minorSearchProgram_value]
  rfl

theorem positivePolynomialProgram_correct (f : K[X]) (hf : 0 < f.natDegree) :
    ((positivePolynomialProgram f hf).value .root).asBool = true ↔ Irreducible f := by
  rw [positivePolynomialProgram_value]
  simp only [DecisionScalar.asBool, Bool.and_eq_true, decide_eq_true_eq,
    minorSearchAnswer_correct]
  have h := irreducible_iff_coefficient_oracle_tests f hf
  simp only [determinantEntry_eq_det] at h
  have hsyl : Matrix.det (fun i j : Fin (f.natDegree + f.derivative.natDegree) ↦
      coefficientSylvesterEntry f i.val j.val) = f.resultant f.derivative :=
    (berkowitzProgram_value _).symm.trans (sylvesterProgram_value f)
  rw [hsyl] at h
  exact h.symm

abbrev PolynomialAddress (n e : ℕ) := Option (PositivePolynomialAddress n e)

/-- Add an unused false leaf, giving a common address type for the degree-zero case. -/
def optionProgram {A R : Type} (P : EntryProgram A R) (z : R) : EntryProgram (Option A) R where
  instruction a := match a with
    | none => .value z
    | some a => match P.instruction a with
      | .value v => .value v
      | .branch op l r => .branch op (some l) (some r)
  rank a := match a with | none => 0 | some a => P.rank a
  descend a op l r h := by
    cases a with
    | none => cases h
    | some a =>
      dsimp only at h ⊢
      cases he : P.instruction a with
      | value v => simp only [he] at h; cases h
      | branch op l r => simp only [he] at h; cases h; exact P.descend _ _ _ _ he

theorem optionProgram_value {A R : Type} [Add R] [Mul R] (P : EntryProgram A R) (z : R)
    (a : A) : (optionProgram P z).value (some a) = P.value a := by
  apply (optionProgram P z).value_eq_of_equations (f := fun a : Option A ↦ match a with
    | none => z | some a => P.value a)
  intro a
  cases a with
  | none => rfl
  | some a =>
    cases he : P.instruction a <;> simp only [optionProgram, he] <;>
      rw [EntryProgram.value, he]

/-- All degrees are handled by the same syntax; testing degree zero is a local
metadata check. The zero-degree branch performs no determinant computation. -/
def polynomialProgram (f : K[X]) :
    EntryProgram (PolynomialAddress f.natDegree f.derivative.natDegree) (DecisionScalar K) :=
  if hf : 0 < f.natDegree then optionProgram (positivePolynomialProgram f hf) (.flag false)
  else ⟨fun _ ↦ .value (.flag false), fun _ ↦ 0, fun _ _ _ _ h ↦ by cases h⟩

def polynomialInitial (n e : ℕ) : PolynomialAddress n e := some .root

theorem polynomialProgram_correct (f : K[X]) :
    ((polynomialProgram f).value (polynomialInitial _ _)).asBool = true ↔ Irreducible f := by
  unfold polynomialProgram polynomialInitial
  split_ifs with hf
  · rw [optionProgram_value]
    exact positivePolynomialProgram_correct f hf
  · rw [EntryProgram.value]
    simp only [DecisionScalar.asBool, Bool.false_eq_true, false_iff]
    exact fun hi ↦ hf hi.natDegree_pos

/-- The algebraic conclusion is attached to an actual terminating stack run. -/
theorem polynomialProgram_halts_correct (f : K[X]) :
    ∃ t v, (polynomialProgram f).step^[t] (.eval (polynomialInitial _ _) []) = .ret v [] ∧
      (v.asBool = true ↔ Irreducible f) := by
  obtain ⟨t, ht⟩ := (polynomialProgram f).correct (polynomialInitial _ _)
  exact ⟨t, _, ht, polynomialProgram_correct f⟩

end SparseIrred.UpperBounds.Section4
