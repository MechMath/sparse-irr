import SparseIrred.UpperBounds.Section4.StackEvaluator
import SparseIrred.UpperBounds.SuccinctMatrix

/-!
# Arithmetic evaluation and Boolean tests in one address machine

Field arithmetic embeds unchanged. The additional Boolean values allow a single
stack evaluator to take nonzero tests, conjoin the squarefree filter and fold
over all deleted minors, without assuming an implementation of a full test.
-/

namespace SparseIrred.UpperBounds.Section4

inductive DecisionScalar (K : Type*) where
  | scalar (value : K)
  | flag (value : Bool)
  | nonzeroTag
  deriving DecidableEq

variable {K : Type*} [Add K] [Mul K] [Zero K] [DecidableEq K]

instance : Add (DecisionScalar K) where
  add x y := match x, y with
    | .scalar a, .scalar b => .scalar (a + b)
    | .flag a, .flag b => .flag (a || b)
    | _, _ => .flag false

instance : Mul (DecisionScalar K) where
  mul x y := match x, y with
    | .scalar a, .scalar b => .scalar (a * b)
    | .flag a, .flag b => .flag (a && b)
    | .nonzeroTag, .scalar a => .flag (decide (a ≠ 0))
    | _, _ => .flag false

@[simp] theorem DecisionScalar.scalar_add (a b : K) :
    (DecisionScalar.scalar a + .scalar b) = .scalar (a + b) := rfl

@[simp] theorem DecisionScalar.scalar_mul (a b : K) :
    (DecisionScalar.scalar a * .scalar b) = .scalar (a * b) := rfl

@[simp] theorem DecisionScalar.flag_add (a b : Bool) :
    (DecisionScalar.flag a + .flag b : DecisionScalar K) = .flag (a || b) := rfl

@[simp] theorem DecisionScalar.flag_mul (a b : Bool) :
    (DecisionScalar.flag a * .flag b : DecisionScalar K) = .flag (a && b) := rfl

@[simp] theorem DecisionScalar.nonzero_mul (a : K) :
    ((DecisionScalar.nonzeroTag : DecisionScalar K) * .scalar a) = .flag (decide (a ≠ 0)) := rfl

section Map
variable {A R S : Type*} [Add R] [Mul R] [Add S] [Mul S]

def EntryProgram.mapInstruction (P : EntryProgram A R) (f : R → S) (a : A) :
    EntryInstruction A S := match P.instruction a with
  | .value v => .value (f v)
  | .branch op l r => .branch op l r

/-- Change only the scalar representation used at leaves and in arithmetic registers. -/
def EntryProgram.mapValues (P : EntryProgram A R) (f : R → S) : EntryProgram A S where
  instruction := P.mapInstruction f
  rank := P.rank
  descend a op l r h := by
    unfold mapInstruction at h
    split at h <;> rename_i he
    · cases h
    · cases h; exact P.descend _ _ _ _ he

theorem EntryProgram.mapValues_value (P : EntryProgram A R) (f : R → S)
    (hadd : ∀ a b, f (a + b) = f a + f b) (hmul : ∀ a b, f (a * b) = f a * f b)
    (a : A) : (P.mapValues f).value a = f (P.value a) := by
  apply (P.mapValues f).value_eq_of_equations (fun a ↦ f (P.value a))
  intro b
  cases he : P.instruction b with
  | value v => simp only [mapValues, mapInstruction, he]; rw [value, he]
  | branch op l r =>
    simp only [mapValues, mapInstruction, he]
    rw [value, he]
    cases op <;> simp only [BinaryOp.apply, hadd, hmul]

@[simp] theorem EntryProgram.mapValues_rank (P : EntryProgram A R) (f : R → S) (a : A) :
    (P.mapValues f).rank a = P.rank a := rfl
end Map

/-- A field program remains the same arithmetic computation inside the decision scalar type. -/
def scalarProgram {A : Type*} (P : EntryProgram A K) : EntryProgram A (DecisionScalar K) :=
  P.mapValues DecisionScalar.scalar

@[simp] theorem scalarProgram_value {A : Type*} (P : EntryProgram A K) (a : A) :
    (scalarProgram P).value a = .scalar (P.value a) :=
  P.mapValues_value DecisionScalar.scalar (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) a

inductive TestAddress (A : Type*) where
  | test
  | tag
  | call (address : A)

/-- A nonzero test invokes the entire field program as a child computation. -/
def nonzeroProgram {A : Type*} (P : EntryProgram A K) (initial : A) :
    EntryProgram (TestAddress A) (DecisionScalar K) where
  instruction a := match a with
    | .test => .branch .mul .tag (.call initial)
    | .tag => .value .nonzeroTag
    | .call a => match P.instruction a with
      | .value v => .value (.scalar v)
      | .branch op l r => .branch op (.call l) (.call r)
  rank a := match a with
    | .test => P.rank initial + 2
    | .tag => 0
    | .call a => P.rank a + 1
  descend a op l r h := by
    cases a with
    | test => cases h; dsimp only; omega
    | tag => cases h
    | call a =>
      dsimp only at h ⊢
      cases he : P.instruction a with
      | value v => simp only [he] at h; cases h
      | branch op l r =>
        simp only [he] at h
        cases h
        have hd := P.descend _ _ _ _ he
        dsimp only
        omega

private def nonzeroMeaning {A : Type*} (P : EntryProgram A K) (initial : A) :
    TestAddress A → DecisionScalar K
  | .test => .flag (decide (P.value initial ≠ 0))
  | .tag => .nonzeroTag
  | .call a => .scalar (P.value a)

theorem nonzeroProgram_value {A : Type*} (P : EntryProgram A K) (initial : A) :
    (nonzeroProgram P initial).value .test = .flag (decide (P.value initial ≠ 0)) := by
  apply (nonzeroProgram P initial).value_eq_of_equations (nonzeroMeaning P initial)
  intro a
  cases a with
  | test => rfl
  | tag => rfl
  | call a =>
    cases he : P.instruction a with
    | value v => simp only [nonzeroProgram, he, nonzeroMeaning]; rw [EntryProgram.value, he]
    | branch op l r =>
      simp only [nonzeroProgram, he, nonzeroMeaning]
      rw [EntryProgram.value, he]
      cases op <;> rfl

@[simp] theorem nonzeroProgram_rank {A : Type*} (P : EntryProgram A K) (initial : A) :
    (nonzeroProgram P initial).rank .test = P.rank initial + 2 := rfl

end SparseIrred.UpperBounds.Section4
