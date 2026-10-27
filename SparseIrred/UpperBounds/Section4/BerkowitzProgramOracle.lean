import SparseIrred.UpperBounds.Section4.BerkowitzProgram

/-!
# Substituting a succinct matrix-entry program

The determinant machine exposes each request for one entry of the original
matrix. Such a leaf can itself be implemented by another stack program, for
example a companion-matrix power computing one Frobenius entry.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace SparseIrred.UpperBounds.Section4

open Matrix

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Every nonconstant leaf of the fully expanded determinant machine reads one entry. -/
def berkowitzEntryRequest : BerkowitzAddress n → Option (Fin n × Fin n)
  | .core (.inner (.outer (.diag s))) => some (s, s)
  | .core (.inner (.outer (.row s k))) => some (s, berkowitzTrailingIndex s.val k)
  | .core (.inner (.outer (.col s l))) => some (berkowitzTrailingIndex s.val l, s)
  | .core (.inner (.inner ⟨s, .entry _ len i j⟩)) =>
      if len = 1 then some (berkowitzTrailingIndex s.val i, berkowitzTrailingIndex s.val j)
      else none
  | _ => none

/-- A successful leaf request agrees with the value produced by that instruction. -/
theorem berkowitzEntryRequest_value (A : Matrix (Fin n) (Fin n) R)
    (a : BerkowitzAddress n) (ij : Fin n × Fin n) (v : R)
    (hv : (berkowitzProgram A).instruction a = .value v)
    (hr : berkowitzEntryRequest a = some ij) : A ij.1 ij.2 = v := by
  cases a with
  | initial | sign => simp [berkowitzEntryRequest] at hr
  | core a => cases a with
    | zero | outer a => simp [berkowitzEntryRequest] at hr
    | inner a => cases a with
      | zero => simp [berkowitzEntryRequest] at hr
      | outer a =>
        cases a <;> simp only [berkowitzEntryRequest] at hr <;> try cases hr
        all_goals
          simpa only [berkowitzProgram, berkowitzInstruction, berkowitzCoreProgram,
            berkowitzExpandedFactorProgram, EntryProgram.substitute,
            EntryProgram.substituteInstruction, berkowitzFactorProgram,
            berkowitzFactorInstruction, berkowitzPowerRequest, EntryInstruction.value.injEq]
            using hv
      | inner a =>
        rcases a with ⟨s, a⟩
        cases a with
        | zero | sum _ _ _ _ _ _ => simp [berkowitzEntryRequest] at hr
        | entry start len i j =>
          simp only [berkowitzEntryRequest] at hr
          split_ifs at hr with hlen <;> try cases hr
          subst len
          simpa only [berkowitzProgram, berkowitzInstruction, berkowitzCoreProgram,
            berkowitzExpandedFactorProgram, EntryProgram.substitute,
            EntryProgram.substituteInstruction, berkowitzPowerProgram, EntryProgram.family,
            EntryProgram.familyInstruction, productProgram, productInstruction,
            Nat.one_ne_zero, ↓reduceIte, berkowitzStrictTail, Matrix.submatrix_apply,
            EntryInstruction.value.injEq] using hv

/-- A requested entry is itself the entire scalar value of that leaf instruction. -/
theorem berkowitzEntryRequest_instruction (A : Matrix (Fin n) (Fin n) R)
    (a : BerkowitzAddress n) (ij : Fin n × Fin n)
    (hr : berkowitzEntryRequest a = some ij) :
    (berkowitzProgram A).instruction a = .value (A ij.1 ij.2) := by
  cases a with
  | initial | sign => simp [berkowitzEntryRequest] at hr
  | core a => cases a with
    | zero | outer a => simp [berkowitzEntryRequest] at hr
    | inner a => cases a with
      | zero => simp [berkowitzEntryRequest] at hr
      | outer a =>
        cases a <;> simp only [berkowitzEntryRequest] at hr <;> try cases hr
        all_goals rfl
      | inner a =>
        rcases a with ⟨s, a⟩
        cases a with
        | zero | sum _ _ _ _ _ _ => simp [berkowitzEntryRequest] at hr
        | entry start len i j =>
          simp only [berkowitzEntryRequest] at hr
          split_ifs at hr with hlen <;> try cases hr
          subst len
          simp only [berkowitzProgram, berkowitzInstruction, berkowitzCoreProgram,
            berkowitzExpandedFactorProgram, EntryProgram.substitute,
            EntryProgram.substituteInstruction, berkowitzPowerProgram, EntryProgram.family,
            EntryProgram.familyInstruction, productProgram, productInstruction,
            Nat.one_ne_zero, ↓reduceIte, berkowitzStrictTail, Matrix.submatrix_apply]

/-- Every other local instruction is independent of the matrix entries. -/
theorem berkowitzEntryRequest_none_instruction (A A' : Matrix (Fin n) (Fin n) R)
    (a : BerkowitzAddress n) (hr : berkowitzEntryRequest a = none) :
    (berkowitzProgram A).instruction a = (berkowitzProgram A').instruction a := by
  cases a with
  | initial | sign => rfl
  | core a => cases a with
    | zero => rfl
    | outer a =>
      cases a with
      | zero => rfl
      | sum start len i j lo count => rfl
      | entry start len i j =>
        by_cases h0 : len = 0
        · subst len; rfl
        by_cases h1 : len = 1
        · subst len
          by_cases hs : start < n
          all_goals simp only [berkowitzProgram, berkowitzInstruction, berkowitzCoreProgram,
            EntryProgram.substitute, EntryProgram.substituteInstruction, productProgram,
            productInstruction, Nat.one_ne_zero, ↓reduceIte, berkowitzFactorRequest, hs,
            ↓reduceDIte, indexedBerkowitzFactor]
        · simp only [berkowitzProgram, berkowitzInstruction, berkowitzCoreProgram,
            EntryProgram.substitute, EntryProgram.substituteInstruction, productProgram,
            productInstruction, h0, h1, ↓reduceIte]
    | inner a => cases a with
      | zero => rfl
      | outer a =>
        cases a with
        | diag s | row s k | col s l => simp [berkowitzEntryRequest] at hr
        | zero | negOne | power s e k l | weighted s e k l | term s e k l
        | rows s e lo count | cols s e k lo count | entry s i j => rfl
      | inner a =>
        rcases a with ⟨s, a⟩
        cases a with
        | zero | sum start len i j lo count => rfl
        | entry start len i j =>
          have h1 : len ≠ 1 := by simpa [berkowitzEntryRequest] using hr
          by_cases h0 : len = 0
          · subst len; rfl
          · simp only [berkowitzProgram, berkowitzInstruction, berkowitzCoreProgram,
              berkowitzExpandedFactorProgram, EntryProgram.substitute,
              EntryProgram.substituteInstruction, berkowitzPowerProgram, EntryProgram.family,
              EntryProgram.familyInstruction, productProgram, productInstruction,
              h0, h1, ↓reduceIte]

def berkowitzSubprogramRequest {B : Type*} (initial : Fin n × Fin n → B) :
    BerkowitzAddress n → Option B := fun a ↦ (berkowitzEntryRequest a).map initial

theorem berkowitzSubprogramRequest_rank {B : Type*} (Q : EntryProgram B R)
    (initial : Fin n × Fin n → B) (K : ℕ) (hK : ∀ ij, Q.rank (initial ij) ≤ K)
    (a : BerkowitzAddress n) (b : B) (hr : berkowitzSubprogramRequest initial a = some b) :
    Q.rank b ≤ K := by
  unfold berkowitzSubprogramRequest at hr
  cases he : berkowitzEntryRequest a with
  | none => simp [he] at hr
  | some ij =>
    simp only [he, Option.map_some, Option.some.injEq] at hr
    subst b
    exact hK ij

/-- Compile each matrix entry as a subprogram, with no scalar-entry correctness assumption. -/
def berkowitzWithEntryProgram {B : Type*} (A : Matrix (Fin n) (Fin n) R)
    (Q : EntryProgram B R) (initial : Fin n × Fin n → B) (K : ℕ)
    (hK : ∀ ij, Q.rank (initial ij) ≤ K) :
    EntryProgram (SubstituteAddress (BerkowitzAddress n) B) R :=
  (berkowitzProgram A).substitute Q (berkowitzSubprogramRequest initial) K
    (berkowitzSubprogramRequest_rank Q initial K hK)

/-- The composed program returns the determinant of the matrix computed by its entry calls. -/
theorem berkowitzWithEntryProgram_value {B : Type*} (A : Matrix (Fin n) (Fin n) R)
    (Q : EntryProgram B R) (initial : Fin n × Fin n → B) (K : ℕ)
    (hK : ∀ ij, Q.rank (initial ij) ≤ K)
    (hQ : ∀ ij, Q.value (initial ij) = A ij.1 ij.2) :
    (berkowitzWithEntryProgram A Q initial K hK).value (.outer .initial) = A.det := by
  have hvalue : ∀ a b v, (berkowitzProgram A).instruction a = .value v →
      berkowitzSubprogramRequest initial a = some b → Q.value b = v := by
    intro a b v hv hr
    unfold berkowitzSubprogramRequest at hr
    cases he : berkowitzEntryRequest a with
    | none => simp [he] at hr
    | some ij =>
      simp only [he, Option.map_some, Option.some.injEq] at hr
      subst b
      rw [hQ]
      exact berkowitzEntryRequest_value A a ij v hv he
  rw [berkowitzWithEntryProgram, EntryProgram.substitute_value _ _ _ _ _ hvalue]
  exact berkowitzProgram_value A

/-- Depths add when, for example, Frobenius entries invoke companion-matrix powering. -/
theorem berkowitzWithEntryProgram_stack_bound {B : Type*} (A : Matrix (Fin n) (Fin n) R)
    (Q : EntryProgram B R) (initial : Fin n × Fin n → B) (K : ℕ)
    (hK : ∀ ij, Q.rank (initial ij) ≤ K) (t : ℕ) :
    ((berkowitzWithEntryProgram A Q initial K hK).step^[t]
      (.eval (.outer .initial) [])).stack.length ≤ berkowitzStackBound n + K + 2 := by
  have h := (berkowitzProgram A).substitute_stack_bound Q
    (berkowitzSubprogramRequest initial) K (berkowitzSubprogramRequest_rank Q initial K hK)
    .initial t
  exact h.trans (by have := berkowitzProgram_rank_initial A; omega)

private theorem program_ext {A R : Type*} (P Q : EntryProgram A R)
    (hi : P.instruction = Q.instruction) (hr : P.rank = Q.rank) : P = Q := by
  cases P
  cases Q
  cases hi
  cases hr
  rfl

/-- After entry substitution the local machine contains no dependence on a dense matrix. -/
theorem berkowitzWithEntryProgram_eq {B : Type*} (A A' : Matrix (Fin n) (Fin n) R)
    (Q : EntryProgram B R) (initial : Fin n × Fin n → B) (K : ℕ)
    (hK : ∀ ij, Q.rank (initial ij) ≤ K) :
    berkowitzWithEntryProgram A Q initial K hK =
      berkowitzWithEntryProgram A' Q initial K hK := by
  apply program_ext
  · funext a
    cases a with
    | zero | inner b => rfl
    | outer a =>
      cases he : berkowitzEntryRequest a with
      | none =>
        have hi := berkowitzEntryRequest_none_instruction A A' a he
        simp only [berkowitzWithEntryProgram, EntryProgram.substitute,
          EntryProgram.substituteInstruction, hi]
      | some ij =>
        have hi := berkowitzEntryRequest_instruction A a ij he
        have hi' := berkowitzEntryRequest_instruction A' a ij he
        simp only [berkowitzWithEntryProgram, EntryProgram.substitute,
          EntryProgram.substituteInstruction, hi, hi', berkowitzSubprogramRequest, he,
          Option.map_some]
  · rfl

/-- An implementation that only receives the matrix-entry subprogram and binary dimensions. -/
def berkowitzOracleProgram {B : Type*} (Q : EntryProgram B R)
    (initial : Fin n × Fin n → B) (K : ℕ) (hK : ∀ ij, Q.rank (initial ij) ≤ K) :
    EntryProgram (SubstituteAddress (BerkowitzAddress n) B) R :=
  berkowitzWithEntryProgram (0 : Matrix (Fin n) (Fin n) R) Q initial K hK

theorem berkowitzOracleProgram_value {B : Type*} (A : Matrix (Fin n) (Fin n) R)
    (Q : EntryProgram B R) (initial : Fin n × Fin n → B) (K : ℕ)
    (hK : ∀ ij, Q.rank (initial ij) ≤ K)
    (hQ : ∀ ij, Q.value (initial ij) = A ij.1 ij.2) :
    (berkowitzOracleProgram Q initial K hK).value (.outer .initial) = A.det := by
  rw [berkowitzOracleProgram, berkowitzWithEntryProgram_eq 0 A]
  exact berkowitzWithEntryProgram_value A Q initial K hK hQ

end SparseIrred.UpperBounds.Section4
