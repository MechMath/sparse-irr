import SparseIrred.UpperBounds.Section4.EntryMachineBooleanBounds
import SparseIrred.UpperBounds.Section4.PolynomialProgramBounds

/-! # The complete polynomial program has a faithful polynomial-width address code -/

noncomputable section
namespace SparseIrred.UpperBounds.Section4

open Polynomial Complexity SparseDiv SparseDiv.StringArith

set_option backward.isDefEq.respectTransparency false

def minorAddressBound (d q : ℕ) : FrobeniusMinorAddress d → Prop :=
  SubstituteAddress.Bounded BerkowitzAddress.Bounded (FrobeniusEntryAddress.Bounded q)

def minorSearchBound (d q : ℕ) : MinorSearchAddress d → Prop :=
  OrAddress.Bounded (fun _ ↦ TestAddress.Bounded (minorAddressBound d q))

def positivePolynomialBound (d e q : ℕ) : PositivePolynomialAddress d e → Prop :=
  BinaryAddress.Bounded (TestAddress.Bounded BerkowitzAddress.Bounded) (minorSearchBound d q)

def polynomialAddressBound (d e q : ℕ) : PolynomialAddress d e → Prop
  | none => True
  | some a => positivePolynomialBound d e q a

def minorSearchCode (d : ℕ) : MinorSearchAddress d → List Bool :=
  OrAddress.binaryCode (fun _ ↦ TestAddress.binaryCode frobeniusMinorCode)

def positivePolynomialCode (d e : ℕ) : PositivePolynomialAddress d e → List Bool :=
  BinaryAddress.binaryCode (TestAddress.binaryCode BerkowitzAddress.binaryCode) (minorSearchCode d)

def polynomialAddressCode (d e : ℕ) : PolynomialAddress d e → List Bool
  | none => [false]
  | some a => true :: positivePolynomialCode d e a

theorem minorSearchCode_injective (d : ℕ) : Function.Injective (minorSearchCode d) :=
  OrAddress.binaryCode_injective _ (fun _ ↦ TestAddress.binaryCode_injective _
    frobeniusMinorCode_injective)

theorem positivePolynomialCode_injective (d e : ℕ) :
    Function.Injective (positivePolynomialCode d e) :=
  BinaryAddress.binaryCode_injective _ _
    (TestAddress.binaryCode_injective _ BerkowitzAddress.binaryCode_injective)
    (minorSearchCode_injective d)

theorem polynomialAddressCode_injective (d e : ℕ) :
    Function.Injective (polynomialAddressCode d e) := by
  intro a b h
  cases a <;> cases b <;> simp only [polynomialAddressCode, List.cons.injEq,
    Bool.false_eq_true, Bool.true_eq_false, false_and, true_and] at h
  all_goals try contradiction
  · rfl
  · exact congrArg some (positivePolynomialCode_injective d e h)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem minorSearchProgram_closed (f : K[X]) (hf : 0 < f.natDegree) :
    (minorSearchProgram f hf).Closed (minorSearchBound f.natDegree (Fintype.card K)) := by
  apply orProgram_closed
  · intro k
    apply nonzeroProgram_closed
    · exact minorProgram_closed f hf _ _
    · exact minorInitial_bounded _ _
  · intro k
    trivial

theorem positivePolynomialProgram_closed (f : K[X]) (hf : 0 < f.natDegree) :
    (positivePolynomialProgram f hf).Closed
      (positivePolynomialBound f.natDegree f.derivative.natDegree (Fintype.card K)) := by
  apply binaryProgram_closed
  · apply nonzeroProgram_closed
    · exact berkowitzProgram_closed _
    · trivial
  · exact minorSearchProgram_closed f hf
  · trivial
  · change 0 + _ ≤ _
    omega

theorem optionProgram_closed {A R : Type} (P : EntryProgram A R) (z : R) (B : A → Prop)
    (hP : P.Closed B) :
    (optionProgram P z).Closed (fun a ↦ match a with | none => True | some a => B a) := by
  intro a op l r ha he
  cases a with
  | none => cases he
  | some a =>
    dsimp only [optionProgram] at he
    cases h : P.instruction a with
    | value v => simp only [h] at he; cases he
    | branch op l r => simp only [h] at he; cases he; exact hP a op l r ha h

theorem polynomialProgram_closed (f : K[X]) :
    (polynomialProgram f).Closed
      (polynomialAddressBound f.natDegree f.derivative.natDegree (Fintype.card K)) := by
  unfold polynomialProgram
  split_ifs with hf
  · intro a op l r ha he
    cases a with
    | none => cases he
    | some a =>
      dsimp only [optionProgram] at he
      cases h : (positivePolynomialProgram f hf).instruction a with
      | value v => simp only [h] at he; cases he
      | branch op l r =>
        simp only [h] at he
        cases he
        exact positivePolynomialProgram_closed f hf a _ _ _ ha h
  · intro a op l r ha he
    cases he

/-- The chosen initial address is valid also for degree zero. -/
theorem polynomialInitial_bounded (d e q : ℕ) :
    polynomialAddressBound d e q (polynomialInitial d e) := trivial

theorem polynomialProgram_addresses_bounded (f : K[X]) (t : ℕ) :
    ((polynomialProgram f).step^[t] (.eval (polynomialInitial _ _) [])).Addresses
      (polynomialAddressBound f.natDegree f.derivative.natDegree (Fintype.card K)) :=
  (polynomialProgram f).addresses_iterate _ (polynomialProgram_closed f) _
    (polynomialInitial_bounded _ _ _) t

private theorem square_size_le (d N : ℕ) (h : d ≤ N) : (d * d).size ≤ 2 * N.size := by
  apply Nat.size_le.mpr
  have hn := Nat.lt_size_self N
  rw [two_mul, pow_add]
  nlinarith

theorem minorSearchCode_length (d q N : ℕ) (a : MinorSearchAddress d)
    (ha : minorSearchBound d q a) (hd : d + 1 ≤ N) (hq : q * d ≤ N) :
    (minorSearchCode d a).length ≤ 32 * (N.size + 6) := by
  have hw := OrAddress.binaryCode_length_of_bounded
    (fun _ ↦ TestAddress.binaryCode frobeniusMinorCode)
    (fun _ ↦ TestAddress.Bounded (minorAddressBound d q)) (24 * (N.size + 5) + 2)
    (by
      intro i b hb
      exact TestAddress.binaryCode_length_of_bounded _ _ _
        (fun c hc ↦ frobeniusMinorCode_length_of_bounded c q N hc (by omega) (by omega) hq)
        b hb) a ha
  have hs := square_size_le (d - 1 + 1) N (by omega)
  exact hw.trans (by omega)

theorem positivePolynomialCode_length (d e q N : ℕ) (a : PositivePolynomialAddress d e)
    (ha : positivePolynomialBound d e q a) (hd : d + e + 1 ≤ N) (hq : q * d ≤ N) :
    (positivePolynomialCode d e a).length ≤ 34 * (N.size + 6) := by
  have hw := BinaryAddress.binaryCode_length_of_bounded
    (TestAddress.binaryCode BerkowitzAddress.binaryCode) (minorSearchCode d)
    (TestAddress.Bounded BerkowitzAddress.Bounded) (minorSearchBound d q)
    (22 * (N.size + 5) + 2) (32 * (N.size + 6))
    (by
      intro b hb
      exact TestAddress.binaryCode_length_of_bounded _ _ _
        (fun c hc ↦ c.binaryCode_length_of_bounded N hc hd) b hb)
    (fun b hb ↦ minorSearchCode_length d q N b hb (by omega) hq) a ha
  exact hw.trans (by omega)

/-- A uniform bound for every address in the complete polynomial computation. -/
theorem polynomialAddressCode_length (d e q N : ℕ) (a : PolynomialAddress d e)
    (ha : polynomialAddressBound d e q a) (hd : d + e + 1 ≤ N) (hq : q * d ≤ N) :
    (polynomialAddressCode d e a).length ≤ 40 * (N.size + 6) := by
  cases a with
  | none => simp [polynomialAddressCode]; omega
  | some a =>
    have hw := positivePolynomialCode_length d e q N a ha hd hq
    simp only [polynomialAddressCode, List.length_cons]
    omega

/-- The address bit bound is polynomial in the actual encoded degree and field size. -/
theorem polynomialAddressCode_length_input (d e q L : ℕ) (a : PolynomialAddress d e)
    (ha : polynomialAddressBound d e q a) (he : e ≤ d)
    (hd : d.size ≤ L) (hq : q.size ≤ L ^ 2 + 1) :
    (polynomialAddressCode d e a).length ≤ 160 * (L + 3) ^ 2 := by
  let N := (q + 2) * (d + e + 2)
  have hN : d + e + 1 ≤ N := by dsimp [N]; nlinarith
  have hqd : q * d ≤ N := by dsimp [N]; nlinarith
  have hqn : q + 2 < 2 ^ (q.size + 2) := by
    have h := Nat.lt_size_self q
    have hp : 1 ≤ 2 ^ q.size := Nat.one_le_pow _ _ (by omega)
    simp only [pow_succ]
    omega
  have hdn : d + e + 2 < 2 ^ (L + 2) := by
    have h := Nat.size_le.mp hd
    have hp : 0 < 2 ^ L := pow_pos (by omega) _
    simp only [pow_succ]
    omega
  have hNs : N.size ≤ q.size + L + 4 := by
    apply Nat.size_le.mpr
    calc
      N < 2 ^ (q.size + 2) * 2 ^ (L + 2) := by dsimp [N]; nlinarith
      _ = 2 ^ (q.size + L + 4) := by rw [← pow_add]; congr 1; omega
  have hw := polynomialAddressCode_length d e q N a ha hN hqd
  nlinarith

/-- Every intermediate bitstring of the complete polynomial evaluator has a
uniform polynomial length; the number of recursive calls does not occur here. -/
theorem polynomialConfig_code_length_input (f : K[X]) (encK : K → List Bool) (L : ℕ)
    (hscalar : ∀ v, (encK v).length ≤ 2 * L ^ 2 + 2 * L)
    (hd : f.natDegree.size ≤ L) (hq : (Fintype.card K).size ≤ L ^ 2 + 1) (t : ℕ) :
    (((polynomialProgram f).step^[t] (.eval (polynomialInitial _ _) [])).framedEncode
      (polynomialAddressCode _ _) (DecisionScalar.binaryCode encK)).length ≤
      1000000 * (L + 3) ^ 8 := by
  have hstate := polynomialProgram_addresses_bounded f t
  have hstack := polynomialProgram_stack_input f L hd hq t
  have haddr : ∀ a, polynomialAddressBound f.natDegree f.derivative.natDegree
      (Fintype.card K) a → (polynomialAddressCode _ _ a).length ≤ 200 * (L + 3) ^ 4 := by
    intro a ha
    have h := polynomialAddressCode_length_input _ _ _ L a ha
      ((natDegree_derivative_le f).trans (Nat.sub_le _ _)) hd hq
    nlinarith [Nat.zero_le (L ^ 3), Nat.zero_le (L ^ 4)]
  have hval : ∀ v : DecisionScalar K, (v.binaryCode encK).length ≤ 200 * (L + 3) ^ 4 := by
    intro v
    have h := DecisionScalar.binaryCode_length encK (2 * L ^ 2 + 2 * L) hscalar v
    nlinarith [Nat.zero_le (L ^ 3), Nat.zero_le (L ^ 4)]
  have hw := EntryConfig.framedEncode_length_le _ _ _ (200 * (L + 3) ^ 4)
    haddr hval _ hstate
  have hbound : 2 * (200 * (L + 3) ^ 4) +
      (2 * (200 * (L + 3) ^ 4) + 7) * (100 * (L + 3) ^ 4) + 4 ≤
      1000000 * (L + 3) ^ 8 := by
    have h1 : 1 ≤ (L + 3) ^ 4 := Nat.one_le_pow _ _ (by omega)
    have hp : (L + 3) ^ 8 = ((L + 3) ^ 4) ^ 2 := by ring
    rw [hp]
    nlinarith
  exact hw.trans ((by gcongr : _ ≤ 2 * (200 * (L + 3) ^ 4) +
    (2 * (200 * (L + 3) ^ 4) + 7) * (100 * (L + 3) ^ 4) + 4).trans hbound)

end SparseIrred.UpperBounds.Section4
