import SparseIrred.UpperBounds.PrimeStreaming
import SparseDivComplexity.Appendix.IntTerms

/-!
# Sparse evaluation by repeated squaring

Term lists are evaluated without constructing a dense coefficient vector. Exponentiation
halves the exponent at each recursive call. The derivative evaluator skips constant
terms, so it also handles evaluation at zero without introducing a negative exponent.
The results are algebraic correctness and recursion bounds, not machine time certificates.
-/

open Polynomial
open SparseDiv.Appendix

namespace SparseIrred.UpperBounds

/-- Repeated squaring with one recursive call on half the exponent. -/
def binaryPow {M : Type*} [Monoid M] (a : M) (e : ℕ) : M :=
  if e = 0 then 1 else
    let b := binaryPow a (e / 2)
    if e % 2 = 0 then b * b else b * b * a
termination_by e
decreasing_by omega

/-- Repeated squaring computes the ordinary power in any monoid. -/
theorem binaryPow_eq_pow {M : Type*} [Monoid M] (a : M) (e : ℕ) :
    binaryPow a e = a ^ e := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    rw [binaryPow]
    by_cases he : e = 0
    · subst e
      simp
    · rw [ite_eq_right he]
      dsimp only
      have hhalf : e / 2 < e := by omega
      simp only [ih _ hhalf]
      split_ifs with heven
      · rw [← pow_add]
        congr 1
        omega
      · rw [← pow_add, ← pow_succ]
        congr 1
        omega

/-- Maximum nested calls in repeated squaring, including the final exponent-zero call. -/
def binaryPowDepth (e : ℕ) : ℕ :=
  if e = 0 then 1 else 1 + binaryPowDepth (e / 2)
termination_by e
decreasing_by omega

/-- An exponent represented by at most `b` binary digits needs at most `b+1` calls. -/
theorem binaryPowDepth_le_of_lt_pow (e b : ℕ) (he : e < 2 ^ b) :
    binaryPowDepth e ≤ b + 1 := by
  induction b generalizing e with
  | zero =>
    have : e = 0 := by simpa using he
    simp [this, binaryPowDepth]
  | succ b ih =>
    rw [binaryPowDepth]
    split_ifs with hzero
    · omega
    · have hpow : e < 2 * 2 ^ b := by simpa [pow_succ, Nat.mul_comm] using he
      have hhalf : e / 2 < 2 ^ b := by omega
      have := ih _ hhalf
      omega

/-- Repeated squaring has logarithmic recursion depth. -/
theorem binaryPowDepth_le_log (e : ℕ) : binaryPowDepth e ≤ e.log2 + 2 := by
  simpa [Nat.add_assoc] using
    binaryPowDepth_le_of_lt_pow e (e.log2 + 1) Nat.lt_log2_self

/-- Tail-recursive sparse evaluation, with an arbitrary initial accumulator. -/
def sparseEvalAux {K : Type*} [CommRing K] (φ : ℤ →+* K) (a : K) : ITerms → K → K
  | [], s => s
  | (c, e) :: l, s => sparseEvalAux φ a l (s + φ c * binaryPow a e)

/-- Evaluate a sparse integer polynomial after mapping its coefficients to `K`. -/
def sparseEval {K : Type*} [CommRing K] (φ : ℤ →+* K) (a : K) (l : ITerms) : K :=
  sparseEvalAux φ a l 0

/-- The accumulator invariant, without assumptions on sorting or repeated exponents. -/
theorem sparseEvalAux_eq {K : Type*} [CommRing K] (φ : ℤ →+* K) (a : K)
    (l : ITerms) (s : K) :
    sparseEvalAux φ a l s = s + ((toPolyZ l).map φ).eval a := by
  induction l generalizing s with
  | nil => simp [sparseEvalAux]
  | cons t l ih =>
    rcases t with ⟨c, e⟩
    simp [sparseEvalAux, ih, toPolyZ_cons, binaryPow_eq_pow, add_assoc]

/-- Correctness of sparse evaluation over an arbitrary commutative coefficient ring. -/
theorem sparseEval_eq {K : Type*} [CommRing K] (φ : ℤ →+* K) (a : K) (l : ITerms) :
    sparseEval φ a l = ((toPolyZ l).map φ).eval a := by
  simpa [sparseEval] using sparseEvalAux_eq φ a l 0

/-- Tail-recursive derivative evaluation, omitting precisely the terms of exponent zero. -/
def sparseDerivativeEvalAux {K : Type*} [CommRing K] (φ : ℤ →+* K) (a : K) :
    ITerms → K → K
  | [], s => s
  | (c, e) :: l, s =>
    if e = 0 then sparseDerivativeEvalAux φ a l s
    else sparseDerivativeEvalAux φ a l (s + φ (c * (e : ℤ)) * binaryPow a (e - 1))

/-- Evaluate the formal derivative from the same sparse term list. -/
def sparseDerivativeEval {K : Type*} [CommRing K] (φ : ℤ →+* K) (a : K)
    (l : ITerms) : K := sparseDerivativeEvalAux φ a l 0

/-- The derivative accumulator invariant, including the constant-term branch. -/
theorem sparseDerivativeEvalAux_eq {K : Type*} [CommRing K] (φ : ℤ →+* K) (a : K)
    (l : ITerms) (s : K) :
    sparseDerivativeEvalAux φ a l s = s + ((toPolyZ l).map φ).derivative.eval a := by
  induction l generalizing s with
  | nil => simp [sparseDerivativeEvalAux]
  | cons t l ih =>
    rcases t with ⟨c, e⟩
    by_cases he : e = 0
    · simp [sparseDerivativeEvalAux, he, ih, toPolyZ_cons]
    · simp [sparseDerivativeEvalAux, he, ih, toPolyZ_cons, binaryPow_eq_pow,
        Polynomial.derivative_X_pow, add_assoc, mul_assoc]

/-- The sparse derivative evaluator agrees with the mapped polynomial derivative. -/
theorem sparseDerivativeEval_eq {K : Type*} [CommRing K] (φ : ℤ →+* K) (a : K)
    (l : ITerms) :
    sparseDerivativeEval φ a l = ((toPolyZ l).map φ).derivative.eval a := by
  simpa [sparseDerivativeEval] using sparseDerivativeEvalAux_eq φ a l 0

/-- Evaluation at zero keeps exactly exponent-zero terms. -/
theorem sparseEval_zero {K : Type*} [CommRing K] (φ : ℤ →+* K) (l : ITerms) :
    sparseEval φ 0 l = φ ((toPolyZ l).coeff 0) := by
  rw [sparseEval_eq, ← Polynomial.coeff_zero_eq_eval_zero]
  simp

/-- At zero the derivative keeps exactly exponent-one terms. -/
theorem sparseDerivativeEval_zero {K : Type*} [CommRing K] (φ : ℤ →+* K)
    (l : ITerms) : sparseDerivativeEval φ 0 l = φ ((toPolyZ l).coeff 1) := by
  rw [sparseDerivativeEval_eq, ← Polynomial.coeff_zero_eq_eval_zero]
  simp [Polynomial.coeff_derivative]

/-- The local root-count update evaluated directly from the sparse input. -/
noncomputable def sparseModularRootIncrement (l : ITerms) (p a : ℕ) : ℕ := by
  classical
  exact if sparseEval (Int.castRingHom (ZMod p)) (a : ZMod p) l = 0 then
    1 + if sparseDerivativeEval (Int.castRingHom (ZMod p)) (a : ZMod p) l = 0 then 1 else 0
  else 0

/-- The sparse update is the exact update used in the streaming-counter correctness proof. -/
theorem sparseModularRootIncrement_eq (l : ITerms) (p a : ℕ) :
    sparseModularRootIncrement l p a = modularRootIncrement (toPolyZ l) p a := by
  classical
  unfold sparseModularRootIncrement modularRootIncrement
  dsimp only
  rw [sparseEval_eq, sparseDerivativeEval_eq]

/-- The residue loop implemented directly on the sparse input. -/
noncomputable def sparseModularRootScanAux (l : ITerms) (p : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, c => c
  | k + 1, a, c =>
    sparseModularRootScanAux l p k (a + 1) (c + sparseModularRootIncrement l p a)

/-- Every iteration of the sparse residue loop agrees with the polynomial-level loop. -/
theorem sparseModularRootScanAux_eq (l : ITerms) (p k a c : ℕ) :
    sparseModularRootScanAux l p k a c = modularRootScanAux (toPolyZ l) p k a c := by
  induction k generalizing a c with
  | zero => rfl
  | succ k ih =>
    rw [sparseModularRootScanAux, modularRootScanAux, sparseModularRootIncrement_eq, ih]

/-- The actual sparse residue scan counts all roots and the extra multiple-root witnesses. -/
theorem sparseModularRootScan_count (l : ITerms) (p : ℕ) (hp : p.Prime) :
    sparseModularRootScanAux l p p 0 0 = primeRootWeight (toPolyZ l) p := by
  rw [sparseModularRootScanAux_eq]
  exact modularRootScan_eq_primeRootWeight (toPolyZ l) p hp

end SparseIrred.UpperBounds
