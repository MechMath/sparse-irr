import SparseIrred.UpperBounds.SparseModularEval
import SparseIrred.UpperBounds.PrimeWitnessCount

/-!
# Executable sparse witnesses and the eight-mode decision procedure

The functions in this file execute on raw integer term lists. They use repeated
squaring in `ZMod p`, so neither dense polynomial construction nor normalization of
the input is required. Their correctness covers duplicate exponents, cancellation,
constant terms, and evaluation at zero.

`executablePrimeMajority` implements one branch after its random choices have been
supplied. Its exact finite-branch counts agree with the Section 3.7 majority gadget.
This file does not assert a Turing-machine implementation or polynomial running time.
In particular, the default decidable primality test is not an implementation of AKS.
-/

open Polynomial
open SparseDiv.Appendix

namespace SparseIrred.UpperBounds

/-- Evaluate the sparse input modulo `p`, using repeated squaring for exponents. -/
def executableModularEval (l : ITerms) (p a : ℕ) : ZMod p :=
  sparseEval (Int.castRingHom (ZMod p)) (a : ZMod p) l

/-- Evaluate the derivative modulo `p` directly from the original sparse input. -/
def executableModularDerivativeEval (l : ITerms) (p a : ℕ) : ZMod p :=
  sparseDerivativeEval (Int.castRingHom (ZMod p)) (a : ZMod p) l

/-- The executable evaluator agrees with polynomial reduction and evaluation. -/
theorem executableModularEval_eq (l : ITerms) (p a : ℕ) :
    executableModularEval l p a =
      ((toPolyZ l).map (Int.castRingHom (ZMod p))).eval (a : ZMod p) :=
  sparseEval_eq _ _ _

/-- The executable derivative evaluator agrees with the derivative after reduction. -/
theorem executableModularDerivativeEval_eq (l : ITerms) (p a : ℕ) :
    executableModularDerivativeEval l p a =
      ((toPolyZ l).map (Int.castRingHom (ZMod p))).derivative.eval (a : ZMod p) :=
  sparseDerivativeEval_eq _ _ _

/-- The executable positive witness test: a prime and its unique zero/false tag. -/
def executablePositivePrimeWitness (p a : ℕ) (b : Bool) : Bool :=
  decide p.Prime && decide (a = 0) && !b

/-- The executable negative witness test, counting a multiple root for both tags. -/
def executableNegativePrimeWitness (l : ITerms) (p a : ℕ) (b : Bool) : Bool :=
  decide p.Prime && decide (a < p) && decide (executableModularEval l p a = 0) &&
    (!b || decide (executableModularDerivativeEval l p a = 0))

/-- The positive test computes exactly the mathematical positive witness predicate. -/
theorem executablePositivePrimeWitness_eq_true (X : ℕ) (w : PrimeWitness X) :
    executablePositivePrimeWitness w.1.val w.2.1.val w.2.2 = true ↔
      positivePrimeWitness X w := by
  simp [executablePositivePrimeWitness, positivePrimeWitness, and_assoc]

/-- The negative test computes exactly the mathematical negative witness predicate. -/
theorem executableNegativePrimeWitness_eq_true (l : ITerms) (X : ℕ)
    (w : PrimeWitness X) :
    executableNegativePrimeWitness l w.1.val w.2.1.val w.2.2 = true ↔
      negativePrimeWitness (toPolyZ l) X w := by
  simp [executableNegativePrimeWitness, negativePrimeWitness,
    executableModularEval_eq, executableModularDerivativeEval_eq, and_assoc]

/-- A false output is precisely failure of the mathematical negative witness test. -/
theorem executableNegativePrimeWitness_eq_false (l : ITerms) (X : ℕ)
    (w : PrimeWitness X) :
    executableNegativePrimeWitness l w.1.val w.2.1.val w.2.2 = false ↔
      ¬negativePrimeWitness (toPolyZ l) X w := by
  rw [← Bool.eq_false_eq_not_eq_true, executableNegativePrimeWitness_eq_true]

/-- One executable branch, with the eight-mode choice and padding coin supplied. -/
def executablePrimeMajority (l : ITerms) (mode p a : ℕ) (b coin : Bool) : Bool :=
  if mode < 3 then executablePositivePrimeWitness p a b || coin
  else if mode < 5 then !executableNegativePrimeWitness l p a b && coin
  else coin

/-- The executable branch agrees with the already verified majority gadget. -/
theorem executablePrimeMajority_eq_true (l : ITerms) (X : ℕ)
    (x : Fin 8 × PrimeWitness X × Bool) :
    executablePrimeMajority l x.1.val x.2.1.1.val x.2.1.2.1.val x.2.1.2.2 x.2.2 = true ↔
      majorityGadget (positivePrimeWitness X) (negativePrimeWitness (toPolyZ l) X) x := by
  unfold executablePrimeMajority majorityGadget
  split_ifs <;>
    simp [executablePositivePrimeWitness_eq_true, executableNegativePrimeWitness_eq_false]

/-- The complete finite choice predicate, now with a computable decider. -/
def executablePrimeBranch (l : ITerms) (X : ℕ)
    (x : Fin 8 × PrimeWitness X × Bool) : Prop :=
  executablePrimeMajority l x.1.val x.2.1.1.val x.2.1.2.1.val x.2.1.2.2 x.2.2 = true

instance (l : ITerms) (X : ℕ) : DecidablePred (executablePrimeBranch l X) :=
  fun _ ↦ inferInstanceAs (Decidable (_ = true))

/-- Function equality transfers finite counts without assuming normalization of the input. -/
theorem executablePrimeBranch_eq (l : ITerms) (X : ℕ) :
    executablePrimeBranch l X =
      majorityGadget (positivePrimeWitness X) (negativePrimeWitness (toPolyZ l) X) := by
  funext x
  exact propext (executablePrimeMajority_eq_true l X x)

/-- The executable branch has exactly the paper's accepting-minus-rejecting balance. -/
theorem executablePrimeBranch_balance (l : ITerms) (X : ℕ) (hX : 0 < X) :
    acceptanceBalance (executablePrimeBranch l X) =
      2 * (3 * (primeCountBelow X : ℤ) - 2 * primeRootSum (toPolyZ l) X) := by
  classical
  simp only [executablePrimeBranch_eq]
  rw [majorityGadget_balance, positivePrimeWitness_count X hX,
    negativePrimeWitness_count]

/-- The finite executable test implements the exact strict root-count threshold. -/
theorem executablePrimeBranch_majority_iff (l : ITerms) (X : ℕ) (hX : 0 < X) :
    Fintype.card (Fin 8 × PrimeWitness X × Bool) <
      2 * witnessCount (executablePrimeBranch l X) ↔
      2 * primeRootSum (toPolyZ l) X < 3 * primeCountBelow X := by
  classical
  simp only [executablePrimeBranch_eq]
  exact primeWitness_majority_iff (toPolyZ l) X hX

/-- For `m`-bit witnesses the executable predicate uses exactly `2*m+5` choice bits. -/
theorem executablePrimeBranch_binary_majority_iff (l : ITerms) (m : ℕ) :
    2 ^ (2 * m + 5) < 2 * witnessCount (executablePrimeBranch l (2 ^ m)) ↔
      2 * primeRootSum (toPolyZ l) (2 ^ m) < 3 * primeCountBelow (2 ^ m) := by
  classical
  simp only [executablePrimeBranch_eq]
  exact primeWitness_binary_majority_iff (toPolyZ l) m

end SparseIrred.UpperBounds
