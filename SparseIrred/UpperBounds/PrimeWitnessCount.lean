import SparseIrred.UpperBounds.IntegerRootCriterion

/-!
# Fixed-length witnesses for prime-root counts

The two predicates of Section 7 use a common finite witness domain. Their actual
numbers of satisfying assignments are the prime counter and the root counter;
combining these identities with the majority gadget gives the desired threshold.
-/

open Polynomial
open scoped BigOperators

namespace SparseIrred.UpperBounds

/-- Canonical residues below `p` embedded in a common larger witness range. -/
theorem sum_fin_restrict_zmod (p X : ℕ) [NeZero p] (hpX : p ≤ X)
    (F : ZMod p → ℕ) :
    (∑ a : Fin X, if a.val < p then F (a.val : ZMod p) else 0) = ∑ a : ZMod p, F a := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun a _ ↦ (a.val : ZMod p)) ?_ ?_ ?_ ?_
  · intro a ha
    exact Finset.mem_univ _
  · intro a ha b hb hab
    apply Fin.ext
    have ha' : a.val < p := (Finset.mem_filter.mp ha).2
    have hb' : b.val < p := (Finset.mem_filter.mp hb).2
    have h := congrArg ZMod.val hab
    simpa [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] using h
  · intro b _
    refine ⟨⟨b.val, lt_of_lt_of_le (ZMod.val_lt b) hpX⟩, ?_, ?_⟩
    · simp [ZMod.val_lt]
    · exact ZMod.natCast_zmod_val b
  · intro a _
    rfl

/-- The witness space consists of two equally wide integers and one bit. -/
abbrev PrimeWitness (X : ℕ) := Fin X × Fin X × Bool

/-- Positive witnesses: exactly one assignment for each prime below `X`. -/
def positivePrimeWitness (X : ℕ) (w : PrimeWitness X) : Prop :=
  w.1.val.Prime ∧ w.2.1.val = 0 ∧ w.2.2 = false

/-- Negative witnesses: one per root, with one extra witness per multiple root. -/
def negativePrimeWitness (f : ℤ[X]) (X : ℕ) (w : PrimeWitness X) : Prop :=
  w.1.val.Prime ∧ w.2.1.val < w.1.val ∧
    (f.map (Int.castRingHom (ZMod w.1.val))).eval (w.2.1.val : ZMod w.1.val) = 0 ∧
    (w.2.2 = false ∨
      (f.map (Int.castRingHom (ZMod w.1.val))).derivative.eval
        (w.2.1.val : ZMod w.1.val) = 0)

instance (X : ℕ) : DecidablePred (positivePrimeWitness X) := by
  intro w
  unfold positivePrimeWitness
  infer_instance

noncomputable instance (f : ℤ[X]) (X : ℕ) :
    DecidablePred (negativePrimeWitness f X) := Classical.decPred _

/-- An indicator-sum presentation of finite witness counts. -/
theorem witnessCount_eq_sum {W : Type*} [Fintype W] (R : W → Prop) [DecidablePred R] :
    witnessCount R = ∑ w, if R w then 1 else 0 := by
  exact (Finset.sum_boole (R := ℕ) R Finset.univ).symm

/-- Counting the positive predicate gives the prime counter, including its strict cutoff. -/
theorem positivePrimeWitness_count (X : ℕ) (hX : 0 < X) :
    witnessCount (positivePrimeWitness X) = primeCountBelow X := by
  classical
  rw [witnessCount_eq_sum]
  simp only [Fintype.sum_prod_type, positivePrimeWitness, Fintype.sum_bool]
  have hzero : ∀ a : Fin X, a.val = 0 ↔ a = ⟨0, hX⟩ := by
    intro a
    exact ⟨fun h ↦ Fin.ext h, fun h ↦ congrArg Fin.val h⟩
  simp_rw [hzero]
  simp only [and_true]
  calc
    _ = ∑ p : Fin X, if p.val.Prime then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : p.val.Prime <;> simp [hp]
    _ = primeCountBelow X := by
      exact (Fin.sum_univ_eq_sum_range (fun p ↦ if p.Prime then 1 else 0) X).trans
        (Finset.sum_boole (R := ℕ) Nat.Prime (Finset.range X))

/-- The extra Boolean choice counts multiple roots once more than simple roots. -/
theorem modularRootWitness_count (p X : ℕ) [Fact p.Prime] (hpX : p ≤ X)
    (g : (ZMod p)[X]) :
    (∑ a : Fin X, ∑ b : Bool,
      if a.val < p ∧ g.eval (a.val : ZMod p) = 0 ∧
        (b = false ∨ g.derivative.eval (a.val : ZMod p) = 0) then 1 else 0) =
      rootCount g + multipleRootCount g := by
  classical
  calc
    _ = ∑ a : Fin X, if a.val < p then
        (if g.eval (a.val : ZMod p) = 0 then 1 else 0) +
        (if g.eval (a.val : ZMod p) = 0 ∧
          g.derivative.eval (a.val : ZMod p) = 0 then 1 else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : a.val < p <;>
        by_cases hr : g.eval (a.val : ZMod p) = 0 <;>
        by_cases hd : g.derivative.eval (a.val : ZMod p) = 0 <;>
        simp [ha, hr, hd]
    _ = ∑ a : ZMod p, ((if g.eval a = 0 then 1 else 0) +
        (if g.eval a = 0 ∧ g.derivative.eval a = 0 then 1 else 0)) :=
      sum_fin_restrict_zmod p X hpX (fun a ↦
        (if g.eval a = 0 then 1 else 0) +
          (if g.eval a = 0 ∧ g.derivative.eval a = 0 then 1 else 0))
    _ = rootCount g + multipleRootCount g := by
      rw [Finset.sum_add_distrib]
      exact congrArg₂ (· + ·)
        (Finset.sum_boole (R := ℕ) (fun a ↦ g.eval a = 0) Finset.univ)
        (Finset.sum_boole (R := ℕ)
          (fun a ↦ g.eval a = 0 ∧ g.derivative.eval a = 0) Finset.univ)

/-- The negative witnesses with a fixed first coordinate count exactly its modular roots. -/
theorem negativePrimeWitness_local_count (f : ℤ[X]) (X : ℕ) (p : Fin X) :
    (∑ a : Fin X, ∑ b : Bool,
      if negativePrimeWitness f X (p, a, b) then 1 else 0) =
      primeRootWeight f p.val := by
  classical
  by_cases hp : p.val.Prime
  · have : Fact p.val.Prime := ⟨hp⟩
    simpa [negativePrimeWitness, hp, primeRootWeight] using
      modularRootWitness_count p.val X p.isLt.le (f.map (Int.castRingHom (ZMod p.val)))
  · simp [negativePrimeWitness, hp, primeRootWeight]

/-- Counting the negative predicate gives the full root counter with multiplicity correction. -/
theorem negativePrimeWitness_count (f : ℤ[X]) (X : ℕ) :
    witnessCount (negativePrimeWitness f X) = primeRootSum f X := by
  classical
  rw [witnessCount_eq_sum]
  simp only [Fintype.sum_prod_type]
  simp_rw [negativePrimeWitness_local_count]
  calc
    _ = ∑ p ∈ Finset.range X, primeRootWeight f p :=
      Fin.sum_univ_eq_sum_range (primeRootWeight f) X
    _ = primeRootSum f X := by
      unfold primeRootSum
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : p.Prime <;> simp [primeRootWeight, hp]

/-- The actual prime-root witnesses implement the strict root-count threshold. -/
theorem primeWitness_majority_iff (f : ℤ[X]) (X : ℕ) (hX : 0 < X) :
    Fintype.card (Fin 8 × PrimeWitness X × Bool) <
      2 * witnessCount (majorityGadget (positivePrimeWitness X) (negativePrimeWitness f X)) ↔
      2 * primeRootSum f X < 3 * primeCountBelow X := by
  rw [majorityGadget_majority_iff, negativePrimeWitness_count,
    positivePrimeWitness_count X hX]

/-- Two `m`-bit integers, the root bit, three mode bits, and the padding bit. -/
theorem primeWitness_choice_count (m : ℕ) :
    Fintype.card (Fin 8 × PrimeWitness (2 ^ m) × Bool) = 2 ^ (2 * m + 5) := by
  simp only [PrimeWitness, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  rw [pow_add, Nat.mul_comm 2 m, pow_mul]
  norm_num
  ring

/-- The strict-majority test on exactly `2 m + 5` binary choices. -/
theorem primeWitness_binary_majority_iff (f : ℤ[X]) (m : ℕ) :
    2 ^ (2 * m + 5) <
      2 * witnessCount
        (majorityGadget (positivePrimeWitness (2 ^ m)) (negativePrimeWitness f (2 ^ m))) ↔
      2 * primeRootSum f (2 ^ m) < 3 * primeCountBelow (2 ^ m) := by
  rw [← primeWitness_choice_count]
  exact primeWitness_majority_iff f (2 ^ m) (by positivity)

/-- The actual witnesses decide primitive nonconstant irreducibility once the analytic
quarter-unit approximation has been supplied. -/
theorem integer_irreducible_iff_primeWitness_majority_of_approximation (f : ℤ[X])
    (hf : f.IsPrimitive) (hdeg : 0 < f.natDegree) (X : ℕ) (hX : 0 < X)
    (hP : 0 < primeCountBelow X)
    (happrox : |(primeRootSum f X : ℝ) / primeCountBelow X -
      factorStatistic (f.map (Int.castRingHom ℚ))| < 1 / 4) :
    Irreducible f ↔ Fintype.card (Fin 8 × PrimeWitness X × Bool) <
      2 * witnessCount (majorityGadget (positivePrimeWitness X) (negativePrimeWitness f X)) :=
  (integer_irreducible_iff_root_threshold_of_approximation f hf hdeg X hP happrox).trans
    (primeWitness_majority_iff f X hX).symm

end SparseIrred.UpperBounds
