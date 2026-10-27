import Mathlib.Tactic

/-!
# The root-count threshold and its majority gadget

This file verifies the numerical implication in Corollary 15 and the exact counting
identity in Section 3.7. It does not assume or assert that the analytic estimate, the
polynomial-time witness predicates, or a particular probabilistic machine exist.
-/

namespace SparseIrred.UpperBounds

open scoped BigOperators

/-- A quarter-unit approximation distinguishes `ρ = 1` from every integer `ρ ≥ 2`. -/
theorem root_threshold_iff (A P ρ : ℕ) (hP : 0 < P) (hρ : 1 ≤ ρ)
    (happrox : |(A : ℝ) / P - ρ| < 1 / 4) :
    2 * A < 3 * P ↔ ρ = 1 := by
  have hp : (0 : ℝ) < P := by exact_mod_cast hP
  have hlo := (abs_lt.mp happrox).1
  have hhi := (abs_lt.mp happrox).2
  constructor
  · intro h
    have h' : (2 : ℝ) * A < 3 * P := by exact_mod_cast h
    have hratio : (A : ℝ) / P < 3 / 2 := (div_lt_iff₀ hp).mpr (by linarith)
    have : (ρ : ℝ) < 2 := by linarith
    have : ρ < 2 := by exact_mod_cast this
    omega
  · rintro rfl
    have : (A : ℝ) / P < 5 / 4 := by linarith
    have : (A : ℝ) < (5 / 4) * P := (div_lt_iff₀ hp).mp this
    have : (2 : ℝ) * A < 3 * P := by linarith
    exact_mod_cast this

/-- Number of witnesses satisfying a predicate on a finite set. -/
def witnessCount {W : Type*} [Fintype W] (R : W → Prop) [DecidablePred R] : ℕ :=
  (Finset.univ.filter R).card

/-- The signed number of accepting choices of a finite predicate. -/
def acceptanceBalance {W : Type*} [Fintype W] (R : W → Prop) [DecidablePred R] : ℤ :=
  ∑ w, if R w then 1 else -1

theorem acceptanceBalance_eq {W : Type*} [Fintype W] (R : W → Prop) [DecidablePred R] :
    acceptanceBalance R = 2 * (witnessCount R : ℤ) - Fintype.card W := by
  classical
  calc
    acceptanceBalance R = ∑ w, (2 * (if R w then 1 else 0) - 1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro w _
      split_ifs <;> norm_num
    _ = 2 * (∑ w, if R w then (1 : ℤ) else 0) - ∑ _w : W, (1 : ℤ) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = _ := by simp [witnessCount, Finset.sum_boole]

/-- The eight modes and one padding bit in Section 3.7. -/
def majorityGadget {W : Type*} (positive negative : W → Prop)
    [DecidablePred positive] [DecidablePred negative] (x : Fin 8 × W × Bool) : Prop :=
  if x.1.val < 3 then positive x.2.1 ∨ x.2.2 = true
  else if x.1.val < 5 then ¬negative x.2.1 ∧ x.2.2 = true
  else x.2.2 = true

instance {W : Type*} (positive negative : W → Prop)
    [DecidablePred positive] [DecidablePred negative] :
    DecidablePred (majorityGadget positive negative) := fun _ ↦ by
  unfold majorityGadget
  infer_instance

/-- Each positive witness contributes `6`, each negative witness contributes `-4`. -/
theorem majorityGadget_local {W : Type*} (positive negative : W → Prop)
    [DecidablePred positive] [DecidablePred negative] (w : W) :
    (∑ mode : Fin 8, ∑ bit : Bool,
      (if majorityGadget positive negative (mode, w, bit) then (1 : ℤ) else -1)) =
      6 * (if positive w then 1 else 0) - 4 * (if negative w then 1 else 0) := by
  by_cases hp : positive w <;> by_cases hn : negative w <;>
    norm_num [majorityGadget, Fin.sum_univ_succ, Fintype.sum_bool, hp, hn]

/-- The exact accepting-minus-rejecting identity asserted in Section 3.7. -/
theorem majorityGadget_balance {W : Type*} [Fintype W] (positive negative : W → Prop)
    [DecidablePred positive] [DecidablePred negative] :
    acceptanceBalance (majorityGadget positive negative) =
      2 * (3 * (witnessCount positive : ℤ) - 2 * witnessCount negative) := by
  classical
  unfold acceptanceBalance
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp_rw [majorityGadget_local]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [witnessCount, ← Finset.sum_boole]
  ring

/-- A strict majority implements `2 A < 3 P`; ties are rejected. -/
theorem majorityGadget_majority_iff {W : Type*} [Fintype W] (positive negative : W → Prop)
    [DecidablePred positive] [DecidablePred negative] :
    Fintype.card (Fin 8 × W × Bool) < 2 * witnessCount (majorityGadget positive negative) ↔
      2 * witnessCount negative < 3 * witnessCount positive := by
  have hb := majorityGadget_balance positive negative
  rw [acceptanceBalance_eq] at hb
  omega

end SparseIrred.UpperBounds
