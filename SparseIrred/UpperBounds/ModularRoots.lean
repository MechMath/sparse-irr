import SparseDivComplexity.Appendix.Content

/-!
# Modular root counts, including multiple roots

These are the local algebraic ingredients of Section 3.2. In particular, multiplicities
divisible by the characteristic do not require excluding additional primes.
-/

open Polynomial

namespace SparseIrred.UpperBounds

/-- Distinct roots in the base finite field. -/
def rootCount {K : Type*} [Field K] [Fintype K] [DecidableEq K] (f : K[X]) : ℕ :=
  (Finset.univ.filter fun a ↦ f.eval a = 0).card

/-- Roots at which the formal derivative also vanishes. -/
noncomputable def multipleRootCount {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (f : K[X]) : ℕ :=
  (Finset.univ.filter fun a ↦ f.eval a = 0 ∧ f.derivative.eval a = 0).card

theorem multipleRootCount_le_rootCount {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (f : K[X]) : multipleRootCount f ≤ rootCount f := by
  apply Finset.card_le_card
  intro a ha
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
  exact ha.1

theorem rootCount_le_natDegree {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (f : K[X]) (hf : f ≠ 0) : rootCount f ≤ f.natDegree := by
  apply le_trans (Finset.card_le_card (t := f.roots.toFinset) ?_)
    ((Multiset.toFinset_card_le _).trans f.card_roots')
  intro a ha
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
  exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hf).mpr ha)

/-- Equation (28), including primes where the degree drops. -/
theorem primitive_modular_root_bounds (f : ℤ[X]) (hf : f.IsPrimitive)
    (p : ℕ) (hp : p.Prime) :
    let g := f.map (Int.castRingHom (ZMod p))
    letI := Fact.mk hp
    multipleRootCount g ≤ rootCount g ∧ rootCount g ≤ f.natDegree := by
  let _ := Fact.mk hp
  dsimp
  refine ⟨multipleRootCount_le_rootCount _, ?_⟩
  exact (rootCount_le_natDegree _
    (SparseDiv.Appendix.map_ne_zero_of_isPrimitive hf hp)).trans Polynomial.natDegree_map_le

/-- At a simple root of `h` disjoint from `g`, the derivative of `h^m*g` is nonzero
exactly when `m = 1`. No restriction on the characteristic or on `m` is used. -/
theorem derivative_at_factor_root {K : Type*} [Field K] (h g : K[X]) (a : K)
    (ha : h.eval a = 0) (hd : h.derivative.eval a ≠ 0) (hg : g.eval a ≠ 0)
    (m : ℕ) (hm : 0 < m) :
    ((h ^ m * g).derivative.eval a ≠ 0 ↔ m = 1) := by
  rcases m with _ | m
  · omega
  rcases m with _ | m
  · simp [Polynomial.derivative_mul, ha, hd, hg]
  · simp [Polynomial.derivative_mul, Polynomial.derivative_pow, ha]

end SparseIrred.UpperBounds
