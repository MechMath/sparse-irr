import SparseIrred.UpperBounds.PrimeWitnessCount

/-!
# Streaming prime-root counters

These tail-recursive loops enumerate candidate primes and residues while retaining
only their indices and counters. The proofs identify their values with the finite
prime-root sums and bound every prefix. They are function-level correctness proofs;
they do not assert a Turing-machine implementation or a machine space certificate.
-/

open Polynomial
open scoped BigOperators

namespace SparseIrred.UpperBounds

/-- One residue contributes once for being a root, and once more for a zero derivative. -/
noncomputable def modularRootIncrement (f : ℤ[X]) (p a : ℕ) : ℕ := by
  classical
  let g := f.map (Int.castRingHom (ZMod p))
  exact if g.eval (a : ZMod p) = 0 then
    1 + if g.derivative.eval (a : ZMod p) = 0 then 1 else 0
  else 0

/-- Scan the next `remaining` residues, starting at `a`, using one accumulator. -/
noncomputable def modularRootScanAux (f : ℤ[X]) (p : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, c => c
  | k + 1, a, c => modularRootScanAux f p k (a + 1) (c + modularRootIncrement f p a)

/-- The complete local scan uses exactly the canonical residues `0, ..., p-1`. -/
noncomputable def modularRootScan (f : ℤ[X]) (p : ℕ) : ℕ :=
  modularRootScanAux f p p 0 0

/-- The invariant for a residue scan with an arbitrary initial accumulator. -/
theorem modularRootScanAux_eq_sum (f : ℤ[X]) (p k a c : ℕ) :
    modularRootScanAux f p k a c =
      c + ∑ i ∈ Finset.range k, modularRootIncrement f p (a + i) := by
  induction k generalizing a c with
  | zero => simp [modularRootScanAux]
  | succ k ih =>
    rw [modularRootScanAux, ih, Finset.sum_range_succ']
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Each residue increments the local counter by at most two. -/
theorem modularRootIncrement_le_two (f : ℤ[X]) (p a : ℕ) :
    modularRootIncrement f p a ≤ 2 := by
  classical
  unfold modularRootIncrement
  dsimp only
  split_ifs <;> omega

/-- Even before using the polynomial degree, the local loop has a bounded accumulator. -/
theorem modularRootScanAux_bounds (f : ℤ[X]) (p k a c : ℕ) :
    c ≤ modularRootScanAux f p k a c ∧
      modularRootScanAux f p k a c ≤ c + 2 * k := by
  rw [modularRootScanAux_eq_sum]
  refine ⟨Nat.le_add_right _ _, Nat.add_le_add_left ?_ _⟩
  calc
    _ ≤ ∑ _i ∈ Finset.range k, 2 :=
      Finset.sum_le_sum (fun i _ ↦ modularRootIncrement_le_two f p (a + i))
    _ = _ := by simp [Nat.mul_comm]

/-- At primes the actual local loop counts `ν_f(p)+μ_f(p)`. -/
theorem modularRootScan_eq_primeRootWeight (f : ℤ[X]) (p : ℕ) (hp : p.Prime) :
    modularRootScan f p = primeRootWeight f p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let g := f.map (Int.castRingHom (ZMod p))
  calc
    modularRootScan f p = ∑ a : Fin p, modularRootIncrement f p a.val := by
      simp only [modularRootScan, modularRootScanAux_eq_sum, zero_add]
      exact (Fin.sum_univ_eq_sum_range (modularRootIncrement f p) p).symm
    _ = ∑ a : Fin p, ∑ b : Bool,
        if a.val < p ∧ g.eval (a.val : ZMod p) = 0 ∧
          (b = false ∨ g.derivative.eval (a.val : ZMod p) = 0) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      change (if g.eval (a.val : ZMod p) = 0 then
        1 + if g.derivative.eval (a.val : ZMod p) = 0 then 1 else 0 else 0) = _
      by_cases hr : g.eval (a.val : ZMod p) = 0 <;>
        by_cases hd : g.derivative.eval (a.val : ZMod p) = 0 <;>
        simp [a.isLt, hr, hd]
    _ = rootCount g + multipleRootCount g := modularRootWitness_count p p le_rfl g
    _ = primeRootWeight f p := by simp [primeRootWeight, hp, g]

/-- The prime counter's exact update at one candidate integer. -/
theorem primeCountBelow_succ (p : ℕ) :
    primeCountBelow (p + 1) = primeCountBelow p + if p.Prime then 1 else 0 := by
  calc
    _ = ∑ i ∈ Finset.range (p + 1), if i.Prime then 1 else 0 :=
      (Finset.sum_boole (R := ℕ) Nat.Prime (Finset.range (p + 1))).symm
    _ = (∑ i ∈ Finset.range p, if i.Prime then 1 else 0) +
        if p.Prime then 1 else 0 := Finset.sum_range_succ _ _
    _ = _ := by rw [Finset.sum_boole]; rfl

/-- The root counter's exact update, with zero weight at nonprimes. -/
theorem primeRootSum_succ (f : ℤ[X]) (p : ℕ) :
    primeRootSum f (p + 1) = primeRootSum f p + primeRootWeight f p := by
  classical
  simp only [primeRootSum, Finset.sum_filter, Finset.sum_range_succ]
  by_cases hp : p.Prime <;> simp [primeRootWeight, hp]

/-- One outer iteration performs a complete local scan only when the candidate is prime. -/
noncomputable def primeStreamingStep (f : ℤ[X]) (p : ℕ) (c : ℕ × ℕ) : ℕ × ℕ :=
  if p.Prime then (c.1 + 1, c.2 + modularRootScan f p) else c

/-- Tail-recursive traversal of the candidate primes with exactly two running counters. -/
noncomputable def primeStreamingAux (f : ℤ[X]) : ℕ → ℕ → (ℕ × ℕ) → ℕ × ℕ
  | 0, _, c => c
  | k + 1, p, c => primeStreamingAux f k (p + 1) (primeStreamingStep f p c)

/-- The complete traversal of all candidates strictly below `X`. -/
noncomputable def primeStreaming (f : ℤ[X]) (X : ℕ) : ℕ × ℕ :=
  primeStreamingAux f X 0 (0, 0)

/-- The update preserves the mathematical interpretation of the two running counters. -/
theorem primeStreamingStep_counts (f : ℤ[X]) (p : ℕ) :
    primeStreamingStep f p (primeCountBelow p, primeRootSum f p) =
      (primeCountBelow (p + 1), primeRootSum f (p + 1)) := by
  classical
  rw [primeCountBelow_succ, primeRootSum_succ]
  by_cases hp : p.Prime
  · simp [primeStreamingStep, hp, modularRootScan_eq_primeRootWeight f p hp]
  · simp [primeStreamingStep, hp, primeRootWeight]

/-- The invariant at an arbitrary starting prefix proves correctness of the tail recursion. -/
theorem primeStreamingAux_counts (f : ℤ[X]) (k p : ℕ) :
    primeStreamingAux f k p (primeCountBelow p, primeRootSum f p) =
      (primeCountBelow (p + k), primeRootSum f (p + k)) := by
  induction k generalizing p with
  | zero => simp [primeStreamingAux]
  | succ k ih =>
    rw [primeStreamingAux, primeStreamingStep_counts, ih]
    simp [Nat.add_comm, Nat.add_left_comm]

/-- The streaming loop returns precisely the two counters in the irreducibility criterion. -/
theorem primeStreaming_eq_counts (f : ℤ[X]) (X : ℕ) :
    primeStreaming f X = (primeCountBelow X, primeRootSum f X) := by
  have h := primeStreamingAux_counts f X 0
  simpa [primeStreaming, primeCountBelow, primeRootSum] using h

/-- Every outer-loop prefix has the counter bounds claimed in the space analysis. -/
theorem primeStreaming_prefix_bounds (f : ℤ[X]) (hf : f.IsPrimitive)
    (k X : ℕ) (hkX : k ≤ X) :
    (primeStreaming f k).1 ≤ X ∧ (primeStreaming f k).2 ≤ 2 * f.natDegree * X := by
  rw [primeStreaming_eq_counts]
  have h := prime_counter_bounds f hf k
  exact ⟨h.1.trans hkX, h.2.trans (Nat.mul_le_mul_left _ hkX)⟩

/-- A local prefix can never exceed its complete local scan. -/
theorem modularRootScan_prefix_le (f : ℤ[X]) (p k : ℕ) (hk : k ≤ p) :
    modularRootScanAux f p k 0 0 ≤ modularRootScan f p := by
  simp only [modularRootScan, modularRootScanAux_eq_sum, zero_add]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hk)

/-- During a prime's local scan, the partially updated global root counter is already
bounded by the next complete outer prefix. -/
theorem primeStreaming_inner_prefix_bound (f : ℤ[X]) (hf : f.IsPrimitive)
    (p k X : ℕ) (hp : p.Prime) (hk : k ≤ p) (hpX : p < X) :
    primeRootSum f p + modularRootScanAux f p k 0 0 ≤ 2 * f.natDegree * X := by
  calc
    _ ≤ primeRootSum f p + primeRootWeight f p := by
      rw [← modularRootScan_eq_primeRootWeight f p hp]
      exact Nat.add_le_add_left (modularRootScan_prefix_le f p k hk) _
    _ = primeRootSum f (p + 1) := (primeRootSum_succ f p).symm
    _ ≤ 2 * f.natDegree * (p + 1) := (prime_counter_bounds f hf (p + 1)).2
    _ ≤ _ := Nat.mul_le_mul_left _ hpX

end SparseIrred.UpperBounds
