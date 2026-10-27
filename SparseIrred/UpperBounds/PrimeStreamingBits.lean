import SparseIrred.UpperBounds.PrimeStreaming
import SparseIrred.UpperBounds.PrimeCutoffCounts

/-!
# Binary widths of the actual streaming counters

The counters in every outer and inner loop prefix have linearly many bits in
the sparse input length and the cutoff exponent. This is a certificate about
the values held by the loops, not yet a TM tape-space implementation theorem.
-/

namespace SparseIrred.UpperBounds

theorem root_counter_size_bound (f : Polynomial ℤ) (m A : ℕ)
    (hA : A ≤ 2 * f.natDegree * 2 ^ m) :
    A.size ≤ (encPoly f).length + m + 1 := by
  apply Nat.size_le.mpr
  have hn := degree_lt_pow_encPoly_length f
  calc
    A ≤ 2 * f.natDegree * 2 ^ m := hA
    _ < 2 * 2 ^ (encPoly f).length * 2 ^ m :=
      Nat.mul_lt_mul_of_pos_right
        (Nat.mul_lt_mul_of_pos_left hn (by decide)) (by positivity)
    _ = 2 ^ ((encPoly f).length + m + 1) := by
      rw [pow_add, pow_add]
      norm_num
      ring

/-- All completed outer-loop prefixes fit in the stated binary counter widths. -/
theorem primeStreaming_prefix_bit_bounds (f : Polynomial ℤ) (hf : f.IsPrimitive)
    (k m : ℕ) (hk : k ≤ 2 ^ m) :
    (primeStreaming f k).1.size ≤ m + 1 ∧
      (primeStreaming f k).2.size ≤ (encPoly f).length + m + 1 := by
  have h := primeStreaming_prefix_bounds f hf k (2 ^ m) hk
  exact ⟨(Nat.size_le_size h.1).trans_eq (Nat.size_pow), root_counter_size_bound f m _ h.2⟩

/-- Updating the root counter inside a prime's residue loop also respects the bit bound. -/
theorem primeStreaming_inner_prefix_bit_bound (f : Polynomial ℤ) (hf : f.IsPrimitive)
    (p k m : ℕ) (hp : p.Prime) (hk : k ≤ p) (hpX : p < 2 ^ m) :
    (primeRootSum f p + modularRootScanAux f p k 0 0).size ≤
      (encPoly f).length + m + 1 :=
  root_counter_size_bound f m _ (primeStreaming_inner_prefix_bound f hf p k _ hp hk hpX)

/-- At the manuscript's cutoff both counters have explicit bounds linear in input length. -/
theorem inputCutoff_counter_bit_bounds (C₀ : ℕ) (f : Polynomial ℤ) (hf : f.IsPrimitive)
    (k : ℕ) (hk : k ≤ 2 ^ inputCutoffExponent C₀ f) :
    (primeStreaming f k).1.size ≤
        128 * (38 + Nat.clog 2 C₀) + 768 * (encPoly f).length + 1 ∧
      (primeStreaming f k).2.size ≤
        128 * (38 + Nat.clog 2 C₀) + 769 * (encPoly f).length + 1 := by
  have h := primeStreaming_prefix_bit_bounds f hf k (inputCutoffExponent C₀ f) hk
  have hm := inputCutoffExponent_le C₀ f
  omega

end SparseIrred.UpperBounds
